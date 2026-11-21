-- Prove2me | solution 1 for HigherOrderId.Certify.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:26:28.366023+00:00
-- url     : https://prove2.me/submissions/94b002f6-1769-478d-a998-6907b5e27e43

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion

section
open Matrix
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.B2
open HigherOrderId.Certify

lemma split_id (d m k : ℕ) (hmk : m + k = d)
    (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) :
    U * Uᵀ + V * Vᵀ = 1 := by
  let e : Fin m ⊕ Fin k ≃ Fin d := finSumFinEquiv.trans (finCongr hmk)
  let W : Matrix (Fin d) (Fin d) ℝ := (Matrix.fromCols U V).submatrix id e.symm
  have hVU : Vᵀ * U = 0 := by
    have := congrArg Matrix.transpose hUV
    simpa [Matrix.transpose_mul] using this
  have hWW : Wᵀ * W = 1 := by
    ext c c'
    have key : ∀ s s' : Fin m ⊕ Fin k, ((Matrix.fromCols U V)ᵀ * Matrix.fromCols U V) s s' =
        (1 : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) ℝ) s s' := by
      intro s s'
      have h1 : (Matrix.fromCols U V)ᵀ * Matrix.fromCols U V =
          Matrix.fromBlocks (Uᵀ * U) (Uᵀ * V) (Vᵀ * U) (Vᵀ * V) := by
        ext s s'
        rcases s with s | s <;> rcases s' with s' | s' <;>
          simp [Matrix.mul_apply, Matrix.fromBlocks, Matrix.fromCols, Matrix.transpose_apply]
      rw [h1, hU, hV, hUV, hVU, Matrix.fromBlocks_one]
    have := key (e.symm c) (e.symm c')
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
    simp only [W, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id]
    rw [this]
    simp [Matrix.one_apply]
  have hWW' : W * Wᵀ = 1 := mul_eq_one_comm.mp hWW
  ext a b
  have := congrFun (congrFun hWW' a) b
  simp only [W, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id] at this
  have h2 : ∑ c : Fin d, (Matrix.fromCols U V) a (e.symm c) * (Matrix.fromCols U V) b (e.symm c) =
      ∑ s : Fin m ⊕ Fin k, (Matrix.fromCols U V) a s * (Matrix.fromCols U V) b s :=
    Equiv.sum_comp e.symm (fun s => (Matrix.fromCols U V) a s * (Matrix.fromCols U V) b s)
  rw [h2, Fintype.sum_sum_type] at this
  simp [Matrix.fromCols] at this
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [this]

lemma part1 (d m k : ℕ) (hmk : m + k = d)
    (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) :
    (∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Q * V = 0 → Q = 0) ↔ FullColRank U := by
  have hs := split_id d m k hmk U V hU hV hUV
  have hVU : Vᵀ * U = 0 := by
    have := congrArg Matrix.transpose hUV
    simpa [Matrix.transpose_mul] using this
  constructor
  · intro H B hB hD
    have hsym : (U * B * Uᵀ).IsSymm := by
      unfold Matrix.IsSymm
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hB.eq,
        Matrix.mul_assoc]
    have hdiag : ∀ i, (U * B * Uᵀ) i i = 0 := fun i => congrFun hD i
    have hQV : (U * B * Uᵀ) * V = 0 := by
      rw [Matrix.mul_assoc, hUV, Matrix.mul_zero]
    have := H _ ⟨hsym, hdiag⟩ hQV
    calc B = (Uᵀ * U) * B * (Uᵀ * U) := by rw [hU]; simp
      _ = Uᵀ * (U * B * Uᵀ) * U := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [this]; simp
  · intro F Q hQ hQV
    have hQ1 : Q = Q * (U * Uᵀ) := by
      have : Q * (U * Uᵀ + V * Vᵀ) = Q := by rw [hs, Matrix.mul_one]
      rw [Matrix.mul_add, ← Matrix.mul_assoc Q V, hQV, Matrix.zero_mul, add_zero] at this
      exact this.symm
    have hQ2 : Q = (U * Uᵀ) * Q := by
      have h := congrArg Matrix.transpose hQ1
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        hQ.1.eq] at h
      rw [Matrix.mul_assoc] at h
      simpa [Matrix.mul_assoc] using h
    have hQ3 : Q = U * (Uᵀ * Q * U) * Uᵀ := by
      calc Q = (U * Uᵀ) * (Q * (U * Uᵀ)) := by rw [← hQ1]; exact hQ2
        _ = _ := by simp only [Matrix.mul_assoc]
    have hB : (Uᵀ * Q * U).IsSymm := by
      unfold Matrix.IsSymm
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQ.1.eq,
        Matrix.mul_assoc]
    have hD : DU U (Uᵀ * Q * U) = 0 := by
      funext a
      have := hQ.2 a
      rw [hQ3] at this
      simpa [DU] using this
    have := F _ hB hD
    rw [hQ3, this]; simp

lemma tri_sum (n : ℕ) : ∑ i ∈ Finset.range n, (n - i) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : ∑ i ∈ Finset.range n, (n + 1 - i) = ∑ i ∈ Finset.range n, (n - i) + n := by
      rw [show ∑ i ∈ Finset.range n, (n + 1 - i) = ∑ i ∈ Finset.range n, ((n - i) + 1) from
        Finset.sum_congr rfl (fun i hi => by have := Finset.mem_range.mp hi; omega)]
      simp [Finset.sum_add_distrib]
    rw [this, ih, Nat.choose_succ_succ (n + 1) 1]
    simp; ring

lemma card_symIdx (m : ℕ) : Fintype.card (SymIdx m) = (m + 1).choose 2 := by
  rw [← tri_sum, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range (fun i => m - i) m]
  apply Finset.sum_congr rfl
  intro i _
  show (∑ y : Fin m, if i ≤ y then 1 else 0) = m - i
  rw [← Finset.card_filter]
  have : (Finset.univ.filter fun j : Fin m => i ≤ j) = Finset.Ici i := by ext j; simp
  rw [this, Fin.card_Ici]

/-- symmetric matrix with prescribed upper triangle -/
noncomputable def Bc {m : ℕ} (c : SymIdx m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if h : i ≤ j then c ⟨(i, j), h⟩ else c ⟨(j, i), le_of_not_ge h⟩

lemma Bc_symm {m : ℕ} (c : SymIdx m → ℝ) : (Bc c).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, Bc]
  by_cases h1 : i ≤ j <;> by_cases h2 : j ≤ i
  · have : i = j := le_antisymm h1 h2
    subst this; simp
  · simp [h1, h2]
  · simp [h1, h2]
  · exact absurd (le_total i j) (by tauto)

lemma Bc_add {m : ℕ} (c c' : SymIdx m → ℝ) : Bc (c + c') = Bc c + Bc c' := by
  ext i j; simp only [Bc, Matrix.add_apply]; split_ifs <;> simp

lemma Bc_smul {m : ℕ} (r : ℝ) (c : SymIdx m → ℝ) : Bc (r • c) = r • Bc c := by
  ext i j; simp only [Bc, Matrix.smul_apply]; split_ifs <;> simp

lemma Bc_ne {m : ℕ} (c : SymIdx m → ℝ) (hc : c ≠ 0) : Bc c ≠ 0 := by
  intro h
  apply hc; funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa [Bc, p.2] using this

lemma DU_add {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (A B : Matrix (Fin m) (Fin m) ℝ) :
    DU U (A + B) = DU U A + DU U B := by
  funext a; simp [DU, Matrix.mul_add, Matrix.add_mul]

lemma DU_smul {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (r : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    DU U (r • A) = r • DU U A := by
  funext a; simp [DU]

lemma part2 (d m k : ℕ) (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hUV : Uᵀ * V = 0) (hlt : d < (m + 1).choose 2) :
    ∃ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q ∧ Q ≠ 0 ∧ Q * V = 0 := by
  let T : (SymIdx m → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    { toFun := fun c => DU U (Bc c)
      map_add' := fun c c' => by rw [Bc_add, DU_add]
      map_smul' := fun r c => by rw [Bc_smul, DU_smul]; rfl }
  have hker : LinearMap.ker T ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      card_symIdx]
    exact hlt
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hT : DU U (Bc c) = 0 := hc
  have hB := Bc_symm c
  refine ⟨U * Bc c * Uᵀ, ⟨?_, fun i => congrFun hT i⟩, ?_, ?_⟩
  · unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hB.eq,
      Matrix.mul_assoc]
  · intro h0
    apply Bc_ne c hc0
    calc Bc c = (Uᵀ * U) * Bc c * (Uᵀ * U) := by rw [hU]; simp
      _ = Uᵀ * (U * Bc c * Uᵀ) * U := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0]; simp
  · rw [Matrix.mul_assoc, hUV, Matrix.mul_zero]


lemma Gw_apply {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (r : FrameRows m) (c : Fin m) :
    Gw ι w (ι r) c = frameRow w r c := by
  unfold Gw
  rw [Finset.sum_eq_single r]
  · simp
  · intro r' _ hr'; simp [ι.injective.ne hr']
  · simp

lemma Sw_det {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w) :
    (Sw ι w).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hSx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hx
  have h1 : (Gw ι w *ᵥ x) ⬝ᵥ (Gw ι w *ᵥ x) = 0 := by
    have : x ⬝ᵥ ((Sw ι w) *ᵥ x) = 0 := by rw [hSx]; simp
    rw [Sw, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
    exact this
  have h2 := dotProduct_self_eq_zero.mp h1
  funext i
  have := congrFun h2 (ι (Sum.inl i))
  simp only [Matrix.mulVec, dotProduct, Gw_apply, frameRow, Pi.zero_apply] at this
  simp [mul_comm] at this
  rcases this with h | h
  · exact h
  · exact absurd h (Real.sqrt_ne_zero'.mpr hw)

lemma sqrtS_props {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w) :
    ∃ Ri : Matrix (Fin m) (Fin m) ℝ, Riᵀ = Ri ∧ (CFC.sqrt (Sw ι w)) * Ri = 1 ∧
      Ri * (CFC.sqrt (Sw ι w)) = 1 ∧ (CFC.sqrt (Sw ι w))ᵀ = CFC.sqrt (Sw ι w) ∧
      Uw ι w = Gw ι w * Ri := by
  set R := CFC.sqrt (Sw ι w) with hR
  have hS : (0 : Matrix (Fin m) (Fin m) ℝ) ≤ Sw ι w := by
    have := Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self (Gw ι w))
    simpa [Sw, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hRR : R * R = Sw ι w := CFC.sqrt_mul_sqrt_self _ hS
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg _
  have hRsym : Rᵀ = R := by
    have := (Matrix.nonneg_iff_posSemidef.mp hR0).isHermitian
    have h2 : Rᴴ = R := this
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have hdet : R.det ≠ 0 := by
    have := Sw_det ι w hw
    rw [← hRR, Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨R⁻¹, ?_, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, hRsym, rfl⟩
  rw [Matrix.transpose_nonsing_inv, hRsym]

lemma fullColRank_Uw {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w) :
    FullColRank (Uw ι w) := by
  obtain ⟨Ri, hRit, hRRi, hRiR, hRt, hU⟩ := sqrtS_props ι w hw
  set R := CFC.sqrt (Sw ι w)
  intro B hB hD
  set B' := Ri * B * Ri with hB'
  have hB's : B'ᵀ = B' := by
    rw [hB', Matrix.transpose_mul, Matrix.transpose_mul, hRit, hB.eq, Matrix.mul_assoc]
  have hdiag : ∀ a, (Gw ι w * B' * (Gw ι w)ᵀ) a a = 0 := by
    intro a
    have := congrFun hD a
    simp only [DU, Pi.zero_apply] at this
    rw [hU, Matrix.transpose_mul, hRit] at this
    rw [← this, hB']
    try simp only [Matrix.mul_assoc]
  have hq : ∀ r, (Gw ι w * B' * (Gw ι w)ᵀ) (ι r) (ι r) =
      ∑ c, ∑ c', frameRow w r c * B' c c' * frameRow w r c' := by
    intro r
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Gw_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hii : ∀ i, B' i i = 0 := by
    intro i
    have := (hq (Sum.inl i)).symm.trans (hdiag _)
    simp [frameRow] at this
    have hsw : √w ≠ 0 := Real.sqrt_ne_zero'.mpr hw
    tauto
  have hij : ∀ i j (h : i < j), B' i j = 0 := by
    intro i j h
    have := (hq (Sum.inr ⟨(i, j), h⟩)).symm.trans (hdiag _)
    have hv : frameRow w (Sum.inr ⟨(i, j), h⟩) = Pi.single i 1 + Pi.single j 1 := by
      funext c
      simp only [frameRow, Pi.add_apply, Pi.single_apply]
      have hne : i ≠ j := ne_of_lt h
      by_cases h1 : c = i <;> by_cases h2 : c = j <;>
        first | simp [h1, h2, hne, hne.symm] | (exfalso; exact hne (h1.symm.trans h2))
    have hform : ∀ v : Fin m → ℝ, ∑ c, ∑ c', v c * B' c c' * v c' = v ⬝ᵥ (B' *ᵥ v) := by
      intro v
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [hform, hv] at this
    simp [add_dotProduct, dotProduct_add, Matrix.mulVec_add, Matrix.mulVec_single, hii] at this
    have hsym : B' j i = B' i j := by
      have := congrFun (congrFun hB's i) j
      simpa using this
    rw [hsym] at this
    linarith
  have hB'0 : B' = 0 := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · simpa using hij i j h
    · subst h; simpa using hii i
    · have := hij j i h
      have hsym := congrFun (congrFun hB's i) j
      simp at hsym
      simp [← hsym, this]
  calc B = R * B' * R := by
        rw [hB']
        calc B = (R * Ri) * B * (Ri * R) := by rw [hRRi, hRiR]; simp
          _ = _ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hB'0]; simp

end HigherOrderId.Certify.Dev.B2

namespace HigherOrderId.Certify

theorem chk_lemma_B_2 (d m k : ℕ) (hd : 10 ≤ d) (hmk : m + k = d)
    (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) :
    ((∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Q * V = 0 → Q = 0) ↔
        FullColRank U) ∧
    (d < (m + 1).choose 2 →
        ∃ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q ∧ Q ≠ 0 ∧ Q * V = 0) ∧
    (m = 0 → ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Q * V = 0 → Q = 0) ∧
    (∀ (ι : FrameRows m ↪ Fin d) (w : ℝ), 1 ≤ m → 1 ≤ w → w ≤ (m : ℝ) → U = Uw ι w →
        ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Q * V = 0 → Q = 0) := by
  have h1 := Dev.B2.part1 d m k hmk U V hU hV hUV
  refine ⟨h1, fun hlt => Dev.B2.part2 d m k U V hU hUV hlt, ?_, ?_⟩
  · intro hm
    exact h1.mpr (fun B _ _ => by ext i j; exact absurd i.2 (by omega))
  · intro ι w _ hw _ hUw
    exact h1.mpr (by rw [hUw]; exact Dev.B2.fullColRank_Uw ι w (by linarith))

end HigherOrderId.Certify
end

theorem solution : type_of% @HigherOrderId.Certify.chk_lemma_B_2 := @HigherOrderId.Certify.chk_lemma_B_2
