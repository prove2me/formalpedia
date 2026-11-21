-- Prove2me | solution 1 for HigherOrderId.Certify.lemma_B_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T20:41:03.631486+00:00
-- url     : https://prove2.me/submissions/b3e795b4-0d10-49f3-a798-2ee38e3a6e9e

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion
import Definitions.Def_HigherOrderId_Certify_TallCompletion
import Theorems.Thm_HigherOrderId_Certify_eq_82_83

section
open Matrix

namespace HigherOrderId.Certify.Dev.Nuc

variable {d : ℕ} {T : Type*} [Fintype T] [DecidableEq T]

end HigherOrderId.Certify.Dev.Nuc
end

section
open Matrix
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.B2
open HigherOrderId.Certify

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

lemma Bc_ne {m : ℕ} (c : SymIdx m → ℝ) (hc : c ≠ 0) : Bc c ≠ 0 := by
  intro h
  apply hc; funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa [Bc, p.2] using this


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

end HigherOrderId.Certify
end

section
open Matrix

namespace HigherOrderId.Certify.Dev.E82
open HigherOrderId.Certify
open HigherOrderId.Certify.Dev.B2

lemma sum_sym {m : ℕ} (f : Fin m → Fin m → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ p : SymIdx m, (if p.1.1 = p.1.2 then 1 else 2) * f p.1.1 p.1.2 = ∑ i, ∑ j, f i j := by
  have h1 : ∑ p : SymIdx m, (if p.1.1 = p.1.2 then (1:ℝ) else 2) * f p.1.1 p.1.2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≤ p.2),
        (if p.1 = p.2 then (1:ℝ) else 2) * f p.1 p.2 :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≤ p.2))
      (by intro x; simp) (fun p => (if p.1 = p.2 then (1:ℝ) else 2) * f p.1 p.2)).symm
  rw [h1, Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ i, ∑ j, f i j = ∑ i, ∑ j, ((if i ≤ j then f i j else 0) + (if j < i then f i j else 0)) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    by_cases h : i ≤ j
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have h3 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [hf]
  rw [h2]
  simp only [Finset.sum_add_distrib]
  rw [h3, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.le, ne_of_lt h]; ring
  · subst h; simp
  · simp [not_le.mpr h, not_lt.mpr h.le]

lemma quad_single {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : Fin d) (i j : Fin m) :
    (U * Matrix.single i j (1:ℝ) * Uᵀ) a a = U a i * U a j := by
  have : (U * Matrix.single i j (1:ℝ) * Uᵀ) a a =
      ∑ k, ∑ l, U a k * (Matrix.single i j (1:ℝ)) k l * U a l := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [this]
  simp [Matrix.single_apply, ite_and, mul_comm]

lemma DUmat_apply {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : Fin d) (p : SymIdx m) :
    DUmat U a p = (if p.1.1 = p.1.2 then U a p.1.1 * U a p.1.1
      else Real.sqrt 2 * (U a p.1.1 * U a p.1.2)) := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only [DUmat, DU, symBasis]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    exact quad_single U a i i
  · simp only [h, if_false]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_add, Matrix.add_mul,
      Matrix.add_apply, quad_single, quad_single]
    have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
    have h3 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    simp only [smul_eq_mul]
    field_simp
    have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [h4]; ring


lemma quad_gen {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (a : Fin d) :
    (U * B * Uᵀ) a a = ∑ k, ∑ l, U a k * B k l * U a l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma DU_Bc {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (c : SymIdx m → ℝ) :
    DU U (Bc (fun p => if p.1.1 = p.1.2 then c p else c p / Real.sqrt 2)) = DUmat U *ᵥ c := by
  funext a
  simp only [DU]
  rw [quad_gen]
  have hs := Bc_symm (fun p : SymIdx m => if p.1.1 = p.1.2 then c p else c p / Real.sqrt 2)
  rw [← sum_sym (fun k l => U a k * Bc (fun p : SymIdx m => if p.1.1 = p.1.2 then c p else
      c p / Real.sqrt 2) k l * U a l) (fun i j => by
        have := congrFun (congrFun hs i) j
        simp only [Matrix.transpose_apply] at this
        rw [← this]; ring)]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl; intro p _
  rw [DUmat_apply]
  have hp := p.2
  have : Bc (fun q : SymIdx m => if q.1.1 = q.1.2 then c q else c q / Real.sqrt 2) p.1.1 p.1.2
      = if p.1.1 = p.1.2 then c p else c p / Real.sqrt 2 := by
    simp [Bc, hp]
  rw [this]
  by_cases h : p.1.1 = p.1.2
  · simp only [h, if_true]; ring
  · simp only [h, if_false]
    have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
    have h4 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    have h5 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [h5]; ring

lemma singVals_pos {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hF : FullColRank U) (j : SymIdx m) :
    0 < singVals U j := by
  have hinj : Function.Injective (DUmat U).mulVec := by
    have key : ∀ c : SymIdx m → ℝ, DUmat U *ᵥ c = 0 → c = 0 := by
      intro c hc'
      set c' : SymIdx m → ℝ := fun p => if p.1.1 = p.1.2 then c p else c p / Real.sqrt 2 with hc'def
      have hD : DU U (Bc c') = 0 := by rw [hc'def, DU_Bc, hc']
      have hB0 : Bc c' = 0 := hF _ (Bc_symm c') hD
      have : c' = 0 := by
        by_contra hne; exact Bc_ne c' hne hB0
      funext p
      have := congrFun this p
      simp only [hc'def, Pi.zero_apply] at this
      by_cases h : p.1.1 = p.1.2
      · simpa [h] using this
      · simp only [h, if_false] at this
        have h2 : Real.sqrt 2 ≠ 0 := by positivity
        simpa [h2] using this
    intro x y hxy
    have h0 : DUmat U *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (key _ h0)
  have hpd := Matrix.PosDef.conjTranspose_mul_self (DUmat U) hinj
  exact Real.sqrt_pos.mpr (hpd.eigenvalues_pos j)


end HigherOrderId.Certify.Dev.E82

namespace HigherOrderId.Certify
open Dev.E82

end HigherOrderId.Certify
end

section
open Matrix

namespace HigherOrderId.Certify.Dev.E84
open HigherOrderId.Certify

lemma frobInner_add_right {n : ℕ} (X Y Z : Matrix (Fin n) (Fin n) ℝ) :
    frobInner X (Y + Z) = frobInner X Y + frobInner X Z := by
  simp only [frobInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma frobInner_add_left {n : ℕ} (X Y Z : Matrix (Fin n) (Fin n) ℝ) :
    frobInner (X + Y) Z = frobInner X Z + frobInner Y Z := by
  simp only [frobInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma frobInner_smul_right {n : ℕ} (c : ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobInner X (c • Y) = c * frobInner X Y := by
  simp only [frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma frobInner_smul_left {n : ℕ} (c : ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobInner (c • X) Y = c * frobInner X Y := by
  simp only [frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma frobInner_comm {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) : frobInner X Y = frobInner Y X := by
  simp only [frobInner]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

end HigherOrderId.Certify.Dev.E84
end

section
open Matrix

namespace HigherOrderId.Certify.Dev.B5
open HigherOrderId.Certify
open HigherOrderId.Certify.Dev.E84

lemma symBasis_apply {m : ℕ} (p : SymIdx m) (i j : Fin m) :
    symBasis p i j = if p.1.1 = p.1.2 then (if i = p.1.1 ∧ j = p.1.1 then 1 else 0)
      else (1 / Real.sqrt 2) * ((if i = p.1.1 ∧ j = p.1.2 then 1 else 0) +
        (if i = p.1.2 ∧ j = p.1.1 then 1 else 0)) := by
  unfold symBasis
  by_cases h : p.1.1 = p.1.2
  · simp only [h, if_true]
    simp [Matrix.single_apply, eq_comm]
  · simp only [h, if_false]
    simp [Matrix.single_apply, eq_comm]

lemma frobInner_sum_right {n : ℕ} {ι : Type*} [Fintype ι] (X : Matrix (Fin n) (Fin n) ℝ)
    (f : ι → Matrix (Fin n) (Fin n) ℝ) : frobInner X (∑ q, f q) = ∑ q, frobInner X (f q) := by
  simp only [frobInner, Matrix.sum_apply, Finset.mul_sum]
  calc _ = ∑ i, ∑ q, ∑ j, X i j * f q i j := by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm


lemma symBasis_symm {m : ℕ} (p : SymIdx m) : (symBasis p).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, symBasis_apply]
  by_cases h : p.1.1 = p.1.2
  · simp only [h, if_true]
    by_cases h1 : i = p.1.2 <;> by_cases h2 : j = p.1.2 <;> simp [h1, h2]
  · simp only [h, if_false]; rw [add_comm]; simp only [and_comm]

lemma sym_coord {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.IsSymm) (p : SymIdx m) :
    frobInner B (symBasis p) = if p.1.1 = p.1.2 then B p.1.1 p.1.1 else Real.sqrt 2 * B p.1.1 p.1.2 := by
  have hs : ∀ i j, B j i = B i j := fun i j => by
    have := congrFun (congrFun hB i) j; simpa [Matrix.transpose_apply] using this
  unfold frobInner
  simp only [symBasis_apply]
  by_cases h : p.1.1 = p.1.2
  · simp only [h, if_true]; simp [ite_and]
  · simp only [h, if_false]
    simp only [mul_add, Finset.sum_add_distrib, ite_and]
    simp [hs p.1.1 p.1.2]
    have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
    have h3 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [h4]; ring

lemma sym_expand {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.IsSymm) :
    ∑ p, frobInner B (symBasis p) • symBasis p = B := by
  have hs : ∀ i j, B j i = B i j := fun i j => by
    have := congrFun (congrFun hB i) j; simpa [Matrix.transpose_apply] using this
  have key : ∀ i j, i ≤ j → (∑ p, frobInner B (symBasis p) • symBasis p) i j = B i j := by
    intro i j hij
    rw [Matrix.sum_apply]
    rw [Finset.sum_eq_single (⟨(i, j), hij⟩ : SymIdx m)]
    · rw [Matrix.smul_apply, sym_coord B hB, symBasis_apply]
      by_cases h : i = j
      · subst h; simp
      · simp only [h, if_false, if_true, smul_eq_mul]
        simp [h]
        have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
        have h3 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        field_simp
    · intro q _ hq
      rw [Matrix.smul_apply, symBasis_apply]
      obtain ⟨⟨a, b⟩, hab⟩ := q
      have hab2 : a ≤ b := hab
      by_cases h : a = b
      · subst h
        have : ¬ (i = a ∧ j = a) := fun hh => hq (by simp [hh.1, hh.2])
        simp [this]
      · have h1 : ¬ (i = a ∧ j = b) := fun hh => hq (by simp [hh.1, hh.2])
        have h2 : ¬ (i = b ∧ j = a) := fun hh => by
          have := lt_of_le_of_ne hab2 h; simp at *; omega
        simp [h, h1, h2]
    · intro h; exact absurd (Finset.mem_univ _) h
  ext i j
  rcases le_total i j with h | h
  · exact key i j h
  · have h1 := key j i h
    have h2 : (∑ p, frobInner B (symBasis p) • symBasis p) i j =
        (∑ p, frobInner B (symBasis p) • symBasis p) j i := by
      simp only [Matrix.sum_apply, Matrix.smul_apply]
      apply Finset.sum_congr rfl; intro p _
      congr 1
      have := congrFun (congrFun (symBasis_symm p) i) j
      simpa [Matrix.transpose_apply] using this.symm
    rw [h2, h1, hs]


lemma DU_expand {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (hB : B.IsSymm) : DU U B = DUmat U *ᵥ (fun p => frobInner B (symBasis p)) := by
  funext a
  conv_lhs => rw [← sym_expand B hB]
  simp only [DU, Matrix.mulVec, dotProduct, DUmat, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl; intro p _
  ring

lemma tr_gram_gram_nonneg {p q n : Type*} [Fintype p] [Fintype q] [Fintype n] [DecidableEq n]
    (P : Matrix p n ℝ) (Q : Matrix q n ℝ) : 0 ≤ (Pᵀ * P * (Qᵀ * Q)).trace := by
  have h1 : (Pᵀ * P * (Qᵀ * Q)).trace = ((Q * Pᵀ)ᵀ * (Q * Pᵀ)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h1]
  have := (Matrix.posSemidef_conjTranspose_mul_self (Q * Pᵀ)).trace_nonneg
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma tr_sq_le {p c : Type*} [Fintype p] [Fintype c] [DecidableEq c]
    (K H Z : Matrix p c ℝ) (h : Kᵀ * K + Hᵀ * H = Zᵀ * Z) :
    ((Kᵀ * K) * (Kᵀ * K)).trace ≤ ((Zᵀ * Z) * (Zᵀ * Z)).trace := by
  rw [← h]
  have e : (Kᵀ * K + Hᵀ * H) * (Kᵀ * K + Hᵀ * H) = (Kᵀ * K) * (Kᵀ * K) + (Kᵀ * K) * (Hᵀ * H) +
      ((Hᵀ * H) * (Kᵀ * K) + (Hᵀ * H) * (Hᵀ * H)) := by
    simp only [add_mul, mul_add]; abel
  rw [e, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm (Hᵀ * H)]
  have a1 := tr_gram_gram_nonneg K H
  have a2 := tr_gram_gram_nonneg H H
  linarith


lemma G_spec {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hF : FullColRank U) :
    ∃ (W : Matrix (SymIdx m) (SymIdx m) ℝ) (lam : SymIdx m → ℝ), Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
      (DUmat U)ᵀ * DUmat U = W * Matrix.diagonal lam * Wᵀ ∧
      ∀ j, 0 < lam j ∧ singVals U j = Real.sqrt (lam j) := by
  have hM := Matrix.isHermitian_conjTranspose_mul_self (DUmat U)
  set W : Matrix (SymIdx m) (SymIdx m) ℝ := (hM.eigenvectorUnitary : Matrix (SymIdx m) (SymIdx m) ℝ)
  have hVV : Wᵀ * W = 1 := by
    have := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa [W, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  refine ⟨W, hM.eigenvalues, hVV, mul_eq_one_comm.mp hVV, ?_, ?_⟩
  · have := hM.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at this
    simpa [W, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · intro j
    have hp := Dev.E82.singVals_pos U hF j
    refine ⟨?_, rfl⟩
    have : singVals U j = Real.sqrt (hM.eigenvalues j) := rfl
    rw [this] at hp
    exact Real.sqrt_pos.mp hp


lemma spec_tr {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ) (hW : Wᵀ * W = 1)
    (f : n → ℝ) : (W * Matrix.diagonal f * Wᵀ).trace = ∑ i, f i := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one,
    Matrix.trace_diagonal]

lemma spec_mul {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ) (hW : Wᵀ * W = 1)
    (f g : n → ℝ) :
    (W * Matrix.diagonal f * Wᵀ) * (W * Matrix.diagonal g * Wᵀ) = W * Matrix.diagonal (f * g) * Wᵀ := by
  calc (W * Matrix.diagonal f * Wᵀ) * (W * Matrix.diagonal g * Wᵀ)
      = W * Matrix.diagonal f * (Wᵀ * W) * Matrix.diagonal g * Wᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hW, Matrix.mul_one, Matrix.mul_assoc W, Matrix.diagonal_mul_diagonal]; simp only [Matrix.mul_assoc]; rfl

end HigherOrderId.Certify.Dev.B5
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.B4
open HigherOrderId.Certify

lemma tr_self_mul_transpose_nonneg {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    (K : Matrix p q ℝ) : 0 ≤ (K * Kᵀ).trace := by
  have := (Matrix.posSemidef_self_mul_conjTranspose K).trace_nonneg
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- Upper bounds on `tr M⁻¹` and `tr M⁻²` (`M = AᵀA`) by any left inverse `L` of `A`. -/
lemma up_gen {d n : Type*} [Fintype d] [DecidableEq d] [Fintype n] [DecidableEq n]
    (A : Matrix d n ℝ) (L : Matrix n d ℝ) (hLA : L * A = 1)
    (W : Matrix n n ℝ) (hW1 : Wᵀ * W = 1) (hW2 : W * Wᵀ = 1) (lam : n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hM : Aᵀ * A = W * diagonal lam * Wᵀ) :
    ∑ j, (lam j)⁻¹ ≤ (L * Lᵀ).trace ∧
      ∑ j, (lam j)⁻¹ ^ 2 ≤ (L * Lᵀ * (L * Lᵀ)).trace := by
  obtain ⟨Mi, hMi⟩ : ∃ Mi, Mi = W * diagonal (fun j => (lam j)⁻¹) * Wᵀ := ⟨_, rfl⟩
  have hMiM : Mi * (Aᵀ * A) = 1 := by
    rw [hM, hMi, Dev.B5.spec_mul W hW1]
    have : (fun j => (lam j)⁻¹) * lam = fun _ => (1:ℝ) := by
      funext j; simp [(hlam j).ne']
    rw [this, diagonal_one, Matrix.mul_one, hW2]
  have hMit : Miᵀ = Mi := by
    rw [hMi]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨P, hP⟩ : ∃ P, P = Mi * Aᵀ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = L - P := ⟨_, rfl⟩
  have hKA : K * A = 0 := by
    rw [hK, Matrix.sub_mul, hLA, hP, Matrix.mul_assoc, hMiM, sub_self]
  have hPP : P * Pᵀ = Mi := by
    rw [hP, Matrix.transpose_mul, Matrix.transpose_transpose, hMit]
    calc Mi * Aᵀ * (A * Mi) = (Mi * (Aᵀ * A)) * Mi := by simp only [Matrix.mul_assoc]
      _ = Mi := by rw [hMiM, Matrix.one_mul]
  have hPK : P * Kᵀ = 0 := by
    rw [hP, Matrix.mul_assoc, ← Matrix.transpose_mul, hKA, Matrix.transpose_zero,
      Matrix.mul_zero]
  have hKP : K * Pᵀ = 0 := by
    have := congrArg Matrix.transpose hPK
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this
  have hL : L = P + K := by rw [hK]; abel
  have hLL : L * Lᵀ = Mi + K * Kᵀ := by
    rw [hL, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hPP, hPK,
      hKP]
    abel
  have htrMi : Mi.trace = ∑ j, (lam j)⁻¹ := by rw [hMi, Dev.B5.spec_tr W hW1]
  refine ⟨?_, ?_⟩
  · rw [hLL, Matrix.trace_add, htrMi]
    linarith [tr_self_mul_transpose_nonneg K]
  · have h := Dev.B5.tr_sq_le Pᵀ Kᵀ Lᵀ (by
      simp only [Matrix.transpose_transpose]; rw [hPP, hLL])
    simp only [Matrix.transpose_transpose] at h
    rw [hPP, hMi, Dev.B5.spec_mul W hW1, Dev.B5.spec_tr W hW1] at h
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl; intro j _; simp [sq]

/-- pointwise tangent-line bound for `x ↦ x⁻²`. -/
lemma tangent (x μ : ℝ) (hx : 0 < x) (hμ : 0 < μ) :
    3 / μ ^ 2 - 2 * x / μ ^ 3 ≤ x⁻¹ ^ 2 := by
  have : x⁻¹ ^ 2 - (3 / μ ^ 2 - 2 * x / μ ^ 3) = (μ - x) ^ 2 * (μ + 2 * x) / (μ ^ 3 * x ^ 2) := by
    field_simp; ring
  have h2 : 0 ≤ (μ - x) ^ 2 * (μ + 2 * x) / (μ ^ 3 * x ^ 2) := by positivity
  linarith

/-- Hölder-type inequality `(Σ q)³ ≤ (Σ qλ)² Σ qλ⁻²`. -/
lemma holder3 {n : Type*} [Fintype n] (q lam : n → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hlam : ∀ j, 0 < lam j) (hS : 0 < ∑ j, q j * lam j) :
    (∑ j, q j) ^ 3 ≤ (∑ j, q j * lam j) ^ 2 * ∑ j, q j * (lam j)⁻¹ ^ 2 := by
  set Q := ∑ j, q j with hQ
  set S := ∑ j, q j * lam j with hSdef
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => hq j)
  rcases hQ0.eq_or_lt with h0 | hQpos
  · rw [← h0]
    have : 0 ≤ ∑ j, q j * (lam j)⁻¹ ^ 2 :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hq j) (by positivity))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  set μ := S / Q with hμ
  have hμpos : 0 < μ := div_pos hS hQpos
  have hpt : ∀ j, q j * (3 / μ ^ 2 - 2 * lam j / μ ^ 3) ≤ q j * (lam j)⁻¹ ^ 2 :=
    fun j => mul_le_mul_of_nonneg_left (tangent (lam j) μ (hlam j) hμpos) (hq j)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpt j)
  have hlhs : ∑ j, q j * (3 / μ ^ 2 - 2 * lam j / μ ^ 3) = 3 * Q / μ ^ 2 - 2 * S / μ ^ 3 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hQ, hSdef, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.sum_div]
    congr 1
    · apply Finset.sum_congr rfl; intro j _; ring
    · apply Finset.sum_congr rfl; intro j _; ring
  rw [hlhs] at hsum
  have hval : 3 * Q / μ ^ 2 - 2 * S / μ ^ 3 = Q ^ 3 / S ^ 2 := by
    rw [hμ]; field_simp; ring
  rw [hval, div_le_iff₀ (by positivity)] at hsum
  linarith [hsum]

/-- Lower bound on `tr M⁻²` from a family `Y` on which `M` acts as a multiple of the identity
(relative to the Gram matrix `γ P`). -/
lemma low_gen {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (W : Matrix n n ℝ) (hW2 : W * Wᵀ = 1) (lam : n → ℝ) (hlam : ∀ j, 0 < lam j)
    (Y : Matrix n k ℝ) (P : Matrix k k ℝ) (γ h : ℝ) (hγ : 0 < γ) (hh : 0 < h)
    (hG : Yᵀ * Y = γ • P) (hYP : Y * P = Y) (hH : Yᵀ * (W * diagonal lam * Wᵀ) * Y = h • P)
    (hr : 0 < P.trace) :
    P.trace * γ ^ 2 / h ^ 2 ≤ ∑ j, (lam j)⁻¹ ^ 2 := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = Wᵀ * Y := ⟨_, rfl⟩
  have hZZ : Zᵀ * Z = γ • P := by
    rw [hZ, Matrix.transpose_mul, Matrix.transpose_transpose, ← hG]
    calc Yᵀ * W * (Wᵀ * Y) = Yᵀ * (W * Wᵀ) * Y := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW2, Matrix.mul_one]
  have hZP : Z * P = Z := by rw [hZ, Matrix.mul_assoc, hYP]
  obtain ⟨N, hN⟩ : ∃ N, N = Z * Zᵀ := ⟨_, rfl⟩
  have hNN : N * N = γ • N := by
    rw [hN]
    calc Z * Zᵀ * (Z * Zᵀ) = Z * (Zᵀ * Z) * Zᵀ := by simp only [Matrix.mul_assoc]
      _ = γ • (Z * P * Zᵀ) := by rw [hZZ]; simp [Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by rw [hZP]
  have hNsym : ∀ i j, N i j = N j i := by
    intro i j; rw [hN]; simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl; intro l _; ring
  have hN0 : ∀ j, 0 ≤ N j j := by
    intro j; rw [hN]; simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_nonneg (fun l _ => mul_self_nonneg _)
  have hNle : ∀ j, N j j ≤ γ := by
    intro j
    have h1 : (N * N) j j = γ * N j j := by rw [hNN]; simp
    have h2 : N j j * N j j ≤ (N * N) j j := by
      rw [Matrix.mul_apply]
      have := Finset.single_le_sum (f := fun l => N j l * N l j)
        (fun l _ => by rw [hNsym l j]; exact mul_self_nonneg _) (Finset.mem_univ j)
      simpa using this
    rw [h1] at h2
    have := hN0 j
    nlinarith
  have hsumN : ∑ j, N j j = γ * P.trace := by
    have : N.trace = (Zᵀ * Z).trace := by rw [hN, Matrix.trace_mul_comm]
    rw [hZZ, Matrix.trace_smul, smul_eq_mul] at this
    rw [← this]; rfl
  have hsumL : ∑ j, lam j * N j j = h * P.trace := by
    have e1 : (diagonal lam * N).trace = ∑ j, lam j * N j j := by
      simp [Matrix.trace, Matrix.diagonal_mul]
    have e2 : (diagonal lam * N).trace = (Yᵀ * (W * diagonal lam * Wᵀ) * Y).trace := by
      rw [hN, hZ, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.transpose_mul,
        Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    rw [← e1, e2, hH, Matrix.trace_smul, smul_eq_mul]
  set q : n → ℝ := fun j => N j j / γ with hq
  have hq0 : ∀ j, 0 ≤ q j := fun j => div_nonneg (hN0 j) hγ.le
  have hq1 : ∀ j, q j ≤ 1 := fun j => (div_le_one hγ).mpr (hNle j)
  have hQ : ∑ j, q j = P.trace := by
    simp only [hq, ← Finset.sum_div, hsumN]; field_simp
  have hS : ∑ j, q j * lam j = h * P.trace / γ := by
    simp only [hq]
    rw [← hsumL, Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _; ring
  have hSpos : 0 < ∑ j, q j * lam j := by rw [hS]; positivity
  have hH3 := holder3 q lam hq0 hlam hSpos
  rw [hQ, hS] at hH3
  have hle : ∑ j, q j * (lam j)⁻¹ ^ 2 ≤ ∑ j, (lam j)⁻¹ ^ 2 := by
    apply Finset.sum_le_sum; intro j _
    have : 0 ≤ (lam j)⁻¹ ^ 2 := by positivity
    nlinarith [hq1 j]
  set X := ∑ j, q j * (lam j)⁻¹ ^ 2
  set r := P.trace
  rw [div_le_iff₀ (by positivity)]
  have : r * γ ^ 2 ≤ X * h ^ 2 := by
    have e : (h * r / γ) ^ 2 * X = (h ^ 2 * X / γ ^ 2) * r ^ 2 := by ring
    rw [e] at hH3
    have hr2 : 0 < r ^ 2 := by positivity
    have : r ≤ h ^ 2 * X / γ ^ 2 := by nlinarith
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  nlinarith
end HigherOrderId.Certify.Dev.B4
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.B4
open HigherOrderId.Certify
open HigherOrderId.Certify.Dev.E84

/-! ## The frame `G_w = Pio · FR` and `S_w` -/

/-- the nonzero frame rows as a `FrameRows m × m` matrix -/
noncomputable def FR (m : ℕ) (w : ℝ) : Matrix (FrameRows m) (Fin m) ℝ := fun r c => frameRow w r c

/-- the placement matrix of `ι` -/
noncomputable def Pio {d m : ℕ} (ι : FrameRows m ↪ Fin d) : Matrix (Fin d) (FrameRows m) ℝ :=
  fun a r => if ι r = a then 1 else 0

lemma Gw_eq {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) : Gw ι w = Pio ι * FR m w := by
  ext a c
  simp only [Gw, Pio, FR, Matrix.mul_apply, ite_mul, one_mul, zero_mul]

lemma Pio_tt {d m : ℕ} (ι : FrameRows m ↪ Fin d) : (Pio ι)ᵀ * Pio ι = 1 := by
  ext r s
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Pio, Matrix.one_apply]
  rw [Finset.sum_eq_single (ι r)]
  · by_cases h : r = s
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma Sw_eq {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) : Sw ι w = (FR m w)ᵀ * FR m w := by
  rw [Sw, Gw_eq, Matrix.transpose_mul]
  calc (FR m w)ᵀ * (Pio ι)ᵀ * (Pio ι * FR m w) = (FR m w)ᵀ * ((Pio ι)ᵀ * Pio ι) * FR m w := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Pio_tt, Matrix.mul_one]

lemma frameRow_inl {m : ℕ} (w : ℝ) (i : Fin m) :
    frameRow w (Sum.inl i) = Real.sqrt w • (Pi.single i 1 : Fin m → ℝ) := by
  funext c; by_cases h : c = i <;> simp [frameRow, h]

lemma frameRow_inr {m : ℕ} (w : ℝ) (p : {p : Fin m × Fin m // p.1 < p.2}) :
    frameRow w (Sum.inr p) = (Pi.single p.1.1 1 + Pi.single p.1.2 1 : Fin m → ℝ) := by
  funext c
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  by_cases h1 : c = p.1.1 <;> by_cases h2 : c = p.1.2
  · exact absurd (h1.symm.trans h2) hne
  · simp [frameRow, h1, h2, Pi.single_apply, hne]
  · simp [frameRow, h1, h2, Pi.single_apply, Ne.symm hne]
  · simp [frameRow, h1, h2, Pi.single_apply]

/-- `2 Σ_{i<j} g i j = Σ_{i,j} g i j - Σ_i g i i` for symmetric `g`. -/
lemma sum_lt {m : ℕ} (g : Fin m → Fin m → ℝ) (hg : ∀ i j, g i j = g j i) :
    2 * ∑ p : {p : Fin m × Fin m // p.1 < p.2}, g p.1.1 p.1.2 =
      ∑ i, ∑ j, g i j - ∑ i, g i i := by
  have h1 : ∑ p : {p : Fin m × Fin m // p.1 < p.2}, g p.1.1 p.1.2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2), g p.1 p.2 :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2))
      (by intro x; simp) (fun p => g p.1 p.2)).symm
  rw [h1, Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ i, ∑ j, g i j = ∑ i, ∑ j, ((if i < j then g i j else 0) +
      (if j < i then g i j else 0) + (if i = j then g i j else 0)) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le, ne_of_lt h]
    · subst h; simp
    · simp [h, not_lt.mpr h.le, ne_of_gt h]
  have h3 : ∑ i, ∑ j, (if j < i then g i j else 0) = ∑ i, ∑ j, (if i < j then g i j else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [hg]
  have h4 : ∑ i, ∑ j, (if i = j then g i j else 0) = ∑ i, g i i := by
    apply Finset.sum_congr rfl; intro i _; simp
  rw [h2]
  simp only [Finset.sum_add_distrib]
  rw [h3, h4]; ring

lemma sum_pair_prod {m : ℕ} (x y : Fin m → ℝ) :
    ∑ i, ∑ j, (x i + x j) * (y i + y j) =
      2 * (m : ℝ) * (x ⬝ᵥ y) + 2 * ((x ⬝ᵥ 1) * (y ⬝ᵥ 1)) := by
  have e : ∀ i j, (x i + x j) * (y i + y j) = x i * y i + x j * y j + (x i * y j + x j * y i) :=
    fun i j => by ring
  simp only [e, Finset.sum_add_distrib]
  have a1 : ∑ i : Fin m, ∑ _j : Fin m, x i * y i = m * (x ⬝ᵥ y) := by
    simp [dotProduct, Finset.mul_sum]
  have a2 : ∑ _i : Fin m, ∑ j : Fin m, x j * y j = m * (x ⬝ᵥ y) := by
    simp [dotProduct]
  have a3 : ∑ i : Fin m, ∑ j : Fin m, x i * y j = (x ⬝ᵥ 1) * (y ⬝ᵥ 1) := by
    simp [dotProduct, Finset.sum_mul_sum]
  have a4 : ∑ i : Fin m, ∑ j : Fin m, x j * y i = (x ⬝ᵥ 1) * (y ⬝ᵥ 1) := by
    rw [Finset.sum_comm]; simp [dotProduct, Finset.sum_mul_sum]
  rw [a1, a2, a3, a4]; ring

/-- `S_w = (w + m - 2) I + J` as a bilinear form. -/
lemma Sb_eq {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 ≤ w) (x y : Fin m → ℝ) :
    x ⬝ᵥ (Sw ι w *ᵥ y) = (w + m - 2) * (x ⬝ᵥ y) + (x ⬝ᵥ 1) * (y ⬝ᵥ 1) := by
  rw [Sw_eq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hr : ∀ (z : Fin m → ℝ) r, (FR m w *ᵥ z) r = frameRow w r ⬝ᵥ z := fun z r => rfl
  simp only [dotProduct.eq_1 (FR m w *ᵥ x), hr, Fintype.sum_sum_type, frameRow_inl, frameRow_inr]
  have hl : ∀ i, (Real.sqrt w • (Pi.single i 1 : Fin m → ℝ)) ⬝ᵥ x *
      ((Real.sqrt w • (Pi.single i 1 : Fin m → ℝ)) ⬝ᵥ y) = w * (x i * y i) := by
    intro i
    simp only [smul_dotProduct, smul_eq_mul]
    have : (Pi.single i 1 : Fin m → ℝ) ⬝ᵥ x = x i := by simp
    have h2 : (Pi.single i 1 : Fin m → ℝ) ⬝ᵥ y = y i := by simp
    rw [this, h2]
    have := Real.mul_self_sqrt hw
    calc √w * x i * (√w * y i) = (√w * √w) * (x i * y i) := by ring
      _ = _ := by rw [this]
  have hp : ∀ p : {p : Fin m × Fin m // p.1 < p.2},
      (Pi.single p.1.1 1 + Pi.single p.1.2 1 : Fin m → ℝ) ⬝ᵥ x *
        ((Pi.single p.1.1 1 + Pi.single p.1.2 1 : Fin m → ℝ) ⬝ᵥ y) =
      (x p.1.1 + x p.1.2) * (y p.1.1 + y p.1.2) := by
    intro p; simp [add_dotProduct]
  simp only [hl, hp]
  have hs := sum_lt (fun i j => (x i + x j) * (y i + y j)) (fun i j => by ring)
  rw [sum_pair_prod] at hs
  have hd : ∑ i, (x i + x i) * (y i + y i) = 4 * (x ⬝ᵥ y) := by
    simp only [dotProduct, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hd] at hs
  have hw' : ∑ i, w * (x i * y i) = w * (x ⬝ᵥ y) := by simp [dotProduct, Finset.mul_sum]
  rw [hw']
  linarith

/-! ## The equivalence `FrameRows m ≃ SymIdx m` -/

def frEquiv (m : ℕ) : FrameRows m ≃ SymIdx m where
  toFun r := match r with
    | .inl i => ⟨(i, i), le_rfl⟩
    | .inr p => ⟨p.1, p.2.le⟩
  invFun q := if h : q.1.1 = q.1.2 then .inl q.1.1 else .inr ⟨q.1, lt_of_le_of_ne q.2 h⟩
  left_inv r := by
    rcases r with i | p
    · simp
    · simp [ne_of_lt p.2]
  right_inv q := by
    by_cases h : q.1.1 = q.1.2
    · simp only [h, dite_true]
      apply Subtype.ext; ext <;> simp [h]
    · simp [h]

/-! ## Symmetric rank-two forms -/

noncomputable def symF {m : ℕ} (u v : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 / 2 : ℝ) • (vecMulVec u v + vecMulVec v u)

lemma symF_symm {m : ℕ} (u v : Fin m → ℝ) : (symF u v).IsSymm := by
  unfold Matrix.IsSymm symF
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_vecMulVec,
    Matrix.transpose_vecMulVec, add_comm]

lemma symF_apply {m : ℕ} (u v : Fin m → ℝ) (i j : Fin m) :
    symF u v i j = (u i * v j + v i * u j) / 2 := by
  simp [symF, vecMulVec_apply]; ring

lemma quad_symF {m : ℕ} (u v f : Fin m → ℝ) :
    f ⬝ᵥ (symF u v *ᵥ f) = (f ⬝ᵥ u) * (f ⬝ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec, symF_apply, Finset.mul_sum, Finset.sum_mul]
  have : ∀ i j, f i * ((u i * v j + v i * u j) / 2 * f j) =
      (f i * u i * (f j * v j) + f j * u j * (f i * v i)) / 2 := fun i j => by ring
  simp only [this, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => f j * u j * (f i * v i))]
  ring

lemma conj_symF {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (u v : Fin m → ℝ) :
    R * symF u v * R = symF (R *ᵥ u) (R *ᵥ v) := by
  have h1 : ∀ x y : Fin m → ℝ, R * vecMulVec x y * R = vecMulVec (R *ᵥ x) (R *ᵥ y) := by
    intro x y
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    congr 1
    conv_lhs => rw [← hRt]
    rw [Matrix.vecMul_transpose]
  unfold symF
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, h1, h1]

lemma inner_vmv {m : ℕ} (a b a' b' : Fin m → ℝ) :
    frobInner (vecMulVec a b) (vecMulVec a' b') = (a ⬝ᵥ a') * (b ⬝ᵥ b') := by
  simp only [frobInner, vecMulVec_apply, dotProduct, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma inner_symF {m : ℕ} (a b a' b' : Fin m → ℝ) :
    frobInner (symF a b) (symF a' b') =
      (1 / 2) * ((a ⬝ᵥ a') * (b ⬝ᵥ b') + (a ⬝ᵥ b') * (b ⬝ᵥ a')) := by
  unfold symF
  rw [frobInner_smul_left, frobInner_smul_right, frobInner_add_left, frobInner_add_right,
    frobInner_add_right, inner_vmv, inner_vmv, inner_vmv, inner_vmv]
  rw [dotProduct_comm b a', dotProduct_comm b b', dotProduct_comm a b', dotProduct_comm a a']
  ring

lemma Rdot {m : ℕ} (R S : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (hRR : R * R = S)
    (x y : Fin m → ℝ) : (R *ᵥ x) ⬝ᵥ (R *ᵥ y) = x ⬝ᵥ (S *ᵥ y) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hRt, hRR]

/-- the Gram entries of conjugated rank-two forms -/
lemma inner_conj_symF {m : ℕ} (R S : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (hRR : R * R = S)
    (u v u' v' : Fin m → ℝ) :
    frobInner (R * symF u v * R) (R * symF u' v' * R) =
      (1 / 2) * ((u ⬝ᵥ (S *ᵥ u')) * (v ⬝ᵥ (S *ᵥ v')) + (u ⬝ᵥ (S *ᵥ v')) * (v ⬝ᵥ (S *ᵥ u'))) := by
  rw [conj_symF R hRt, conj_symF R hRt, inner_symF, Rdot R S hRt hRR, Rdot R S hRt hRR,
    Rdot R S hRt hRR, Rdot R S hRt hRR]

/-! ## The left inverse of `D_G` -/

noncomputable def vv {m : ℕ} (i : Fin m) : Fin m → ℝ := (2:ℝ) • (Pi.single i 1 : Fin m → ℝ) - 1

noncomputable def uF {m : ℕ} : FrameRows m → Fin m → ℝ
  | .inl i => Pi.single i 1
  | .inr p => Pi.single p.1.1 1

noncomputable def vF {m : ℕ} : FrameRows m → Fin m → ℝ
  | .inl i => vv i
  | .inr p => Pi.single p.1.2 1

noncomputable def kF {m : ℕ} (w : ℝ) : FrameRows m → ℝ
  | .inl _ => w⁻¹
  | .inr _ => 1

noncomputable def Cfr {m : ℕ} (w : ℝ) (r : FrameRows m) : Matrix (Fin m) (Fin m) ℝ :=
  kF w r • symF (uF r) (vF r)

lemma Cfr_symm {m : ℕ} (w : ℝ) (r : FrameRows m) : (Cfr w r).IsSymm := by
  unfold Cfr Matrix.IsSymm
  rw [Matrix.transpose_smul, (symF_symm _ _).eq]

/-- `D_G(X)_r = f_rᵀ X f_r` -/
noncomputable def DG {m : ℕ} (w : ℝ) (X : Matrix (Fin m) (Fin m) ℝ) : FrameRows m → ℝ :=
  fun r => frameRow w r ⬝ᵥ (X *ᵥ frameRow w r)

lemma single_apply' {m : ℕ} (a c : Fin m) : (Pi.single a (1:ℝ) : Fin m → ℝ) c = if c = a then 1 else 0 :=
  Pi.single_apply a 1 c

lemma single_dot {m : ℕ} (c : Fin m) (x : Fin m → ℝ) : (Pi.single c 1 : Fin m → ℝ) ⬝ᵥ x = x c := by
  simp

lemma single_dot_one {m : ℕ} (c : Fin m) : (Pi.single c 1 : Fin m → ℝ) ⬝ᵥ 1 = 1 := by
  simp

lemma vv_apply {m : ℕ} (i k : Fin m) : vv i k = 2 * (if k = i then 1 else 0) - 1 := by
  simp [vv, Pi.single_apply]

lemma DG_Cfr {m : ℕ} (w : ℝ) (hw : 0 < w) (r s : FrameRows m) :
    DG w (Cfr w r) s = if r = s then 1 else 0 := by
  have hsq := Real.mul_self_sqrt hw.le
  have hwne : w ≠ 0 := hw.ne'
  unfold DG Cfr
  rw [Matrix.smul_mulVec, dotProduct_smul, quad_symF, smul_eq_mul]
  rcases r with i | p <;> rcases s with k | q
  · simp only [kF, uF, vF, frameRow_inl, smul_dotProduct, vv_apply, smul_eq_mul, single_dot,
      single_dot_one, single_apply', Sum.inl.injEq]
    by_cases h : k = i
    · subst h; simp only [if_true]; field_simp; nlinarith [hsq]
    · simp only [h, Ne.symm h, if_false]; ring
  · simp only [kF, uF, vF, frameRow_inr, vv_apply, add_dotProduct, single_dot, single_dot_one,
      single_apply', reduceCtorEq, if_false]
    have hne : q.1.1 ≠ q.1.2 := ne_of_lt q.2
    split_ifs with h1 h2 h2 <;> first | ring1 | (exfalso; exact hne (h1.trans h2.symm))
  · simp only [kF, uF, vF, frameRow_inl, smul_dotProduct, single_dot, single_apply',
      reduceCtorEq, if_false, smul_eq_mul]
    have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
    split_ifs with h1 h2 <;> first | ring1 | (exfalso; exact hne (h1.symm.trans h2))
  · simp only [kF, uF, vF, frameRow_inr, add_dotProduct, single_dot, single_apply',
      Sum.inr.injEq]
    have hpl : p.1.1 < p.1.2 := p.2
    have hql : q.1.1 < q.1.2 := q.2
    have key : p = q ↔ (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := by
      constructor
      · intro h; subst h; exact ⟨rfl, rfl⟩
      · intro hh; exact Subtype.ext (Prod.ext hh.1 hh.2)
    by_cases h : p = q
    · subst h
      have hne : p.1.1 ≠ p.1.2 := ne_of_lt hpl
      simp [hne, Ne.symm hne]
    · rw [if_neg h]
      have hne' : ¬ (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := fun hh => h (key.mpr hh)
      split_ifs <;> first | ring1 | (exfalso; omega) |
        (exfalso; apply hne'; constructor <;> (symm; assumption))

end HigherOrderId.Certify.Dev.B4
end

section
set_option autoImplicit false
open Matrix
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.B4
open HigherOrderId.Certify
open HigherOrderId.Certify.Dev.E84

lemma sqrt_mul_self_Sw {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) :
    CFC.sqrt (Sw ι w) * CFC.sqrt (Sw ι w) = Sw ι w := by
  have hS : (0 : Matrix (Fin m) (Fin m) ℝ) ≤ Sw ι w := by
    have := Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self (Gw ι w))
    simpa [Sw, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  exact CFC.sqrt_mul_sqrt_self _ hS

lemma DU_on {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (Ri : Matrix (Fin m) (Fin m) ℝ)
    (hRit : Riᵀ = Ri) (hU : Uw ι w = Gw ι w * Ri) (B : Matrix (Fin m) (Fin m) ℝ)
    (s : FrameRows m) : DU (Uw ι w) B (ι s) = DG w (Ri * B * Ri) s := by
  unfold DU
  rw [hU, Matrix.transpose_mul, hRit]
  have e : Gw ι w * Ri * B * (Ri * (Gw ι w)ᵀ) = Gw ι w * (Ri * B * Ri) * (Gw ι w)ᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e, Dev.E82.quad_gen]
  simp only [Dev.B2.Gw_apply]
  unfold DG
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; ring

lemma DU_off {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (a : Fin d) (ha : ∀ r, ι r ≠ a) : DU (Uw ι w) B a = 0 := by
  have hG : ∀ c, Gw ι w a c = 0 := by
    intro c; unfold Gw; simp [ha]
  unfold DU Uw
  have e : Gw ι w * (CFC.sqrt (Sw ι w))⁻¹ * B * (Gw ι w * (CFC.sqrt (Sw ι w))⁻¹)ᵀ =
      Gw ι w * ((CFC.sqrt (Sw ι w))⁻¹ * B * ((CFC.sqrt (Sw ι w))⁻¹)ᵀ) * (Gw ι w)ᵀ := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [e, Dev.E82.quad_gen]
  simp [hG]

lemma RCR_symm {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (w : ℝ) (r : FrameRows m) :
    (R * Cfr w r * R).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hRt, (Cfr_symm w r).eq, Matrix.mul_assoc]

/-- coordinates of `R C_r R` in `symBasis` -/
noncomputable def Lfr {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (w : ℝ) :
    Matrix (SymIdx m) (FrameRows m) ℝ :=
  fun p r => frobInner (R * Cfr w r * R) (symBasis p)

/-- the Gram matrix `Γ_{rs} = ⟨R C_r R, R C_s R⟩` -/
noncomputable def Gam {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (w : ℝ) :
    Matrix (FrameRows m) (FrameRows m) ℝ :=
  fun r s => frobInner (R * Cfr w r * R) (R * Cfr w s * R)

lemma parseval {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℝ) (hY : Y.IsSymm) :
    ∑ p, frobInner X (symBasis p) * frobInner Y (symBasis p) = frobInner X Y := by
  conv_rhs => rw [← Dev.B5.sym_expand Y hY]
  rw [Dev.B5.frobInner_sum_right]
  apply Finset.sum_congr rfl; intro p _
  rw [frobInner_smul_right]; ring

lemma LtL_eq {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (w : ℝ) :
    (Lfr R w)ᵀ * Lfr R w = Gam R w := by
  ext r s
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Lfr, Gam]
  exact parseval _ _ (RCR_symm R hRt w s)

lemma A_Lfr {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w)
    (R Ri : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (hRit : Riᵀ = Ri) (hRiR : Ri * R = 1)
    (hRRi : R * Ri = 1) (hU : Uw ι w = Gw ι w * Ri) :
    DUmat (Uw ι w) * Lfr R w = Pio ι := by
  ext a r
  have h1 : (DUmat (Uw ι w) * Lfr R w) a r = DU (Uw ι w) (R * Cfr w r * R) a := by
    rw [Dev.B5.DU_expand _ _ (RCR_symm R hRt w r)]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Lfr]
  rw [h1]
  by_cases ha : ∃ s, ι s = a
  · obtain ⟨s, rfl⟩ := ha
    rw [DU_on ι w Ri hRit hU]
    have e : Ri * (R * Cfr w r * R) * Ri = Cfr w r := by
      calc Ri * (R * Cfr w r * R) * Ri = (Ri * R) * Cfr w r * (R * Ri) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hRiR, hRRi, Matrix.one_mul, Matrix.mul_one]
    rw [e, DG_Cfr w hw]
    simp [Pio]
  · push Not at ha
    rw [DU_off ι w _ a ha]
    simp [Pio, ha r]

lemma Lfr_left {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w)
    (R Ri : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (hRit : Riᵀ = Ri) (hRiR : Ri * R = 1)
    (hRRi : R * Ri = 1) (hU : Uw ι w = Gw ι w * Ri) :
    (Lfr R w * (Pio ι)ᵀ) * DUmat (Uw ι w) = 1 := by
  have h : ((Pio ι)ᵀ * DUmat (Uw ι w)) * Lfr R w = 1 := by
    rw [Matrix.mul_assoc, A_Lfr ι w hw R Ri hRt hRit hRiR hRRi hU, Pio_tt]
  rw [Matrix.mul_assoc]
  exact (Matrix.mul_eq_one_comm_of_equiv (frEquiv m)).mp h

lemma LLt_eq {d m : ℕ} (ι : FrameRows m ↪ Fin d) (R : Matrix (Fin m) (Fin m) ℝ) (w : ℝ) :
    (Lfr R w * (Pio ι)ᵀ) * (Lfr R w * (Pio ι)ᵀ)ᵀ = Lfr R w * (Lfr R w)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc Lfr R w * (Pio ι)ᵀ * (Pio ι * (Lfr R w)ᵀ) = Lfr R w * ((Pio ι)ᵀ * Pio ι) * (Lfr R w)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Pio_tt, Matrix.mul_one]

lemma tr_LLt {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (w : ℝ) :
    (Lfr R w * (Lfr R w)ᵀ).trace = (Gam R w).trace := by
  rw [Matrix.trace_mul_comm, LtL_eq R hRt]

lemma tr_LLt2 {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (w : ℝ) :
    (Lfr R w * (Lfr R w)ᵀ * (Lfr R w * (Lfr R w)ᵀ)).trace = (Gam R w * Gam R w).trace := by
  rw [← LtL_eq R hRt]
  calc (Lfr R w * (Lfr R w)ᵀ * (Lfr R w * (Lfr R w)ᵀ)).trace
      = (Lfr R w * ((Lfr R w)ᵀ * Lfr R w * (Lfr R w)ᵀ)).trace := by simp only [Matrix.mul_assoc]
    _ = ((Lfr R w)ᵀ * Lfr R w * (Lfr R w)ᵀ * Lfr R w).trace := by
        rw [Matrix.trace_mul_comm]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- the bilinear form of `S_w = a I + J` -/
noncomputable def sbf {m : ℕ} (a : ℝ) (x y : Fin m → ℝ) : ℝ := a * (x ⬝ᵥ y) + (x ⬝ᵥ 1) * (y ⬝ᵥ 1)

lemma Gam_formula {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 ≤ w)
    (R : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (hRR : R * R = Sw ι w) (r s : FrameRows m) :
    Gam R w r s = kF w r * kF w s * ((1 / 2) *
      (sbf (w + m - 2) (uF r) (uF s) * sbf (w + m - 2) (vF r) (vF s) +
        sbf (w + m - 2) (uF r) (vF s) * sbf (w + m - 2) (vF r) (uF s))) := by
  unfold Gam Cfr
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, frobInner_smul_left,
    frobInner_smul_right, inner_conj_symF R (Sw ι w) hRt hRR]
  simp only [Sb_eq ι w hw, sbf]
  ring

lemma Gam_symm {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (w : ℝ) (r s : FrameRows m) :
    Gam R w r s = Gam R w s r := frobInner_comm _ _

end HigherOrderId.Certify.Dev.B4
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.B4
open HigherOrderId.Certify

/-! ## Values of the bilinear form on the frame vectors -/

lemma one_dot_one (m : ℕ) : (1 : Fin m → ℝ) ⬝ᵥ 1 = m := by simp

lemma vv_dot_one {m : ℕ} (k : Fin m) : vv k ⬝ᵥ 1 = 2 - m := by
  simp only [vv, sub_dotProduct, smul_dotProduct, single_dot_one, one_dot_one, smul_eq_mul]
  ring

lemma sbf_ee {m : ℕ} (a : ℝ) (i k : Fin m) :
    sbf a (Pi.single i 1) (Pi.single k 1) = a * (if i = k then 1 else 0) + 1 := by
  simp only [sbf, single_dot_one, single_dot, single_apply', Pi.one_apply]; ring

lemma sbf_ev {m : ℕ} (a : ℝ) (i k : Fin m) :
    sbf a (Pi.single i 1) (vv k) = a * (2 * (if i = k then 1 else 0) - 1) + (2 - m) := by
  simp only [sbf, single_dot_one, vv_dot_one, single_dot, vv_apply, Pi.one_apply]; ring

lemma sbf_comm {m : ℕ} (a : ℝ) (x y : Fin m → ℝ) : sbf a x y = sbf a y x := by
  simp only [sbf, dotProduct_comm x y]; ring

lemma sbf_ve {m : ℕ} (a : ℝ) (i k : Fin m) :
    sbf a (vv i) (Pi.single k 1) = a * (2 * (if k = i then 1 else 0) - 1) + (2 - m) := by
  rw [sbf_comm, sbf_ev]

lemma sbf_vv {m : ℕ} (a : ℝ) (i k : Fin m) :
    sbf a (vv i) (vv k) = a * (4 * (if i = k then 1 else 0) - 4 + m) + (2 - m) ^ 2 := by
  have h : vv i ⬝ᵥ vv k = 4 * (if i = k then 1 else 0) - 4 + m := by
    have e : vv i ⬝ᵥ vv k = 2 * vv k i - vv k ⬝ᵥ 1 := by
      conv_lhs => rw [vv]
      rw [sub_dotProduct, smul_dotProduct, single_dot, smul_eq_mul, dotProduct_comm 1]
    rw [e, vv_apply, vv_dot_one]; ring
  simp only [sbf, h, vv_dot_one]; ring

/-! ## The Gram entries -/

/-- `s(i,k) = e_iᵀ S e_k` -/
noncomputable def sE (a : ℝ) {m : ℕ} (i k : Fin m) : ℝ := a * (if i = k then 1 else 0) + 1

/-- `t(i,k) = (2e_i - 1)ᵀ S e_k` -/
noncomputable def tE (a : ℝ) {m : ℕ} (i k : Fin m) : ℝ :=
  a * (2 * (if k = i then 1 else 0) - 1) + (2 - m)

noncomputable def E0 (a m : ℝ) : ℝ := (1 / 2) * (a * (m - 4) + (2 - m) ^ 2 + (a + m - 2) ^ 2)

noncomputable def E1 (a m : ℝ) : ℝ := (1 / 2) * ((a + 1) * (a * m + (2 - m) ^ 2) + (a + 2 - m) ^ 2)

section
variable {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 ≤ w)
  (R : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (hRR : R * R = Sw ι w)
include hw hRt hRR

lemma Gam_ll (i j : Fin m) :
    Gam R w (.inl i) (.inl j) = (if i = j then E1 (w + m - 2) m else E0 (w + m - 2) m) / w ^ 2 := by
  rw [Gam_formula ι w hw R hRt hRR]
  simp only [kF, uF, vF, sbf_ee, sbf_ev, sbf_ve, sbf_vv]
  by_cases h : i = j
  · subst h; simp only [if_true, E1]; field_simp; ring
  · simp only [h, Ne.symm h, if_false, E0]; field_simp; ring

lemma Gam_lr (i : Fin m) (q : {p : Fin m × Fin m // p.1 < p.2}) :
    Gam R w (.inl i) (.inr q) = w⁻¹ * ((1 / 2) *
      (sE (w + m - 2) i q.1.1 * tE (w + m - 2) i q.1.2 +
        sE (w + m - 2) i q.1.2 * tE (w + m - 2) i q.1.1)) := by
  rw [Gam_formula ι w hw R hRt hRR]
  simp only [kF, uF, vF, sbf_ee, sbf_ev, sbf_ve, sE, tE]
  ring

lemma Gam_rr (p q : {p : Fin m × Fin m // p.1 < p.2}) :
    Gam R w (.inr p) (.inr q) = (1 / 2) *
      (sE (w + m - 2) p.1.1 q.1.1 * sE (w + m - 2) p.1.2 q.1.2 +
        sE (w + m - 2) p.1.1 q.1.2 * sE (w + m - 2) p.1.2 q.1.1) := by
  rw [Gam_formula ι w hw R hRt hRR]
  simp only [kF, uF, vF, sbf_ee, sE]
  ring

end

/-! ## Elementary bounds -/

lemma sE_bounds (a : ℝ) (ha : 0 ≤ a) {m : ℕ} (i k : Fin m) :
    1 ≤ sE a i k ∧ sE a i k ≤ a + 1 := by
  unfold sE; split_ifs <;> constructor <;> linarith

lemma tE_abs (a : ℝ) {m : ℕ} (hm : (1:ℝ) ≤ m) (ha : 0 ≤ a) (ha2 : a ≤ 2 * m - 2) (i k : Fin m) :
    tE a i k ^ 2 ≤ 9 * (m : ℝ) ^ 2 := by
  unfold tE
  have h : ∀ D : ℝ, (D = 0 ∨ D = 1) → (a * (2 * D - 1) + (2 - m)) ^ 2 ≤ 9 * (m : ℝ) ^ 2 := by
    rintro D (rfl | rfl) <;> nlinarith
  apply h; split_ifs <;> simp

lemma sum_sE_sq (a : ℝ) {m : ℕ} (k : Fin m) :
    ∑ i, sE a i k ^ 2 = a ^ 2 + 2 * a + m := by
  have e : ∀ i, sE a i k ^ 2 = (a ^ 2 + 2 * a) * (if i = k then 1 else 0) + 1 := by
    intro i; unfold sE; split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma sum_sE_sq' (a : ℝ) {m : ℕ} (i : Fin m) :
    ∑ k, sE a i k ^ 2 = a ^ 2 + 2 * a + m := by
  have e : ∀ k, sE a i k ^ 2 = (a ^ 2 + 2 * a) * (if i = k then 1 else 0) + 1 := by
    intro k; unfold sE; split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma sum_lt_le {m : ℕ} (f : Fin m → Fin m → ℝ) (hf : ∀ i j, 0 ≤ f i j) :
    ∑ q : {p : Fin m × Fin m // p.1 < p.2}, f q.1.1 q.1.2 ≤ ∑ i, ∑ j, f i j := by
  have h1 : ∑ q : {p : Fin m × Fin m // p.1 < p.2}, f q.1.1 q.1.2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2), f p.1 p.2 :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2))
      (by intro x; simp) (fun p => f p.1 p.2)).symm
  rw [h1, ← Fintype.sum_prod_type']
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => hf p.1 p.2)

lemma sum_lt_const {m : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    ∑ _q : {p : Fin m × Fin m // p.1 < p.2}, c ≤ (m : ℝ) ^ 2 * c := by
  calc ∑ _q : {p : Fin m × Fin m // p.1 < p.2}, c
      = ∑ q : {p : Fin m × Fin m // p.1 < p.2}, (fun (_ _ : Fin m) => c) q.1.1 q.1.2 := rfl
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, c := sum_lt_le _ (fun _ _ => hc)
    _ = _ := by simp; ring

lemma E1_le (a m w : ℝ) (hm : 1 ≤ m) (hw : 1 ≤ w) (hwm : w ≤ m) (ha : a = w + m - 2) :
    0 ≤ E1 a m ∧ E1 a m ≤ 4 * m ^ 3 := by
  subst ha
  unfold E1
  have h1 : 0 ≤ w + m - 2 := by linarith
  have h2 : (2 - m) ^ 2 ≤ m ^ 2 := by nlinarith
  have h3 : (w + m - 2) * m ≤ 2 * m ^ 2 := by nlinarith
  have h4 : 0 ≤ (w + m - 2) * m + (2 - m) ^ 2 := by positivity
  have h5 : (w + m - 2 + 1) * ((w + m - 2) * m + (2 - m) ^ 2) ≤ 2 * m * (3 * m ^ 2) := by
    apply mul_le_mul (by linarith) (by linarith) h4 (by linarith)
  have h6 : (w + m - 2 + 2 - m) ^ 2 ≤ m ^ 3 := by
    have : w + m - 2 + 2 - m = w := by ring
    rw [this]; nlinarith
  constructor
  · have : 0 ≤ (w + m - 2 + 1) * ((w + m - 2) * m + (2 - m) ^ 2) := by positivity
    positivity
  · nlinarith

lemma E0_sq (a m w : ℝ) (hm : 1 ≤ m) (hw : 1 ≤ w) (hwm : w ≤ m) (ha : a = w + m - 2) :
    E0 a m ^ 2 ≤ 100 * m ^ 4 := by
  subst ha
  unfold E0
  have h1 : |(w + m - 2) * (m - 4)| ≤ 10 * m ^ 2 := by
    rw [abs_mul]
    have : |w + m - 2| ≤ 2 * m := by rw [abs_le]; constructor <;> linarith
    have h' : |m - 4| ≤ 5 * m := by rw [abs_le]; constructor <;> linarith
    calc |w + m - 2| * |m - 4| ≤ (2 * m) * (5 * m) :=
          mul_le_mul this h' (abs_nonneg _) (by linarith)
      _ = _ := by ring
  have h2 : (2 - m) ^ 2 ≤ m ^ 2 := by nlinarith
  have h3 : (w + m - 2 + m - 2) ^ 2 ≤ 9 * m ^ 2 := by nlinarith
  have hb : |(1 / 2) * ((w + m - 2) * (m - 4) + (2 - m) ^ 2 + (w + m - 2 + m - 2) ^ 2)| ≤ 10 * m ^ 2 := by
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith [sq_nonneg (2 - m), sq_nonneg (w + m - 2 + m - 2)]
  have := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  nlinarith

end HigherOrderId.Certify.Dev.B4
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.B4
open HigherOrderId.Certify

section
variable {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hm : (1:ℝ) ≤ m) (hw1 : 1 ≤ w)
  (hwm : w ≤ m) (R : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (hRR : R * R = Sw ι w)
include hm hw1 hwm hRt hRR

lemma S_le : (w + m - 2) ^ 2 + 2 * (w + m - 2) + m ≤ 9 * (m : ℝ) ^ 2 := by nlinarith

lemma tr_Gam_le : (Gam R w).trace ≤ 8 * (m : ℝ) ^ 4 := by
  have hw0 : (0:ℝ) ≤ w := by linarith
  have ha0 : 0 ≤ w + m - 2 := by linarith
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  have h1 : ∀ i : Fin m, Gam R w (.inl i) (.inl i) ≤ 4 * (m : ℝ) ^ 3 := by
    intro i
    rw [Gam_ll ι w hw0 R hRt hRR, if_pos rfl]
    obtain ⟨e0, e1⟩ := E1_le (w + m - 2) m w hm hw1 hwm rfl
    have : E1 (w + m - 2) m / w ^ 2 ≤ E1 (w + m - 2) m :=
      div_le_self e0 (by nlinarith)
    linarith
  have h2 : ∀ p : {p : Fin m × Fin m // p.1 < p.2}, Gam R w (.inr p) (.inr p) ≤ 4 * (m : ℝ) ^ 2 := by
    intro p
    rw [Gam_rr ι w hw0 R hRt hRR]
    have b := fun i k => sE_bounds (w + m - 2) ha0 (m := m) i k
    have q1 := b p.1.1 p.1.1
    have q2 := b p.1.2 p.1.2
    have q3 := b p.1.1 p.1.2
    have q4 := b p.1.2 p.1.1
    have m1 : sE (w + m - 2) p.1.1 p.1.1 * sE (w + m - 2) p.1.2 p.1.2 ≤ (2 * m) * (2 * m) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have m2 : sE (w + m - 2) p.1.1 p.1.2 * sE (w + m - 2) p.1.2 p.1.1 ≤ (2 * m) * (2 * m) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    nlinarith
  have s1 : ∑ i : Fin m, Gam R w (.inl i) (.inl i) ≤ m * (4 * (m : ℝ) ^ 3) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
    simpa using this
  have s2 : ∑ p : {p : Fin m × Fin m // p.1 < p.2}, Gam R w (.inr p) (.inr p) ≤
      (m : ℝ) ^ 2 * (4 * (m : ℝ) ^ 2) :=
    (Finset.sum_le_sum (fun p _ => h2 p)).trans (sum_lt_const _ (by positivity))
  nlinarith

lemma sum_ll : ∑ i : Fin m, ∑ j : Fin m, Gam R w (.inl i) (.inl j) ^ 2 ≤
    (16 * (m : ℝ) ^ 7 + 100 * (m : ℝ) ^ 6) / w ^ 4 := by
  have hw0 : (0:ℝ) ≤ w := by linarith
  have hpt : ∀ i j : Fin m, Gam R w (.inl i) (.inl j) ^ 2 ≤
      (16 * (m : ℝ) ^ 6 * (if i = j then 1 else 0) + 100 * (m : ℝ) ^ 4) / w ^ 4 := by
    intro i j
    rw [Gam_ll ι w hw0 R hRt hRR, div_pow, ← pow_mul]
    apply div_le_div_of_nonneg_right _ (by positivity)
    split_ifs
    · obtain ⟨e0, e1⟩ := E1_le (w + m - 2) m w hm hw1 hwm rfl
      have : E1 (w + m - 2) m ^ 2 ≤ (4 * m ^ 3) ^ 2 := pow_le_pow_left₀ e0 e1 2
      nlinarith
    · have := E0_sq (w + m - 2) m w hm hw1 hwm rfl
      linarith
  calc ∑ i : Fin m, ∑ j : Fin m, Gam R w (.inl i) (.inl j) ^ 2
      ≤ ∑ i : Fin m, ∑ j : Fin m,
          (16 * (m : ℝ) ^ 6 * (if i = j then 1 else 0) + 100 * (m : ℝ) ^ 4) / w ^ 4 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
    _ = _ := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
          Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
        ring

lemma sum_lr : ∑ i : Fin m, ∑ q : {p : Fin m × Fin m // p.1 < p.2},
    Gam R w (.inl i) (.inr q) ^ 2 ≤ 81 * (m : ℝ) ^ 6 := by
  have hw0 : (0:ℝ) ≤ w := by linarith
  have ha0 : 0 ≤ w + m - 2 := by linarith
  have ha2 : w + m - 2 ≤ 2 * m - 2 := by linarith
  set a := w + m - 2 with ha
  have hpt : ∀ (i : Fin m) (q : {p : Fin m × Fin m // p.1 < p.2}),
      Gam R w (.inl i) (.inr q) ^ 2 ≤
        (9 * (m : ℝ) ^ 2 / 2) * (sE a i q.1.1 ^ 2 + sE a i q.1.2 ^ 2) := by
    intro i q
    rw [Gam_lr ι w hw0 R hRt hRR]
    have t1 := tE_abs a hm ha0 ha2 i q.1.1
    have t2 := tE_abs a hm ha0 ha2 i q.1.2
    have hwi : 0 < w⁻¹ := by positivity
    have hwi1 : w⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hw1
    set x := sE a i q.1.1 * tE a i q.1.2 + sE a i q.1.2 * tE a i q.1.1
    have hx : x ^ 2 ≤ 2 * (sE a i q.1.1 ^ 2 * tE a i q.1.2 ^ 2 + sE a i q.1.2 ^ 2 * tE a i q.1.1 ^ 2) := by
      nlinarith [sq_nonneg (sE a i q.1.1 * tE a i q.1.2 - sE a i q.1.2 * tE a i q.1.1)]
    have hy : sE a i q.1.1 ^ 2 * tE a i q.1.2 ^ 2 + sE a i q.1.2 ^ 2 * tE a i q.1.1 ^ 2 ≤
        sE a i q.1.1 ^ 2 * (9 * m ^ 2) + sE a i q.1.2 ^ 2 * (9 * m ^ 2) := by
      have := sq_nonneg (sE a i q.1.1); have := sq_nonneg (sE a i q.1.2)
      nlinarith
    have hw2 : (w⁻¹) ^ 2 ≤ 1 := by nlinarith
    calc (w⁻¹ * ((1 / 2) * x)) ^ 2 = (w⁻¹) ^ 2 * (x ^ 2 / 4) := by ring
      _ ≤ 1 * (x ^ 2 / 4) := mul_le_mul_of_nonneg_right hw2 (by positivity)
      _ ≤ _ := by nlinarith
  have hq : ∀ q : {p : Fin m × Fin m // p.1 < p.2},
      ∑ i : Fin m, Gam R w (.inl i) (.inr q) ^ 2 ≤ 81 * (m : ℝ) ^ 4 := by
    intro q
    calc ∑ i : Fin m, Gam R w (.inl i) (.inr q) ^ 2
        ≤ ∑ i : Fin m, (9 * (m : ℝ) ^ 2 / 2) * (sE a i q.1.1 ^ 2 + sE a i q.1.2 ^ 2) :=
          Finset.sum_le_sum (fun i _ => hpt i q)
      _ = (9 * (m : ℝ) ^ 2 / 2) * ((a ^ 2 + 2 * a + m) + (a ^ 2 + 2 * a + m)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_sE_sq, sum_sE_sq]
      _ ≤ _ := by
          have := S_le ι w hm hw1 hwm R hRt hRR
          nlinarith
  rw [Finset.sum_comm]
  calc ∑ q : {p : Fin m × Fin m // p.1 < p.2}, ∑ i : Fin m, Gam R w (.inl i) (.inr q) ^ 2
      ≤ ∑ _q : {p : Fin m × Fin m // p.1 < p.2}, 81 * (m : ℝ) ^ 4 := Finset.sum_le_sum (fun q _ => hq q)
    _ ≤ (m : ℝ) ^ 2 * (81 * (m : ℝ) ^ 4) := sum_lt_const _ (by positivity)
    _ = _ := by ring

lemma sum_rr : ∑ p : {p : Fin m × Fin m // p.1 < p.2}, ∑ q : {p : Fin m × Fin m // p.1 < p.2},
    Gam R w (.inr p) (.inr q) ^ 2 ≤ 81 * (m : ℝ) ^ 6 := by
  have hw0 : (0:ℝ) ≤ w := by linarith
  set a := w + m - 2 with ha
  have hp : ∀ p : {p : Fin m × Fin m // p.1 < p.2},
      ∑ q : {p : Fin m × Fin m // p.1 < p.2}, Gam R w (.inr p) (.inr q) ^ 2 ≤ 81 * (m : ℝ) ^ 4 := by
    intro p
    have hpt : ∀ q : {p : Fin m × Fin m // p.1 < p.2}, Gam R w (.inr p) (.inr q) ^ 2 ≤
        (fun k l => (1 / 2) * (sE a p.1.1 k ^ 2 * sE a p.1.2 l ^ 2 +
          sE a p.1.1 l ^ 2 * sE a p.1.2 k ^ 2)) q.1.1 q.1.2 := by
      intro q
      rw [Gam_rr ι w hw0 R hRt hRR]
      simp only
      nlinarith [sq_nonneg (sE a p.1.1 q.1.1 * sE a p.1.2 q.1.2 - sE a p.1.1 q.1.2 * sE a p.1.2 q.1.1)]
    calc ∑ q : {p : Fin m × Fin m // p.1 < p.2}, Gam R w (.inr p) (.inr q) ^ 2
        ≤ ∑ q : {p : Fin m × Fin m // p.1 < p.2},
            (fun k l => (1 / 2) * (sE a p.1.1 k ^ 2 * sE a p.1.2 l ^ 2 +
              sE a p.1.1 l ^ 2 * sE a p.1.2 k ^ 2)) q.1.1 q.1.2 :=
          Finset.sum_le_sum (fun q _ => hpt q)
      _ ≤ ∑ k : Fin m, ∑ l : Fin m, (1 / 2) * (sE a p.1.1 k ^ 2 * sE a p.1.2 l ^ 2 +
              sE a p.1.1 l ^ 2 * sE a p.1.2 k ^ 2) :=
          sum_lt_le (fun k l => (1 / 2) * (sE a p.1.1 k ^ 2 * sE a p.1.2 l ^ 2 +
              sE a p.1.1 l ^ 2 * sE a p.1.2 k ^ 2)) (fun k l => by positivity)
      _ = (a ^ 2 + 2 * a + m) ^ 2 := by
          have e1 : ∑ k : Fin m, ∑ l : Fin m, sE a p.1.1 k ^ 2 * sE a p.1.2 l ^ 2 =
              (a ^ 2 + 2 * a + m) ^ 2 := by
            rw [← Finset.sum_mul_sum, sum_sE_sq', sum_sE_sq']; ring
          have e2 : ∑ k : Fin m, ∑ l : Fin m, sE a p.1.1 l ^ 2 * sE a p.1.2 k ^ 2 =
              (a ^ 2 + 2 * a + m) ^ 2 := by
            simp only [mul_comm (sE a p.1.1 _ ^ 2)]
            rw [← Finset.sum_mul_sum, sum_sE_sq', sum_sE_sq']; ring
          have e3 : ∀ k : Fin m, ∑ l : Fin m, (1 / 2) * (sE a p.1.1 k ^ 2 * sE a p.1.2 l ^ 2 +
              sE a p.1.1 l ^ 2 * sE a p.1.2 k ^ 2) =
              (1 / 2) * ∑ l : Fin m, sE a p.1.1 k ^ 2 * sE a p.1.2 l ^ 2 +
                (1 / 2) * ∑ l : Fin m, sE a p.1.1 l ^ 2 * sE a p.1.2 k ^ 2 := by
            intro k; rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
          rw [Finset.sum_congr rfl (fun k _ => e3 k), Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, e1, e2]; ring
      _ ≤ _ := by
          have h0 : 0 ≤ a ^ 2 + 2 * a + m := by
            have : 0 ≤ a := by rw [ha]; linarith
            positivity
          have := S_le ι w hm hw1 hwm R hRt hRR
          rw [← ha] at this
          nlinarith
  calc _ ≤ ∑ _p : {p : Fin m × Fin m // p.1 < p.2}, 81 * (m : ℝ) ^ 4 :=
        Finset.sum_le_sum (fun p _ => hp p)
    _ ≤ (m : ℝ) ^ 2 * (81 * (m : ℝ) ^ 4) := sum_lt_const _ (by positivity)
    _ = _ := by ring

lemma trGam2_le : (Gam R w * Gam R w).trace ≤ 343 * ((m : ℝ) ^ 6 + (m : ℝ) ^ 7 / w ^ 4) := by
  have hsplit : (Gam R w * Gam R w).trace =
      ∑ i : Fin m, ∑ j : Fin m, Gam R w (.inl i) (.inl j) ^ 2 +
      2 * ∑ i : Fin m, ∑ q : {p : Fin m × Fin m // p.1 < p.2}, Gam R w (.inl i) (.inr q) ^ 2 +
      ∑ p : {p : Fin m × Fin m // p.1 < p.2}, ∑ q : {p : Fin m × Fin m // p.1 < p.2},
        Gam R w (.inr p) (.inr q) ^ 2 := by
    have e : (Gam R w * Gam R w).trace = ∑ r, ∑ s, Gam R w r s ^ 2 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _
      rw [Gam_symm R w s r, sq]
    rw [e]
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
    have e2 : ∑ p : {p : Fin m × Fin m // p.1 < p.2}, ∑ j : Fin m, Gam R w (.inr p) (.inl j) ^ 2 =
        ∑ i : Fin m, ∑ q : {p : Fin m × Fin m // p.1 < p.2}, Gam R w (.inl i) (.inr q) ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro q _
      rw [Gam_symm]
    rw [e2]; ring
  rw [hsplit]
  have h1 := sum_ll ι w hm hw1 hwm R hRt hRR
  have h2 := sum_lr ι w hm hw1 hwm R hRt hRR
  have h3 := sum_rr ι w hm hw1 hwm R hRt hRR
  have hw4 : 1 ≤ w ^ 4 := one_le_pow₀ hw1
  have h6 : 100 * (m : ℝ) ^ 6 / w ^ 4 ≤ 100 * (m : ℝ) ^ 6 := div_le_self (by positivity) hw4
  have e : (16 * (m : ℝ) ^ 7 + 100 * (m : ℝ) ^ 6) / w ^ 4 =
      16 * ((m : ℝ) ^ 7 / w ^ 4) + 100 * (m : ℝ) ^ 6 / w ^ 4 := by ring
  have h7 : 0 ≤ (m : ℝ) ^ 7 / w ^ 4 := by positivity
  have h8 : 0 ≤ (m : ℝ) ^ 6 := by positivity
  nlinarith

end

end HigherOrderId.Certify.Dev.B4
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.B4
open HigherOrderId.Certify

/-- the centring projection `P = I - J/m` -/
noncomputable def Pc (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i k => (if i = k then 1 else 0) - 1 / (m : ℝ)

lemma Pc_symm (m : ℕ) (i k : Fin m) : Pc m i k = Pc m k i := by
  unfold Pc; by_cases h : i = k
  · subst h; rfl
  · simp [h, Ne.symm h]

lemma Pc_colsum {m : ℕ} (hm : 1 ≤ m) (k : Fin m) : ∑ i, Pc m i k = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Pc, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp; ring

lemma Pc_mul {m : ℕ} (hm : 1 ≤ m) : Pc m * Pc m = Pc m := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  ext k l
  have e : ∀ j, Pc m k j * Pc m j l = (if k = j then 1 else 0) * Pc m j l - (1 / m) * Pc m j l := by
    intro j; unfold Pc; ring
  simp only [Matrix.mul_apply, e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h2 : ∑ j, Pc m j l = 0 := Pc_colsum hm l
  rw [h2]
  simp [ite_mul, Finset.sum_ite_eq]

lemma Pc_trace {m : ℕ} (hm : 1 ≤ m) : (Pc m).trace = (m : ℝ) - 1 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Matrix.trace, Matrix.diag, Pc, if_true, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma Pc_t {m : ℕ} : (Pc m)ᵀ = Pc m := by
  ext i k; simp only [Matrix.transpose_apply]; exact Pc_symm m k i

/-- the test family `E = (w P ; 0)` on the frame rows -/
noncomputable def Ef (m : ℕ) (w : ℝ) : Matrix (FrameRows m) (Fin m) ℝ :=
  Matrix.fromRows (w • Pc m) (0 : Matrix {p : Fin m × Fin m // p.1 < p.2} (Fin m) ℝ)

lemma Ef_mul_P {m : ℕ} (hm : 1 ≤ m) (w : ℝ) : Ef m w * Pc m = Ef m w := by
  unfold Ef
  rw [Matrix.fromRows_mul, Matrix.smul_mul, Pc_mul hm, Matrix.zero_mul]

lemma EtE {m : ℕ} (hm : 1 ≤ m) (w : ℝ) : (Ef m w)ᵀ * Ef m w = (w ^ 2) • Pc m := by
  unfold Ef
  rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, Matrix.transpose_zero,
    Matrix.zero_mul, add_zero, Matrix.transpose_smul, Pc_t, Matrix.smul_mul, Matrix.mul_smul,
    Pc_mul hm, smul_smul, sq]

lemma EtGE {d m : ℕ} (hm : 1 ≤ m) (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w)
    (R : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (hRR : R * R = Sw ι w) :
    (Ef m w)ᵀ * Gam R w * Ef m w =
      (E1 (w + m - 2) m - E0 (w + m - 2) m) • Pc m := by
  set γ := E1 (w + m - 2) m - E0 (w + m - 2) m
  set c0 := E0 (w + m - 2) m
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, Ef,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero, Matrix.smul_apply, smul_eq_mul]
  have key : ∀ i j : Fin m, w * Pc m i k * Gam R w (.inl i) (.inl j) * (w * Pc m j l) =
      γ * ((if i = j then 1 else 0) * Pc m i k * Pc m j l) + c0 * (Pc m i k * Pc m j l) := by
    intro i j
    rw [Gam_ll ι w hw.le R hRt hRR]
    have : w ≠ 0 := hw.ne'
    split_ifs <;> field_simp <;> ring
  simp only [Finset.sum_mul, key, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ j : Fin m, ∑ i : Fin m, (if i = j then 1 else 0) * Pc m i k * Pc m j l =
      Pc m k l := by
    have : ∀ j : Fin m, ∑ i : Fin m, (if i = j then 1 else 0) * Pc m i k * Pc m j l =
        Pc m k j * Pc m j l := by
      intro j; simp [ite_mul, Finset.sum_ite_eq', Pc_symm m j k]
    simp only [this]
    have := congrFun (congrFun (Pc_mul hm) k) l
    simpa [Matrix.mul_apply] using this
  have h2 : ∑ j : Fin m, ∑ i : Fin m, Pc m i k * Pc m j l = 0 := by
    simp only [← Finset.sum_mul, Pc_colsum hm, zero_mul, Finset.sum_const_zero]
  rw [h1, h2]; ring

lemma gamma_eq (a m : ℝ) : E1 a m - E0 a m = a ^ 2 * m / 2 + a * (m - 4) ^ 2 / 2 := by
  unfold E1 E0; ring

/-- the lower bound `Σ λ⁻² ≥ m⁷/(128 w⁴)` for `m ≥ 2`. -/
lemma low_frame {d m : ℕ} (hm2 : 2 ≤ m) (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw1 : 1 ≤ w)
    (R Ri : Matrix (Fin m) (Fin m) ℝ) (hRt : Rᵀ = R) (hRR : R * R = Sw ι w)
    (hRit : Riᵀ = Ri) (hRiR : Ri * R = 1) (hRRi : R * Ri = 1) (hU : Uw ι w = Gw ι w * Ri)
    (W : Matrix (SymIdx m) (SymIdx m) ℝ) (hW2 : W * Wᵀ = 1) (lam : SymIdx m → ℝ)
    (hlam : ∀ j, 0 < lam j)
    (hM : (DUmat (Uw ι w))ᵀ * DUmat (Uw ι w) = W * diagonal lam * Wᵀ) :
    (m : ℝ) ^ 7 / (128 * w ^ 4) ≤ ∑ j, (lam j)⁻¹ ^ 2 := by
  have hm1 : 1 ≤ m := by omega
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hw : 0 < w := by linarith
  set γ := E1 (w + m - 2) m - E0 (w + m - 2) m with hγ
  have ha : (m : ℝ) - 1 ≤ w + m - 2 := by linarith
  have hγlow : ((m : ℝ) - 1) ^ 2 * m / 2 ≤ γ := by
    rw [hγ, gamma_eq]
    have h1 : ((m : ℝ) - 1) ^ 2 ≤ (w + m - 2) ^ 2 := by nlinarith
    have h2 : 0 ≤ (w + m - 2) * ((m : ℝ) - 4) ^ 2 / 2 := by
      have : 0 ≤ w + m - 2 := by linarith
      positivity
    nlinarith
  have hγpos : 0 < γ := by
    have : 0 < ((m : ℝ) - 1) ^ 2 * m / 2 := by
      have : 0 < (m : ℝ) - 1 := by linarith
      positivity
    linarith
  set Y := Lfr R w * Ef m w with hY
  have hG : Yᵀ * Y = γ • Pc m := by
    rw [hY, Matrix.transpose_mul]
    calc (Ef m w)ᵀ * (Lfr R w)ᵀ * (Lfr R w * Ef m w)
        = (Ef m w)ᵀ * ((Lfr R w)ᵀ * Lfr R w) * Ef m w := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [LtL_eq R hRt, EtGE hm1 ι w hw R hRt hRR]
  have hYP : Y * Pc m = Y := by rw [hY, Matrix.mul_assoc, Ef_mul_P hm1]
  have hH : Yᵀ * (W * diagonal lam * Wᵀ) * Y = (w ^ 2) • Pc m := by
    rw [← hM]
    have hAY : DUmat (Uw ι w) * Y = Pio ι * Ef m w := by
      rw [hY, ← Matrix.mul_assoc, A_Lfr ι w hw R Ri hRt hRit hRiR hRRi hU]
    calc Yᵀ * ((DUmat (Uw ι w))ᵀ * DUmat (Uw ι w)) * Y
        = (DUmat (Uw ι w) * Y)ᵀ * (DUmat (Uw ι w) * Y) := by
          rw [Matrix.transpose_mul (DUmat (Uw ι w)) Y]; simp only [Matrix.mul_assoc]
      _ = (Ef m w)ᵀ * ((Pio ι)ᵀ * Pio ι) * Ef m w := by
          rw [hAY, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Pio_tt, Matrix.mul_one, EtE hm1]
  have htr : 0 < (Pc m).trace := by rw [Pc_trace hm1]; linarith
  have key := low_gen W hW2 lam hlam Y (Pc m) γ (w ^ 2) hγpos (by positivity) hG hYP hH htr
  rw [Pc_trace hm1] at key
  refine le_trans ?_ key
  -- (m-1) γ² / w⁴ ≥ m⁷/(128 w⁴)
  have hw4 : 0 < w ^ 4 := by positivity
  rw [show (w ^ 2) ^ 2 = w ^ 4 by ring, div_le_div_iff₀ (by positivity) hw4]
  have hm1' : (m : ℝ) / 2 ≤ (m : ℝ) - 1 := by linarith
  have hγ2 : (((m : ℝ) - 1) ^ 2 * m / 2) ^ 2 ≤ γ ^ 2 :=
    pow_le_pow_left₀ (by have : 0 ≤ (m:ℝ) - 1 := by linarith
                         positivity) hγlow 2
  have hp : ((m : ℝ) / 2) ^ 5 ≤ ((m : ℝ) - 1) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hm1' 5
  have e : ((m : ℝ) - 1) * (((m : ℝ) - 1) ^ 2 * m / 2) ^ 2 = ((m : ℝ) - 1) ^ 5 * m ^ 2 / 4 := by
    ring
  have h3 : (m : ℝ) ^ 7 / 128 ≤ ((m : ℝ) - 1) * γ ^ 2 := by
    have h4 : ((m : ℝ) - 1) * (((m : ℝ) - 1) ^ 2 * m / 2) ^ 2 ≤ ((m : ℝ) - 1) * γ ^ 2 :=
      mul_le_mul_of_nonneg_left hγ2 (by linarith)
    rw [e] at h4
    have h5 : ((m : ℝ) / 2) ^ 5 * m ^ 2 / 4 ≤ ((m : ℝ) - 1) ^ 5 * m ^ 2 / 4 := by
      have : (0:ℝ) ≤ (m : ℝ) ^ 2 / 4 := by positivity
      nlinarith
    have e2 : ((m : ℝ) / 2) ^ 5 * m ^ 2 / 4 = (m : ℝ) ^ 7 / 128 := by ring
    linarith
  nlinarith

end HigherOrderId.Certify.Dev.B4
end

section
set_option autoImplicit false
open Matrix
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.B4
open HigherOrderId.Certify

lemma UtU {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (R Ri : Matrix (Fin m) (Fin m) ℝ)
    (hRR : R * R = Sw ι w) (hRit : Riᵀ = Ri) (hRiR : Ri * R = 1) (hRRi : R * Ri = 1)
    (hU : Uw ι w = Gw ι w * Ri) : (Uw ι w)ᵀ * Uw ι w = 1 := by
  rw [hU, Matrix.transpose_mul, hRit]
  calc Ri * (Gw ι w)ᵀ * (Gw ι w * Ri) = Ri * Sw ι w * Ri := by
        rw [Sw]; simp only [Matrix.mul_assoc]
    _ = (Ri * R) * (R * Ri) := by rw [← hRR]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hRiR, hRRi, Matrix.one_mul]

lemma inv_sqrt_pow2 (x : ℝ) (hx : 0 < x) : (Real.sqrt x)⁻¹ ^ 2 = x⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hx.le]

lemma inv_sqrt_pow4 (x : ℝ) (hx : 0 < x) : (Real.sqrt x)⁻¹ ^ 4 = x⁻¹ ^ 2 := by
  rw [show (4:ℕ) = 2 * 2 by rfl, pow_mul, inv_sqrt_pow2 x hx]

end HigherOrderId.Certify.Dev.B4

namespace HigherOrderId.Certify
open HigherOrderId.Certify.Dev.B4 in
theorem chk_lemma_B_4 :
    ∃ c₁ C₁ c₂ C₂ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < c₂ ∧ 0 < C₂ ∧
      ∀ (d m : ℕ) (ι : FrameRows m ↪ Fin d) (w : ℝ), 10 ≤ d → 1 ≤ m → 1 ≤ w → w ≤ (m : ℝ) →
        FullColRank (Uw ι w) ∧
        c₁ * (m : ℝ) ^ 4 ≤ ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 2 ∧
        ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 2 ≤ C₁ * (m : ℝ) ^ 4 ∧
        c₂ * ((m : ℝ) ^ 6 + (m : ℝ) ^ 7 / w ^ 4) ≤ ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 4 ∧
        ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 4 ≤ C₂ * ((m : ℝ) ^ 6 + (m : ℝ) ^ 7 / w ^ 4) := by
  obtain ⟨c, hc, H⟩ := eq_82_83
  refine ⟨c, 8, min (c / 2) (1 / 256), 343, hc, by norm_num,
    lt_min (by linarith) (by norm_num), by norm_num, ?_⟩
  intro d m ι w hd hm hw1 hwm
  have hw0 : 0 < w := by linarith
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hF := Dev.B2.fullColRank_Uw ι w hw0
  obtain ⟨Ri, hRit, hRRi, hRiR, hRt, hU⟩ := Dev.B2.sqrtS_props ι w hw0
  have hRR := sqrt_mul_self_Sw ι w
  generalize CFC.sqrt (Sw ι w) = R at hRRi hRiR hRt hRR
  have hUU := UtU ι w R Ri hRR hRit hRiR hRRi hU
  obtain ⟨-, -, H3⟩ := H d m (Uw ι w) hd hUU
  obtain ⟨-, h2a, h2b, h4a, h4b⟩ := H3 hm hF
  obtain ⟨W, lam, hW1, hW2, hM, hlam⟩ := Dev.B5.G_spec (Uw ι w) hF
  have e2 : ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 2 = ∑ j, (lam j)⁻¹ := by
    apply Finset.sum_congr rfl; intro j _
    rw [(hlam j).2, inv_sqrt_pow2 _ (hlam j).1]
  have e4 : ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 4 = ∑ j, (lam j)⁻¹ ^ 2 := by
    apply Finset.sum_congr rfl; intro j _
    rw [(hlam j).2, inv_sqrt_pow4 _ (hlam j).1]
  obtain ⟨u1, u2⟩ := up_gen (DUmat (Uw ι w)) (Lfr R w * (Pio ι)ᵀ)
    (Lfr_left ι w hw0 R Ri hRt hRit hRiR hRRi hU) W hW1 hW2 lam (fun j => (hlam j).1) hM
  rw [LLt_eq, tr_LLt R hRt] at u1
  rw [LLt_eq, tr_LLt2 R hRt] at u2
  have t1 := tr_Gam_le ι w hmR hw1 hwm R hRt hRR
  have t2 := trGam2_le ι w hmR hw1 hwm R hRt hRR
  refine ⟨hF, by linarith, by rw [e2]; linarith, ?_, by rw [e4]; linarith⟩
  -- lower bound for the fourth inverse moment
  have hX : c * (m : ℝ) ^ 6 ≤ ∑ j, (singVals (Uw ι w) j)⁻¹ ^ 4 := h4b.trans h4a
  rw [e4] at hX ⊢
  set X := ∑ j, (lam j)⁻¹ ^ 2
  have hc2 : min (c / 2) (1 / 256) ≤ c / 2 := min_le_left _ _
  have hc3 : min (c / 2) (1 / 256) ≤ 1 / 256 := min_le_right _ _
  have hc0 : 0 < min (c / 2) (1 / 256) := lt_min (by linarith) (by norm_num)
  have hm6 : (0:ℝ) ≤ (m : ℝ) ^ 6 := by positivity
  have hm7 : (0:ℝ) ≤ (m : ℝ) ^ 7 / w ^ 4 := by positivity
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · have hm1' : m = 1 := by omega
    subst hm1'
    have hw : w = 1 := le_antisymm (by simpa using hwm) hw1
    subst hw
    norm_num at hX ⊢
    nlinarith
  · have hL := low_frame hm2 ι w hw1 R Ri hRt hRR hRit hRiR hRRi hU W hW2 lam
      (fun j => (hlam j).1) hM
    have e : (m : ℝ) ^ 7 / (128 * w ^ 4) = ((m : ℝ) ^ 7 / w ^ 4) / 128 := by
      rw [div_div, mul_comm]
    rw [e] at hL
    have a1 : min (c / 2) (1 / 256) * (m : ℝ) ^ 6 ≤ (c / 2) * (m : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_right hc2 hm6
    have a2 : min (c / 2) (1 / 256) * ((m : ℝ) ^ 7 / w ^ 4) ≤ (1 / 256) * ((m : ℝ) ^ 7 / w ^ 4) :=
      mul_le_mul_of_nonneg_right hc3 hm7
    nlinarith
end HigherOrderId.Certify
end

theorem solution : type_of% @HigherOrderId.Certify.chk_lemma_B_4 := @HigherOrderId.Certify.chk_lemma_B_4
