-- Prove2me | solution 1 for HigherOrderId.Certify.lemma_B_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:16:34.42076+00:00
-- url     : https://prove2.me/submissions/3cc16906-f2b2-4b38-9d47-eff36e16d5ed

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion
import Definitions.Def_HigherOrderId_Certify_TallCompletion

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

lemma Bc_ne {m : ℕ} (c : SymIdx m → ℝ) (hc : c ≠ 0) : Bc c ≠ 0 := by
  intro h
  apply hc; funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa [Bc, p.2] using this

end HigherOrderId.Certify.Dev.B2

namespace HigherOrderId.Certify

end HigherOrderId.Certify
end

section
open Matrix

namespace HigherOrderId.Certify.Dev.Nuc

variable {d : ℕ} {T : Type*} [Fintype T] [DecidableEq T]

end HigherOrderId.Certify.Dev.Nuc
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

lemma frobInner_eq_trace {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobInner X Y = (Xᵀ * Y).trace := by
  simp only [frobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

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

/-- unitary-conjugated inner products -/
lemma frobInner_conj {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hU : Uᵀ * U = 1)
    (B B' : Matrix (Fin m) (Fin m) ℝ) :
    frobInner (U * B * Uᵀ) (U * B' * Uᵀ) = frobInner B B' := by
  rw [frobInner_eq_trace, frobInner_eq_trace]
  have : (U * B * Uᵀ)ᵀ * (U * B' * Uᵀ) = U * (Bᵀ * B') * Uᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]

lemma frobInner_conj_rest {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (X : Matrix (Fin d) (Fin d) ℝ) (hX : Uᵀ * X * U = 0) :
    frobInner (U * B * Uᵀ) X = 0 := by
  rw [frobInner_eq_trace]
  have : (U * B * Uᵀ)ᵀ * X = U * (Bᵀ * (Uᵀ * X)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm]
  have h2 : Bᵀ * (Uᵀ * X) * U = Bᵀ * (Uᵀ * X * U) := by simp only [Matrix.mul_assoc]
  rw [h2, hX]; simp


lemma frobInner_sub_left {n : ℕ} (X Y Z : Matrix (Fin n) (Fin n) ℝ) :
    frobInner (X - Y) Z = frobInner X Z - frobInner Y Z := by
  simp only [frobInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

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

lemma inner_single {m : ℕ} (a b c d : Fin m) :
    frobInner (Matrix.single a b (1:ℝ)) (Matrix.single c d 1) = if a = c ∧ b = d then 1 else 0 := by
  simp [frobInner, Matrix.single_apply, ite_and]

lemma symBasis_inner {m : ℕ} (p q : SymIdx m) :
    frobInner (symBasis p) (symBasis q) = if p = q then 1 else 0 := by
  obtain ⟨⟨a, b⟩, hab⟩ := p
  obtain ⟨⟨a', b'⟩, hab'⟩ := q
  have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have h3 : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) * 2 = 1 := by
    field_simp; have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2); linarith
  have hab2 : a ≤ b := hab
  have hab2' : a' ≤ b' := hab'
  simp only [symBasis]
  by_cases h1 : a = b <;> by_cases h1' : a' = b'
  · subst h1; subst h1'
    simp only [if_true]
    simp only [inner_single]
    by_cases h : a = a' <;> simp [h, Subtype.ext_iff, Prod.ext_iff]
  · subst h1
    simp only [if_true, h1', if_false]
    simp only [frobInner_smul_right, frobInner_add_right, inner_single]
    have : ¬ (a = a') ∨ ¬ (a = b') := by
      by_contra hh; push Not at hh; exact h1' (hh.1.symm.trans hh.2)
    rcases this with h | h <;> simp [h, h1', Subtype.ext_iff, Prod.ext_iff]
  · subst h1'
    simp only [if_true, h1, if_false]
    simp only [frobInner_smul_left, frobInner_add_left, inner_single]
    have : ¬ (a = a') ∨ ¬ (b = a') := by
      by_contra hh; push Not at hh; exact h1 (hh.1.trans hh.2.symm)
    rcases this with h | h <;> simp [h, h1, Subtype.ext_iff, Prod.ext_iff]
  · have hlt : a < b := lt_of_le_of_ne hab2 h1
    have hlt' : a' < b' := lt_of_le_of_ne hab2' h1'
    simp only [h1, h1', if_false]
    simp only [frobInner_smul_right, frobInner_smul_left, frobInner_add_right, frobInner_add_left,
      inner_single]
    by_cases h : a = a' <;> by_cases h' : b = b'
    · subst h; subst h'
      simp [Subtype.ext_iff, Prod.ext_iff, h1]
      have h3' : (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹) = 1 := by
        field_simp; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      exact h3'
    · have : ¬ (a = a' ∧ b = b') := fun hh => h' hh.2
      have h5 : ¬ (a = b' ∧ b = a') := fun hh => by omega
      have h6 : ¬ (a = a' ∧ b = a') := fun hh => by omega
      have h7 : ¬ (a = b' ∧ b = b') := fun hh => by omega
      simp [Subtype.ext_iff, Prod.ext_iff, h, h', h5, h6, h7, this, h1, h1', Ne.symm h1, Ne.symm h1']
    · have : ¬ (a = a' ∧ b = b') := fun hh => h hh.1
      have h5 : ¬ (a = b' ∧ b = a') := fun hh => by omega
      have h6 : ¬ (a = a' ∧ b = a') := fun hh => by omega
      have h7 : ¬ (a = b' ∧ b = b') := fun hh => by omega
      simp [Subtype.ext_iff, Prod.ext_iff, h, h', h5, h6, h7, this, h1, h1', Ne.symm h1, Ne.symm h1']
    · have : ¬ (a = a' ∧ b = b') := fun hh => h hh.1
      have h5 : ¬ (a = b' ∧ b = a') := fun hh => by omega
      have h6 : ¬ (a = a' ∧ b = a') := fun hh => by omega
      have h7 : ¬ (a = b' ∧ b = b') := fun hh => by omega
      simp [Subtype.ext_iff, Prod.ext_iff, h, h', h5, h6, h7, this, h1, h1', Ne.symm h1, Ne.symm h1']
      all_goals (intro hh1 hh2; omega)


/-- dot product of columns -/
def cdot {d a b : ℕ} (X : Matrix (Fin d) (Fin a) ℝ) (Y : Matrix (Fin d) (Fin b) ℝ)
    (i : Fin a) (l : Fin b) : ℝ := ∑ r, X r i * Y r l

lemma cdot_eq {d a b : ℕ} (X : Matrix (Fin d) (Fin a) ℝ) (Y : Matrix (Fin d) (Fin b) ℝ)
    (i : Fin a) (l : Fin b) : cdot X Y i l = (Xᵀ * Y) i l := by
  simp [cdot, Matrix.mul_apply, Matrix.transpose_apply]

lemma inner_cos {d a b a' b' : ℕ} (X : Matrix (Fin d) (Fin a) ℝ) (Y : Matrix (Fin d) (Fin b) ℝ)
    (X' : Matrix (Fin d) (Fin a') ℝ) (Y' : Matrix (Fin d) (Fin b') ℝ)
    (i : Fin a) (l : Fin b) (i' : Fin a') (l' : Fin b') :
    frobInner (colOuterSym X Y i l) (colOuterSym X' Y' i' l') =
      2 * (cdot X X' i i' * cdot Y Y' l l' + cdot X Y' i l' * cdot Y X' l i') := by
  unfold frobInner colOuterSym cdot
  have : ∀ r s, (X r i * Y s l + Y r l * X s i) * (X' r i' * Y' s l' + Y' r l' * X' s i') =
      (X r i * X' r i') * (Y s l * Y' s l') + (X r i * Y' r l') * (Y s l * X' s i') +
      (Y r l * X' r i') * (X s i * Y' s l') + (Y r l * Y' r l') * (X s i * X' s i') := by
    intros; ring
  simp_rw [this, Finset.sum_add_distrib, ← Finset.sum_mul_sum]
  have e1 : ∑ r, Y r l * X' r i' = ∑ r, X' r i' * Y r l := by simp [mul_comm]
  have e2 : ∑ r, X r i * Y' r l' = ∑ r, Y' r l' * X r i := by simp [mul_comm]
  have e3 : ∑ r, Y r l * X' r i' = ∑ r, X' r i' * Y r l := by simp [mul_comm]
  have e4 : ∑ r, Y r l * Y' r l' = ∑ r, Y r l * Y' r l' := rfl
  have e5 : ∑ r, X r i * X' r i' = ∑ r, X r i * X' r i' := rfl
  have e6 : ∑ r, X r i * Y' r l' = ∑ r, X r i * Y' r l' := rfl
  have e7 : ∑ s, X s i * Y' s l' = ∑ s, X s i * Y' s l' := rfl
  have e8 : ∑ s, Y s l * X' s i' = ∑ s, Y s l * X' s i' := rfl
  have e9 : ∑ r, Y r l * X' r i' = ∑ s, Y s l * X' s i' := rfl
  ring


noncomputable def kap {k : ℕ} (p : {p : Fin k × Fin k // p.1 ≤ p.2}) : ℝ :=
  if p.1.1 = p.1.2 then 1 / 2 else 1 / Real.sqrt 2

lemma restBasis_inr {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (p : {p : Fin k × Fin k // p.1 ≤ p.2}) :
    restBasis U V (Sum.inr p) = kap p • colOuterSym V V p.1.1 p.1.2 := by
  unfold restBasis kap
  by_cases h : p.1.1 = p.1.2
  · simp only [h, if_true]
    ext r s; simp [colOuterSym, h]; ring
  · simp [h]

lemma kap_sq {k : ℕ} (p q : {p : Fin k × Fin k // p.1 ≤ p.2}) :
    kap p * kap q * 2 * ((if p.1.1 = q.1.1 then 1 else 0) * (if p.1.2 = q.1.2 then 1 else 0) +
      (if p.1.1 = q.1.2 then 1 else 0) * (if p.1.2 = q.1.1 then 1 else 0)) =
      if p = q then 1 else 0 := by
  obtain ⟨⟨l, l'⟩, hl⟩ := p
  obtain ⟨⟨n, n'⟩, hn⟩ := q
  have hl2 : l ≤ l' := hl
  have hn2 : n ≤ n' := hn
  have h3 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = 1 := by
    field_simp; exact (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)).symm
  have hB : ((if l = n' then (1:ℝ) else 0) * (if l' = n then 1 else 0)) =
      if (l = l' ∧ n = n' ∧ l = n) then 1 else 0 := by
    by_cases hh : l = n' ∧ l' = n
    · have : l = l' ∧ n = n' ∧ l = n := by omega
      simp [hh.1, hh.2, this]
    · have : ¬ (l = l' ∧ n = n' ∧ l = n) := fun hh2 => hh (by omega)
      rw [if_neg this]
      by_cases h5 : l = n' <;> simp [h5] <;> intro h6 <;> exact absurd ⟨h5, h6⟩ hh
  simp only [kap]
  show _ * _ * 2 * ((if l = n then (1:ℝ) else 0) * (if l' = n' then 1 else 0) +
      (if l = n' then 1 else 0) * (if l' = n then 1 else 0)) = _
  rw [hB]
  by_cases hpq : l = n ∧ l' = n'
  · obtain ⟨rfl, rfl⟩ := hpq
    by_cases h : l = l'
    · subst h; simp; norm_num
    · simp [h]; exact h3
  · have h4 : ¬ (l = l' ∧ n = n' ∧ l = n) := fun hh => hpq ⟨hh.2.2, hh.1.symm.trans (hh.2.2.trans hh.2.1)⟩
    have h5 : ¬ (⟨(l, l'), hl⟩ : {p : Fin k × Fin k // p.1 ≤ p.2}) = ⟨(n, n'), hn⟩ := by
      simpa [Subtype.ext_iff, Prod.ext_iff] using hpq
    rw [if_neg h4, if_neg h5]
    by_cases h : l = n
    · have : l' ≠ n' := fun hh => hpq ⟨h, hh⟩
      simp [h, this]
    · simp [h]


lemma cos_eq {d a b : ℕ} (X : Matrix (Fin d) (Fin a) ℝ) (Y : Matrix (Fin d) (Fin b) ℝ)
    (i : Fin a) (l : Fin b) :
    colOuterSym X Y i l = vecMulVec (fun r => X r i) (fun s => Y s l) +
      vecMulVec (fun r => Y r l) (fun s => X s i) := by
  ext r s; simp [colOuterSym, vecMulVec_apply]

lemma cos_symm {d a b : ℕ} (X : Matrix (Fin d) (Fin a) ℝ) (Y : Matrix (Fin d) (Fin b) ℝ)
    (i : Fin a) (l : Fin b) : (colOuterSym X Y i l).IsSymm := by
  ext r s; simp [colOuterSym]; ring

lemma cos_rest {d m a b : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (X : Matrix (Fin d) (Fin a) ℝ)
    (Y : Matrix (Fin d) (Fin b) ℝ) (hUY : Uᵀ * Y = 0) (i : Fin a) (l : Fin b) :
    Uᵀ * colOuterSym X Y i l * U = 0 := by
  have hy : Uᵀ *ᵥ (fun s => Y s l) = 0 := by
    funext a'
    have := congrFun (congrFun hUY a') l
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hy2 : (fun s => Y s l) ᵥ* U = 0 := by
    have h := Matrix.vecMul_transpose Uᵀ (fun s => Y s l)
    rw [Matrix.transpose_transpose] at h
    rw [h, hy]
  rw [cos_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hy, hy2]
  simp


lemma restBasis_inl {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (c : Fin m × Fin k) :
    restBasis U V (Sum.inl c) = (1 / Real.sqrt 2) • colOuterSym U V c.1 c.2 := rfl

lemma rest_inRest {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hUV : Uᵀ * V = 0) (s : RestIdx m k) : InRest U (restBasis U V s) := by
  rcases s with c | p
  · rw [restBasis_inl]
    refine ⟨?_, ?_⟩
    · unfold Matrix.IsSymm; rw [Matrix.transpose_smul, (cos_symm U V c.1 c.2).eq]
    · rw [Matrix.mul_smul, Matrix.smul_mul, cos_rest U U V hUV, smul_zero]
  · rw [restBasis_inr]
    refine ⟨?_, ?_⟩
    · unfold Matrix.IsSymm; rw [Matrix.transpose_smul, (cos_symm V V _ _).eq]
    · rw [Matrix.mul_smul, Matrix.smul_mul, cos_rest U V V hUV, smul_zero]

lemma rest_orth {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) (s s' : RestIdx m k) :
    frobInner (restBasis U V s) (restBasis U V s') = if s = s' then 1 else 0 := by
  have hVU : Vᵀ * U = 0 := by
    have := congrArg Matrix.transpose hUV
    simpa [Matrix.transpose_mul] using this
  have cUU : ∀ i i', cdot U U i i' = if i = i' then 1 else 0 := fun i i' => by
    rw [cdot_eq, hU]; simp [Matrix.one_apply]
  have cVV : ∀ i i', cdot V V i i' = if i = i' then 1 else 0 := fun i i' => by
    rw [cdot_eq, hV]; simp [Matrix.one_apply]
  have cUV : ∀ i l, cdot U V i l = 0 := fun i l => by rw [cdot_eq, hUV]; simp
  have cVU : ∀ i l, cdot V U i l = 0 := fun i l => by rw [cdot_eq, hVU]; simp
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = 1 := by
    field_simp; exact (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)).symm
  rcases s with c | p <;> rcases s' with c' | q
  · rw [restBasis_inl, restBasis_inl, frobInner_smul_left, frobInner_smul_right, inner_cos,
      cUU, cUV, cVU, cVV]
    by_cases h1 : c.1 = c'.1 <;> by_cases h2' : c.2 = c'.2 <;>
      simp [h1, h2', Sum.inl.injEq, Prod.ext_iff] <;> first | (rw [← mul_assoc]; exact h2) | skip
  · rw [restBasis_inl, restBasis_inr, frobInner_smul_left, frobInner_smul_right, inner_cos,
      cUV, cUV, cVV, cVV]
    simp
  · rw [restBasis_inl, restBasis_inr, frobInner_comm, frobInner_smul_left, frobInner_smul_right,
      inner_cos, cUV, cUV, cVV, cVV]
    simp
  · rw [restBasis_inr, restBasis_inr, frobInner_smul_left, frobInner_smul_right, inner_cos,
      cVV, cVV, cVV, cVV]
    have := kap_sq p q
    simp only [Sum.inr.injEq]
    rw [← this]; ring


lemma kap_sq4 {k : ℕ} (p : {p : Fin k × Fin k // p.1 ≤ p.2}) :
    kap p * kap p * 4 = if p.1.1 = p.1.2 then 1 else 2 := by
  have h3 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = 1 := by
    field_simp; exact (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)).symm
  unfold kap
  by_cases h : p.1.1 = p.1.2
  · simp [h]; norm_num
  · simp [h]; linarith [h3]

lemma AAt_entry {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a b : Fin d) :
    ∑ p, DUmat U a p * DUmat U b p = (∑ i, U a i * U b i) ^ 2 := by
  have h1 : ∀ p : SymIdx m, DUmat U a p * DUmat U b p =
      (if p.1.1 = p.1.2 then (1:ℝ) else 2) *
        ((U a p.1.1 * U a p.1.2) * (U b p.1.1 * U b p.1.2)) := by
    intro p
    rw [Dev.E82.DUmat_apply, Dev.E82.DUmat_apply]
    by_cases h : p.1.1 = p.1.2
    · simp only [h, if_true]; ring
    · simp only [h, if_false]
      have h4 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      calc _ = (Real.sqrt 2 * Real.sqrt 2) * ((U a p.1.1 * U a p.1.2) * (U b p.1.1 * U b p.1.2)) := by ring
        _ = _ := by rw [h4]
  simp_rw [h1]
  rw [Dev.E82.sum_sym (fun i j => (U a i * U a j) * (U b i * U b j)) (fun i j => by ring)]
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma rho_diag_sum {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hmk : m + k = d) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) (a b : Fin d) :
    ∑ s, restBasis U V s a a * restBasis U V s b b =
      (if a = b then 1 else 0) - (∑ i, U a i * U b i) ^ 2 := by
  have hs := Dev.B2.split_id d m k hmk U V hU hV hUV
  have hPQ : (∑ i, U a i * U b i) + (∑ l, V a l * V b l) = if a = b then 1 else 0 := by
    have := congrFun (congrFun hs a) b
    simpa [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.one_apply] using this
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    field_simp; exact (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)).symm
  rw [Fintype.sum_sum_type]
  have e1 : ∑ c : Fin m × Fin k, restBasis U V (Sum.inl c) a a * restBasis U V (Sum.inl c) b b =
      2 * ((∑ i, U a i * U b i) * (∑ l, V a l * V b l)) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    simp only [restBasis_inl, Matrix.smul_apply, colOuterSym, smul_eq_mul, one_div]
    calc _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * 4 * ((U a i * U b i) * (V a l * V b l)) := by ring
      _ = _ := by rw [h2]; ring
  have e2 : ∑ p : {p : Fin k × Fin k // p.1 ≤ p.2}, restBasis U V (Sum.inr p) a a *
      restBasis U V (Sum.inr p) b b = (∑ l, V a l * V b l) ^ 2 := by
    have h1 : ∀ p : {p : Fin k × Fin k // p.1 ≤ p.2}, restBasis U V (Sum.inr p) a a *
        restBasis U V (Sum.inr p) b b = (if p.1.1 = p.1.2 then (1:ℝ) else 2) *
          ((V a p.1.1 * V a p.1.2) * (V b p.1.1 * V b p.1.2)) := by
      intro p
      rw [restBasis_inr]
      simp only [Matrix.smul_apply, colOuterSym, smul_eq_mul]
      rw [← kap_sq4 p]; ring
    simp_rw [h1]
    rw [Dev.E82.sum_sym (fun i j => (V a i * V a j) * (V b i * V b j)) (fun i j => by ring)]
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  rw [e1, e2]
  set P := ∑ i, U a i * U b i
  set Q := ∑ l, V a l * V b l
  have hQ : Q = (if a = b then 1 else 0) - P := by linarith
  rw [hQ]
  by_cases h : a = b <;> simp [h] <;> ring


lemma DUmat_inj {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hF : FullColRank U) :
    Function.Injective (DUmat U).mulVec := by
  have key : ∀ c : SymIdx m → ℝ, DUmat U *ᵥ c = 0 → c = 0 := by
    intro c hc'
    set c' : SymIdx m → ℝ := fun p => if p.1.1 = p.1.2 then c p else c p / Real.sqrt 2 with hc'def
    have hD : DU U (Dev.B2.Bc c') = 0 := by rw [hc'def, Dev.E82.DU_Bc, hc']
    have hB0 : Dev.B2.Bc c' = 0 := hF _ (Dev.B2.Bc_symm c') hD
    have : c' = 0 := by
      by_contra hne; exact Dev.B2.Bc_ne c' hne hB0
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

lemma G_inv {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hF : FullColRank U) :
    ((DUmat U)ᵀ * DUmat U)⁻¹ * ((DUmat U)ᵀ * DUmat U) = 1 ∧
    ((DUmat U)ᵀ * DUmat U) * ((DUmat U)ᵀ * DUmat U)⁻¹ = 1 := by
  have hpd := Matrix.PosDef.conjTranspose_mul_self (DUmat U) (DUmat_inj U hF)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpd
  have hu : IsUnit ((DUmat U)ᵀ * DUmat U).det := (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  exact ⟨Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu⟩

lemma vmv_conj {d : ℕ} {T : Type*} [Fintype T] (M : Matrix T (Fin d) ℝ) (x : Fin d → ℝ) :
    vecMulVec (M *ᵥ x) (M *ᵥ x) = M * vecMulVec x x * Mᵀ := by
  rw [← Matrix.mul_vecMulVec, Matrix.mul_assoc, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

lemma MMadj_eq {d m k : ℕ} (hmk : m + k = d) (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0)
    (hF : FullColRank U) :
    MMadj U V = ((DUmat U)ᵀ * DUmat U)⁻¹ - 1 := by
  set A := DUmat U with hA
  set G := Aᵀ * A with hG
  obtain ⟨hGi, hiG⟩ := G_inv U hF
  have hGs : Gᵀ = G := by rw [hG, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hGis : (G⁻¹)ᵀ = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, hGs]
  set W : Matrix (Fin d) (Fin d) ℝ := ∑ s, vecMulVec (diagVec (restBasis U V s))
      (diagVec (restBasis U V s)) with hW
  have hW' : W = 1 - A * Aᵀ := by
    ext a b
    simp only [hW, Matrix.sum_apply, vecMulVec_apply, diagVec, Matrix.sub_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.transpose_apply]
    rw [rho_diag_sum U V hmk hU hV hUV a b, ← AAt_entry U a b]
  set M : Matrix (SymIdx m) (Fin d) ℝ := G⁻¹ * Aᵀ with hM
  have hMM : MMadj U V = M * W * Mᵀ := by
    unfold MMadj
    rw [hW, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl; intro s _
    have hMc : Mc U (restBasis U V s) = M *ᵥ diagVec (restBasis U V s) := by
      unfold Mc
      rw [hM, ← Matrix.mulVec_mulVec]
      simp [hG, hA, Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [hMc]; exact vmv_conj M _
  rw [hMM, hW', hM]
  have e1 : Aᵀ * (1 - A * Aᵀ) * A = G - G * G := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hG]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  calc (G⁻¹ * Aᵀ) * (1 - A * Aᵀ) * (G⁻¹ * Aᵀ)ᵀ
      = G⁻¹ * (Aᵀ * (1 - A * Aᵀ) * A) * G⁻¹ := by
        rw [Matrix.transpose_mul, hGis, Matrix.transpose_transpose]; simp only [Matrix.mul_assoc]
    _ = G⁻¹ * (G - G * G) * G⁻¹ := by rw [e1]
    _ = G⁻¹ - 1 := by
        have h1 : G⁻¹ * G * G⁻¹ = G⁻¹ := by rw [hGi, Matrix.one_mul]
        have h2 : G⁻¹ * (G * G) * G⁻¹ = 1 := by
          calc G⁻¹ * (G * G) * G⁻¹ = (G⁻¹ * G) * (G * G⁻¹) := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hGi, hiG, Matrix.one_mul]
        rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2]


lemma frobInner_sub_right {n : ℕ} (X Y Z : Matrix (Fin n) (Fin n) ℝ) :
    frobInner X (Y - Z) = frobInner X Y - frobInner X Z := by
  simp only [frobInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma frobInner_sum_right {n : ℕ} {ι : Type*} [Fintype ι] (X : Matrix (Fin n) (Fin n) ℝ)
    (f : ι → Matrix (Fin n) (Fin n) ℝ) : frobInner X (∑ q, f q) = ∑ q, frobInner X (f q) := by
  simp only [frobInner, Matrix.sum_apply, Finset.mul_sum]
  calc _ = ∑ i, ∑ q, ∑ j, X i j * f q i j := by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

lemma frobInner_sum_left {n : ℕ} {ι : Type*} [Fintype ι] (X : Matrix (Fin n) (Fin n) ℝ)
    (f : ι → Matrix (Fin n) (Fin n) ℝ) : frobInner (∑ q, f q) X = ∑ q, frobInner (f q) X := by
  rw [frobInner_comm, frobInner_sum_right]
  apply Finset.sum_congr rfl; intro q _; rw [frobInner_comm]

lemma frobInner_Mmap {m : ℕ} (c c' : SymIdx m → ℝ) :
    frobInner (∑ q, c q • symBasis q) (∑ q, c' q • symBasis q) = ∑ q, c q * c' q := by
  rw [frobInner_sum_left]
  apply Finset.sum_congr rfl; intro q _
  rw [frobInner_sum_right]
  simp only [frobInner_smul_left, frobInner_smul_right, symBasis_inner]
  simp [Finset.sum_ite_eq, mul_comm]

noncomputable def Nmat {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) :
    Matrix (SymIdx m) (RestIdx m k) ℝ := fun p s => Mc U (restBasis U V s) p

lemma LGram_eq {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) :
    LGram U V = 1 + (Nmat U V)ᵀ * Nmat U V := by
  ext s s'
  have hLG : LGram U V s s' = frobInner (Lmap U (restBasis U V s)) (Lmap U (restBasis U V s')) := by
    simp only [LGram, Matrix.mul_apply, Matrix.conjTranspose_apply, Lcols, star_trivial, frobInner,
      Fintype.sum_prod_type]
  rw [hLG]
  set ρ := restBasis U V s
  set ρ' := restBasis U V s'
  set M := ∑ q, Mc U ρ q • symBasis q with hM
  set M' := ∑ q, Mc U ρ' q • symBasis q with hM'
  have hL : Lmap U ρ = ρ - U * M * Uᵀ := rfl
  have hL' : Lmap U ρ' = ρ' - U * M' * Uᵀ := rfl
  have hr := (rest_inRest U V hUV s).2
  have hr' := (rest_inRest U V hUV s').2
  rw [hL, hL', frobInner_sub_left, frobInner_sub_right, frobInner_sub_right,
    frobInner_comm ρ (U * M' * Uᵀ), frobInner_conj_rest U M' ρ hr, frobInner_conj_rest U M ρ' hr',
    frobInner_conj U hU, frobInner_Mmap, rest_orth U V hU hV hUV]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply, Nmat]
  ring


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

lemma Qhat_repro {d m k : ℕ} (hmk : m + k = d) (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0)
    (hF : FullColRank U) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) :
    Qhat U V (Q * V) = Q := by
  have hs := Dev.B2.split_id d m k hmk U V hU hV hUV
  have hQs : Qᵀ = Q := hQ.1
  set B : Matrix (Fin m) (Fin m) ℝ := Uᵀ * Q * U with hB
  have hBs : B.IsSymm := by
    unfold Matrix.IsSymm
    rw [hB, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQs,
      Matrix.mul_assoc]
  have hr : rhat U V (Q * V) = Q - U * B * Uᵀ := by
    unfold rhat
    have e1 : (Uᵀ * (Q * V))ᵀ = Vᵀ * Q * U := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hQs, Matrix.transpose_transpose]
    have e2 : (Vᵀ * (Q * V))ᵀ = Vᵀ * (Q * V) := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hQs, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    have e3 : (1 / 2 : ℝ) • (Vᵀ * (Q * V) + (Vᵀ * (Q * V))ᵀ) = Vᵀ * (Q * V) := by
      rw [e2, ← two_smul ℝ (Vᵀ * (Q * V)), smul_smul]; norm_num
    rw [e1, e3]
    have hQ' : Q = (U * Uᵀ) * Q * (U * Uᵀ) + (U * Uᵀ) * Q * (V * Vᵀ) + (V * Vᵀ) * Q * (U * Uᵀ) +
        (V * Vᵀ) * Q * (V * Vᵀ) := by
      calc Q = (U * Uᵀ + V * Vᵀ) * Q * (U * Uᵀ + V * Vᵀ) := by rw [hs]; simp
        _ = _ := by simp only [add_mul, mul_add]; abel
    have hsum : (U * (Uᵀ * (Q * V)) * Vᵀ + V * (Vᵀ * Q * U) * Uᵀ + V * (Vᵀ * (Q * V)) * Vᵀ) +
        U * B * Uᵀ = Q := by
      rw [hB]
      conv_rhs => rw [hQ']
      simp only [Matrix.mul_assoc]
      try abel
    exact eq_sub_of_add_eq hsum
  have hdiag : diagVec (rhat U V (Q * V)) = -(DUmat U *ᵥ (fun p => frobInner B (symBasis p))) := by
    rw [← DU_expand U B hBs]
    funext a
    simp only [diagVec, hr, Matrix.sub_apply, hQ.2 a, DU, Pi.neg_apply]
    ring
  obtain ⟨hGi, hiG⟩ := G_inv U hF
  have hMc : Mc U (rhat U V (Q * V)) = -(fun p => frobInner B (symBasis p)) := by
    unfold Mc
    rw [hdiag, Matrix.mulVec_neg, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mulVec_mulVec, Matrix.mul_assoc, hGi,
      Matrix.one_mulVec]
  have hMm : Mmap U (rhat U V (Q * V)) = -B := by
    unfold Mmap
    rw [hMc]
    have : ∑ p, (-(fun p => frobInner B (symBasis p))) p • symBasis p = -∑ p, frobInner B (symBasis p) • symBasis p := by
      simp [neg_smul, Finset.sum_neg_distrib]
    rw [this, sym_expand B hBs]
  have hL : Lmap U (rhat U V (Q * V)) = Q := by
    unfold Lmap
    rw [hMm, hr]; simp
  unfold Qhat
  rw [hL]
  ext i j
  simp only [P0]
  by_cases h : i = j
  · subst h; simp [hQ.2 i]
  · have := congrFun (congrFun hQs i) j
    simp only [Matrix.transpose_apply] at this
    simp [h]; linarith


noncomputable def Fm {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) :
    RestIdx m k → Fin d × Fin k → ℝ := fun s c =>
  match s with
  | Sum.inl ⟨i, l⟩ => Real.sqrt 2 * U c.1 i * (if l = c.2 then 1 else 0)
  | Sum.inr p => kap p * (V c.1 p.1.1 * (if p.1.2 = c.2 then 1 else 0) +
      V c.1 p.1.2 * (if p.1.1 = c.2 then 1 else 0))

lemma Fm_inl {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (i : Fin m) (l : Fin k) (c : Fin d × Fin k) :
    Fm U V (Sum.inl (i, l)) c = Real.sqrt 2 * U c.1 i * (if l = c.2 then 1 else 0) := rfl

lemma Fm_inr {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (p : SymIdx k) (c : Fin d × Fin k) :
    Fm U V (Sum.inr p) c = kap p * (V c.1 p.1.1 * (if p.1.2 = c.2 then 1 else 0) +
      V c.1 p.1.2 * (if p.1.1 = c.2 then 1 else 0)) := rfl

lemma E1_aux {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (Y : Matrix (Fin m) (Fin k) ℝ) (r s : Fin d) :
    ∑ i, ∑ l, Y i l * (U r i * V s l + V r l * U s i) =
      (U * Y * Vᵀ + V * Yᵀ * Uᵀ) r s := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, mul_add,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro i _
    ring
  · apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    ring

lemma E1 {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (Mg : Matrix (Fin d) (Fin k) ℝ) :
    ∑ c : Fin m × Fin k, (∑ c', Fm U V (Sum.inl c) c' * Mg c'.1 c'.2) • restBasis U V (Sum.inl c) =
      U * (Uᵀ * Mg) * Vᵀ + V * (Uᵀ * Mg)ᵀ * Uᵀ := by
  have h2 : (Real.sqrt 2) * (1 / Real.sqrt 2) = 1 := by field_simp
  have hc : ∀ i l, ∑ c' : Fin d × Fin k, Fm U V (Sum.inl (i, l)) c' * Mg c'.1 c'.2 =
      Real.sqrt 2 * (Uᵀ * Mg) i l := by
    intro i l
    rw [Fintype.sum_prod_type, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_eq_single l]
    · rw [Fm_inl]; simp [Matrix.transpose_apply]; ring
    · intro b _ hb; rw [Fm_inl]; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have e1 : ∀ i l, (∑ c', Fm U V (Sum.inl (i, l)) c' * Mg c'.1 c'.2) •
      restBasis U V (Sum.inl (i, l)) = (Uᵀ * Mg) i l • colOuterSym U V i l := by
    intro i l
    rw [hc, restBasis_inl, smul_smul]
    rw [show Real.sqrt 2 * (Uᵀ * Mg) i l * (1 / Real.sqrt 2) = (Uᵀ * Mg) i l by field_simp]
  ext r s
  rw [Fintype.sum_prod_type]
  simp_rw [e1]
  simp only [Matrix.sum_apply, Matrix.smul_apply, colOuterSym, smul_eq_mul]
  have := E1_aux U V (Uᵀ * Mg) r s
  rw [Matrix.add_apply]
  rw [Matrix.add_apply] at this
  exact this


lemma E2 {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (Mg : Matrix (Fin d) (Fin k) ℝ) :
    ∑ p : SymIdx k, (∑ c', Fm U V (Sum.inr p) c' * Mg c'.1 c'.2) • restBasis U V (Sum.inr p) =
      V * ((1 / 2 : ℝ) • (Vᵀ * Mg + (Vᵀ * Mg)ᵀ)) * Vᵀ := by
  obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin k) (Fin k) ℝ, W = Vᵀ * Mg := ⟨_, rfl⟩
  rw [← hW]
  have hc : ∀ p : SymIdx k, ∑ c' : Fin d × Fin k, Fm U V (Sum.inr p) c' * Mg c'.1 c'.2 =
      kap p * (W p.1.1 p.1.2 + W p.1.2 p.1.1) := by
    intro p
    rw [Fintype.sum_prod_type]
    simp only [Fm_inr, hW, Matrix.mul_apply, Matrix.transpose_apply]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_assoc]
  ext r s
  simp_rw [hc]
  have hterm : ∀ p : SymIdx k, ((kap p * (W p.1.1 p.1.2 + W p.1.2 p.1.1)) • restBasis U V (Sum.inr p)) r s =
      (1 / 4 : ℝ) * ((if p.1.1 = p.1.2 then (1:ℝ) else 2) *
        ((W p.1.1 p.1.2 + W p.1.2 p.1.1) * (V r p.1.1 * V s p.1.2 + V r p.1.2 * V s p.1.1))) := by
    intro p
    rw [restBasis_inr, smul_smul, Matrix.smul_apply, smul_eq_mul, ← kap_sq4 p]
    simp only [colOuterSym]
    ring
  simp only [Matrix.sum_apply, hterm]
  rw [← Finset.mul_sum]
  have hs := Dev.E82.sum_sym (fun l l' => (W l l' + W l' l) * (V r l * V s l' + V r l' * V s l))
    (fun i j => by ring)
  beta_reduce at hs
  rw [hs]
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  have h1 : ∑ x, ∑ i, 1 / 4 * ((W x i + W i x) * (V r i * V s x)) =
      ∑ x, ∑ i, 1 / 4 * ((W x i + W i x) * (V r x * V s i)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  rw [h1]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  have hc1 : ∑ j, ∑ x, V r x * (1 / 2 * W x j) * V s j = ∑ x, ∑ j, V r x * (1 / 2 * W x j) * V s j :=
    Finset.sum_comm
  have hc2 : ∑ j, ∑ x, V r x * (1 / 2 * W j x) * V s j = ∑ x, ∑ j, V r x * (1 / 2 * W j x) * V s j :=
    Finset.sum_comm
  rw [hc1, hc2]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring


lemma rhat_expand {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (Mg : Matrix (Fin d) (Fin k) ℝ) :
    rhat U V Mg = ∑ s, (∑ c, Fm U V s c * Mg c.1 c.2) • restBasis U V s := by
  rw [Fintype.sum_sum_type, E1 U V Mg, E2 U V Mg]
  unfold rhat
  simp only [add_assoc]

lemma ind_prod {k : ℕ} (a b : Fin k) :
    ∑ l0, ((if a = l0 then (1:ℝ) else 0) * (if b = l0 then 1 else 0)) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; simp
  · simp [h]

lemma Dfm_inl_inl {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (c c' : Fin m × Fin k) :
    ∑ x, Fm U V (Sum.inl c) x * Fm U V (Sum.inl c') x = if c = c' then 2 else 0 := by
  obtain ⟨i, l⟩ := c
  obtain ⟨i', l'⟩ := c'
  have hUU : ∑ a, U a i * U a i' = if i = i' then 1 else 0 := by
    have := congrFun (congrFun hU i) i'
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using this
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Fintype.sum_prod_type]
  simp only [Fm_inl]
  have : ∀ a : Fin d, ∑ l0, Real.sqrt 2 * U a i * (if l = l0 then (1:ℝ) else 0) *
      (Real.sqrt 2 * U a i' * (if l' = l0 then 1 else 0)) =
      2 * (U a i * U a i') * (if l = l' then 1 else 0) := by
    intro a
    have e : ∀ l0 : Fin k, Real.sqrt 2 * U a i * (if l = l0 then (1:ℝ) else 0) *
        (Real.sqrt 2 * U a i' * (if l' = l0 then 1 else 0)) =
        (Real.sqrt 2 * Real.sqrt 2 * (U a i * U a i')) *
          ((if l = l0 then (1:ℝ) else 0) * (if l' = l0 then 1 else 0)) := by intro l0; ring
    simp_rw [e]
    rw [← Finset.mul_sum, ind_prod, h2]
  simp_rw [this]
  rw [← Finset.sum_mul]
  have : ∑ a, 2 * (U a i * U a i') = 2 * (if i = i' then 1 else 0) := by
    rw [← Finset.mul_sum, hUU]
  rw [this]
  by_cases h1 : i = i' <;> by_cases h2 : l = l' <;> simp [h1, h2, Prod.ext_iff]


lemma Dfm_inl_inr {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hUV : Uᵀ * V = 0) (c : Fin m × Fin k) (q : SymIdx k) :
    ∑ x, Fm U V (Sum.inl c) x * Fm U V (Sum.inr q) x = 0 := by
  obtain ⟨i, l⟩ := c
  have hUV' : ∀ a' : Fin k, ∑ a, U a i * V a a' = 0 := fun a' => by
    have := congrFun (congrFun hUV i) a'
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using this
  rw [Fintype.sum_prod_type]
  simp only [Fm_inl, Fm_inr]
  have : ∀ a : Fin d, ∑ l0, Real.sqrt 2 * U a i * (if l = l0 then (1:ℝ) else 0) *
      (kap q * (V a q.1.1 * (if q.1.2 = l0 then 1 else 0) + V a q.1.2 * (if q.1.1 = l0 then 1 else 0))) =
      Real.sqrt 2 * kap q * (U a i * V a q.1.1 * (if l = q.1.2 then 1 else 0) +
        U a i * V a q.1.2 * (if l = q.1.1 then 1 else 0)) := by
    intro a
    have e : ∀ l0 : Fin k, Real.sqrt 2 * U a i * (if l = l0 then (1:ℝ) else 0) *
      (kap q * (V a q.1.1 * (if q.1.2 = l0 then 1 else 0) + V a q.1.2 * (if q.1.1 = l0 then 1 else 0))) =
      Real.sqrt 2 * kap q * (U a i * V a q.1.1) * ((if l = l0 then (1:ℝ) else 0) * (if q.1.2 = l0 then 1 else 0)) +
      Real.sqrt 2 * kap q * (U a i * V a q.1.2) * ((if l = l0 then (1:ℝ) else 0) * (if q.1.1 = l0 then 1 else 0)) := by
      intro l0; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ind_prod, ind_prod]
    ring
  simp_rw [this]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hUV', zero_mul, add_zero, mul_zero]


lemma Dfm_inr_inr {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hV : Vᵀ * V = 1) (p q : SymIdx k) :
    ∑ x, Fm U V (Sum.inr p) x * Fm U V (Sum.inr q) x = if p = q then 1 else 0 := by
  have hVV : ∀ l n : Fin k, ∑ a, V a l * V a n = if l = n then 1 else 0 := fun l n => by
    have := congrFun (congrFun hV l) n
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using this
  rw [Fintype.sum_prod_type]
  simp only [Fm_inr]
  have : ∀ a : Fin d, ∑ l0, kap p * (V a p.1.1 * (if p.1.2 = l0 then (1:ℝ) else 0) +
      V a p.1.2 * (if p.1.1 = l0 then 1 else 0)) * (kap q * (V a q.1.1 * (if q.1.2 = l0 then 1 else 0) +
      V a q.1.2 * (if q.1.1 = l0 then 1 else 0))) =
      kap p * kap q * ((V a p.1.1 * V a q.1.1) * (if p.1.2 = q.1.2 then 1 else 0) +
        (V a p.1.1 * V a q.1.2) * (if p.1.2 = q.1.1 then 1 else 0) +
        (V a p.1.2 * V a q.1.1) * (if p.1.1 = q.1.2 then 1 else 0) +
        (V a p.1.2 * V a q.1.2) * (if p.1.1 = q.1.1 then 1 else 0)) := by
    intro a
    have e : ∀ l0 : Fin k, kap p * (V a p.1.1 * (if p.1.2 = l0 then (1:ℝ) else 0) +
      V a p.1.2 * (if p.1.1 = l0 then 1 else 0)) * (kap q * (V a q.1.1 * (if q.1.2 = l0 then 1 else 0) +
      V a q.1.2 * (if q.1.1 = l0 then 1 else 0))) =
      kap p * kap q * (V a p.1.1 * V a q.1.1) * ((if p.1.2 = l0 then (1:ℝ) else 0) * (if q.1.2 = l0 then 1 else 0)) +
      kap p * kap q * (V a p.1.1 * V a q.1.2) * ((if p.1.2 = l0 then (1:ℝ) else 0) * (if q.1.1 = l0 then 1 else 0)) +
      kap p * kap q * (V a p.1.2 * V a q.1.1) * ((if p.1.1 = l0 then (1:ℝ) else 0) * (if q.1.2 = l0 then 1 else 0)) +
      kap p * kap q * (V a p.1.2 * V a q.1.2) * ((if p.1.1 = l0 then (1:ℝ) else 0) * (if q.1.1 = l0 then 1 else 0)) := by
      intro l0; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ind_prod, ind_prod, ind_prod, ind_prod]
    ring
  simp_rw [this]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hVV]
  have hk := kap_sq p q
  rw [← hk]
  ring


lemma Mc_add {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (X Y : Matrix (Fin d) (Fin d) ℝ) :
    Mc U (X + Y) = Mc U X + Mc U Y := by
  unfold Mc
  have : diagVec (X + Y) = diagVec X + diagVec Y := by funext i; simp [diagVec]
  rw [this, Matrix.mulVec_add, Matrix.mulVec_add]

lemma Mc_smul {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : ℝ) (X : Matrix (Fin d) (Fin d) ℝ) :
    Mc U (a • X) = a • Mc U X := by
  unfold Mc
  have : diagVec (a • X) = a • diagVec X := by funext i; simp [diagVec]
  rw [this, Matrix.mulVec_smul, Matrix.mulVec_smul]

lemma Lmap_add {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (X Y : Matrix (Fin d) (Fin d) ℝ) :
    Lmap U (X + Y) = Lmap U X + Lmap U Y := by
  unfold Lmap Mmap
  rw [Mc_add]
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Matrix.mul_add, Matrix.add_mul]
  abel

lemma Lmap_smul {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : ℝ) (X : Matrix (Fin d) (Fin d) ℝ) :
    Lmap U (a • X) = a • Lmap U X := by
  unfold Lmap Mmap
  rw [Mc_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Matrix.mul_smul,
    Matrix.smul_mul, smul_sub]

lemma Lmap_sum {d m : ℕ} {ι : Type*} [Fintype ι] (U : Matrix (Fin d) (Fin m) ℝ) (a : ι → ℝ)
    (X : ι → Matrix (Fin d) (Fin d) ℝ) :
    Lmap U (∑ s, a s • X s) = ∑ s, a s • Lmap U (X s) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    have h0 : diagVec (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by funext i; simp [diagVec]
    simp [Lmap, Mmap, Mc, h0]
  | insert s t hs ih =>
    rw [Finset.sum_insert hs, Finset.sum_insert hs, Lmap_add, Lmap_smul, ih]


noncomputable def Zm {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin k) ℝ :=
  fun p c => Lmap U (rhat U V (Matrix.single c.1 c.2 1)) p.1 p.2

lemma Zm_eq {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) :
    Zm U V = Lcols U V * Matrix.of (Fm U V) := by
  ext p c
  have hco : ∀ s, ∑ x : Fin d × Fin k, Fm U V s x * (Matrix.single c.1 c.2 (1:ℝ)) x.1 x.2 = Fm U V s c := by
    intro s
    rw [Finset.sum_eq_single c]
    · simp
    · intro x _ hx
      have : ¬ (c.1 = x.1 ∧ c.2 = x.2) := fun h => hx (Prod.ext h.1.symm h.2.symm)
      simp [Matrix.single_apply, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [Zm]
  rw [rhat_expand]
  simp_rw [hco]
  rw [Lmap_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Lcols,
    Matrix.of_apply]
  apply Finset.sum_congr rfl; intro s _; ring

lemma rhat_symm {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (Mg : Matrix (Fin d) (Fin k) ℝ) : (rhat U V Mg).IsSymm := by
  unfold rhat Matrix.IsSymm
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_smul, Matrix.mul_assoc]
  rw [add_comm (Mgᵀ * V) (Vᵀ * Mg)]
  abel


lemma Lmap_symm {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (X : Matrix (Fin d) (Fin d) ℝ)
    (hX : X.IsSymm) : (Lmap U X).IsSymm := by
  have hM : (Mmap U X)ᵀ = Mmap U X := by
    unfold Mmap
    rw [Matrix.transpose_sum]
    apply Finset.sum_congr rfl; intro q _
    rw [Matrix.transpose_smul, (symBasis_symm q).eq]
  unfold Matrix.IsSymm Lmap
  rw [Matrix.transpose_sub, hX.eq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hM, Matrix.mul_assoc]

lemma noiseMap_eq {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (p : Fin d × Fin d) (c : Fin d × Fin k) :
    noiseMap U V p c = if p.1 = p.2 then 0 else Zm U V p c := by
  have hs := Lmap_symm U _ (rhat_symm U V (Matrix.single c.1 c.2 (1:ℝ)))
  have h2 : Lmap U (rhat U V (Matrix.single c.1 c.2 1)) p.2 p.1 =
      Lmap U (rhat U V (Matrix.single c.1 c.2 1)) p.1 p.2 := by
    have := congrFun (congrFun hs p.1) p.2
    simpa [Matrix.transpose_apply] using this
  simp only [noiseMap, Qhat, P0, Zm]
  by_cases h : p.1 = p.2
  · simp [h]
  · simp only [h, if_false]
    rw [h2]; ring

lemma Gram_split {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) :
    (noiseMap U V)ᵀ * noiseMap U V + (Zm U V - noiseMap U V)ᵀ * (Zm U V - noiseMap U V) =
      (Zm U V)ᵀ * Zm U V := by
  ext c c'
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [noiseMap_eq, noiseMap_eq]
  by_cases h : p.1 = p.2 <;> simp [h]


noncomputable def dd (m k : ℕ) : RestIdx m k → ℝ := fun s => Sum.elim (fun _ => (2:ℝ)) (fun _ => 1) s

lemma FF_eq {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) :
    Matrix.of (Fm U V) * (Matrix.of (Fm U V))ᵀ = Matrix.diagonal (dd m k) := by
  ext s s'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.diagonal_apply]
  rcases s with c | p <;> rcases s' with c' | q
  · rw [Dfm_inl_inl U V hU]; simp [dd]
  · rw [Dfm_inl_inr U V hUV]; simp
  · have := Dfm_inl_inr U V hUV c' p
    simp only [mul_comm] at this ⊢
    rw [this]; simp
  · rw [Dfm_inr_inr U V hV]; simp [dd]

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

lemma tr_mul_diag {s : Type*} [Fintype s] [DecidableEq s] (A : Matrix s s ℝ) (f : s → ℝ) :
    (A * Matrix.diagonal f).trace = ∑ i, A i i * f i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

lemma tr_sq_diag {s : Type*} [Fintype s] [DecidableEq s] (A : Matrix s s ℝ) (f : s → ℝ) :
    (A * Matrix.diagonal f * (A * Matrix.diagonal f)).trace = ∑ i, ∑ j, A i j * f j * (A j i * f i) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_mul, mul_comm, mul_left_comm,
    mul_assoc]


lemma LGram_eq_T {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) :
    LGram U V = (Lcols U V)ᵀ * Lcols U V := by
  unfold LGram; rw [Matrix.conjTranspose_eq_transpose_of_trivial]

lemma dd_pos {m k : ℕ} (s : RestIdx m k) : 0 < dd m k s ∧ dd m k s ≤ 2 := by
  rcases s with c | p <;> simp [dd] <;> norm_num

lemma ZZ_eq {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) :
    (Zm U V)ᵀ * Zm U V = (Matrix.of (Fm U V))ᵀ * LGram U V * Matrix.of (Fm U V) := by
  rw [Zm_eq, LGram_eq_T, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

lemma trK_le {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) :
    (noiseMap U V * (noiseMap U V)ᵀ).trace ≤ 2 * (LGram U V).trace := by
  rw [Matrix.trace_mul_comm]
  have hG := congrArg Matrix.trace (Gram_split U V)
  rw [Matrix.trace_add] at hG
  have hH : 0 ≤ ((Zm U V - noiseMap U V)ᵀ * (Zm U V - noiseMap U V)).trace := by
    have := (Matrix.posSemidef_conjTranspose_mul_self (Zm U V - noiseMap U V)).trace_nonneg
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have h1 : ((Zm U V)ᵀ * Zm U V).trace = ∑ s, LGram U V s s * dd m k s := by
    rw [ZZ_eq, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
      FF_eq U V hU hV hUV, tr_mul_diag]
  have h2 : ∑ s, LGram U V s s * dd m k s ≤ 2 * (LGram U V).trace := by
    rw [Matrix.trace, Finset.mul_sum]
    apply Finset.sum_le_sum; intro s _
    have hnn : 0 ≤ LGram U V s s := by
      rw [LGram_eq_T]
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_nonneg (fun p _ => mul_self_nonneg _)
    simp only [Matrix.diag_apply]
    nlinarith [(dd_pos s).2]
  linarith


lemma trK2_le {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) :
    ((noiseMap U V * (noiseMap U V)ᵀ) * (noiseMap U V * (noiseMap U V)ᵀ)).trace ≤
      4 * (LGram U V * LGram U V).trace := by
  set K := noiseMap U V with hK
  have h0 : ((K * Kᵀ) * (K * Kᵀ)).trace = (((Kᵀ * K)) * (Kᵀ * K)).trace := by
    calc ((K * Kᵀ) * (K * Kᵀ)).trace = (K * (Kᵀ * (K * Kᵀ))).trace := by simp only [Matrix.mul_assoc]
      _ = ((Kᵀ * (K * Kᵀ)) * K).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h0]
  have h1 := tr_sq_le K (Zm U V - K) (Zm U V) (Gram_split U V)
  refine h1.trans ?_
  set F : Matrix (RestIdx m k) (Fin d × Fin k) ℝ := Matrix.of (Fm U V) with hF
  set LG := LGram U V with hLG
  have h2 : ((Zm U V)ᵀ * Zm U V * ((Zm U V)ᵀ * Zm U V)).trace =
      (LG * Matrix.diagonal (dd m k) * (LG * Matrix.diagonal (dd m k))).trace := by
    rw [ZZ_eq]
    have e : Fᵀ * LG * F * (Fᵀ * LG * F) = Fᵀ * (LG * (F * Fᵀ) * LG) * F := by
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, FF_eq U V hU hV hUV]
    simp only [Matrix.mul_assoc]
  rw [h2, tr_sq_diag]
  have hs : ∀ i j, LG j i = LG i j := fun i j => by
    rw [hLG, LGram_eq_T]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl; intro p _; ring
  rw [show (LG * LG).trace = ∑ i, ∑ j, LG i j * LG j i by simp [Matrix.trace, Matrix.mul_apply]]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  rw [hs i j]
  have a1 := dd_pos i
  have a2 := dd_pos j
  have hsq : 0 ≤ LG i j * LG i j := mul_self_nonneg _
  have : dd m k i * dd m k j ≤ 4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hsq]


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

lemma NN_eq {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) :
    MMadj U V = Nmat U V * (Nmat U V)ᵀ := by
  ext p q
  simp [MMadj, Nmat, Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply]

lemma NN_spec {d m k : ℕ} (hmk : m + k = d) (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0)
    (hF : FullColRank U) :
    ∃ (W : Matrix (SymIdx m) (SymIdx m) ℝ) (lam : SymIdx m → ℝ), Wᵀ * W = 1 ∧
      Nmat U V * (Nmat U V)ᵀ = W * Matrix.diagonal (fun j => (lam j)⁻¹ - 1) * Wᵀ ∧
      ∀ j, singVals U j = Real.sqrt (lam j) ∧ 0 < lam j := by
  obtain ⟨W, lam, hWW, hWW', hG, hl⟩ := G_spec U hF
  refine ⟨W, lam, hWW, ?_, fun j => ⟨(hl j).2, (hl j).1⟩⟩
  rw [← NN_eq, MMadj_eq hmk U V hU hV hUV hF]
  have hinv : ((DUmat U)ᵀ * DUmat U)⁻¹ = W * Matrix.diagonal (fun j => (lam j)⁻¹) * Wᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hG, spec_mul W hWW, ← Matrix.diagonal_one] 
    have : (lam * fun j => (lam j)⁻¹) = fun _ => (1:ℝ) := by
      funext j; simp [(hl j).1.ne']
    rw [this, Matrix.diagonal_one, Matrix.mul_one, hWW']
  rw [hinv]
  have h1 : (1 : Matrix (SymIdx m) (SymIdx m) ℝ) = W * Matrix.diagonal (fun _ => (1:ℝ)) * Wᵀ := by
    rw [Matrix.diagonal_one, Matrix.mul_one, hWW']
  conv_lhs => rw [h1]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]


lemma trLG {d m k : ℕ} (hmk : m + k = d) (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0)
    (hF : FullColRank U) :
    (LGram U V).trace = (Fintype.card (RestIdx m k) : ℝ) - Fintype.card (SymIdx m) +
      ∑ j, (singVals U j)⁻¹ ^ 2 := by
  obtain ⟨W, lam, hWW, hN, hl⟩ := NN_spec hmk U V hU hV hUV hF
  rw [LGram_eq U V hU hV hUV, Matrix.trace_add, Matrix.trace_one, Matrix.trace_mul_comm, hN,
    spec_tr W hWW, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have : ∀ j, (singVals U j)⁻¹ ^ 2 = (lam j)⁻¹ := fun j => by
    rw [(hl j).1, inv_pow, Real.sq_sqrt (hl j).2.le]
  simp_rw [this]
  ring

lemma trLG2 {d m k : ℕ} (hmk : m + k = d) (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0)
    (hF : FullColRank U) :
    (LGram U V * LGram U V).trace = (Fintype.card (RestIdx m k) : ℝ) - Fintype.card (SymIdx m) +
      ∑ j, (singVals U j)⁻¹ ^ 4 := by
  obtain ⟨W, lam, hWW, hN, hl⟩ := NN_spec hmk U V hU hV hUV hF
  set N := Nmat U V with hNdef
  have hC : (Nᵀ * N * (Nᵀ * N)).trace = ((N * Nᵀ) * (N * Nᵀ)).trace := by
    calc (Nᵀ * N * (Nᵀ * N)).trace = (Nᵀ * (N * (Nᵀ * N))).trace := by simp only [Matrix.mul_assoc]
      _ = ((N * (Nᵀ * N)) * Nᵀ).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have e : (1 + Nᵀ * N) * (1 + Nᵀ * N) = 1 + Nᵀ * N + Nᵀ * N + Nᵀ * N * (Nᵀ * N) := by
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]; abel
  rw [LGram_eq U V hU hV hUV, e, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_one, hC, Matrix.trace_mul_comm Nᵀ N, hN, spec_mul W hWW, spec_tr W hWW, spec_tr W hWW]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Pi.mul_apply]
  have : ∀ j, (singVals U j)⁻¹ ^ 4 = ((lam j)⁻¹) ^ 2 := fun j => by
    rw [(hl j).1, inv_pow, show (4:ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (hl j).2.le, inv_pow]
  simp_rw [this]
  have h : ∀ x, ((lam x)⁻¹ - 1) * ((lam x)⁻¹ - 1) = (lam x)⁻¹ ^ 2 - 2 * (lam x)⁻¹ + 1 := fun x => by ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring


open Polynomial in
lemma roots_prod_lin {n : Type*} [Fintype n] (f : n → ℝ) :
    (∏ i, (X - C (f i))).roots = Finset.univ.val.map f := by
  rw [Finset.prod_eq_multiset_prod]
  have : Multiset.map (fun i => X - C (f i)) Finset.univ.val =
      Multiset.map (fun a => X - C a) (Finset.univ.val.map f) := by rw [Multiset.map_map]; rfl
  rw [this]
  exact roots_multiset_prod_X_sub_C _

lemma herm_spec {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    ∃ W : Matrix n n ℝ, Wᵀ * W = 1 ∧ A = W * Matrix.diagonal hA.eigenvalues * Wᵀ := by
  set W : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)
  have hVV : Wᵀ * W = 1 := by
    have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    simpa [W, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  refine ⟨W, hVV, ?_⟩
  have := hA.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at this
  simpa [W, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this

open Polynomial in
lemma charpoly_conj_diag {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ)
    (hW : Wᵀ * W = 1) (f : n → ℝ) :
    (W * Matrix.diagonal f * Wᵀ).charpoly = ∏ i, (X - C (f i)) := by
  rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one,
    Matrix.charpoly_diagonal]

lemma card_T_le_R {d m k : ℕ} (hmk : m + k = d) (hd : 10 ≤ d) (U : Matrix (Fin d) (Fin m) ℝ)
    (hF : FullColRank U) : Fintype.card (SymIdx m) ≤ Fintype.card (RestIdx m k) := by
  have hinj := DUmat_inj U hF
  have hle : Fintype.card (SymIdx m) ≤ d := by
    have := LinearMap.finrank_le_finrank_of_injective (f := Matrix.mulVecLin (DUmat U)) hinj
    simpa [Module.finrank_fintype_fun_eq_card] using this
  rw [Dev.B2.card_symIdx] at hle ⊢
  have hR : Fintype.card (RestIdx m k) = m * k + (k + 1).choose 2 := by
    simp only [RestIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [← Dev.B2.card_symIdx k]
  have e1 : (m + 1).choose 2 = (m + 1) * m / 2 := by rw [Nat.choose_two_right]; simp
  have e2 : (k + 1).choose 2 = (k + 1) * k / 2 := by rw [Nat.choose_two_right]; simp
  rw [hR, e1, e2]
  rw [e1] at hle
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exfalso
    have h5 : 5 * m ≤ (m + 1) * m / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num)).mpr; nlinarith
    omega
  · have h3 : k ≤ (k + 1) * k / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num)).mpr; nlinarith
    have h4 : m ≤ m * k := Nat.le_mul_of_pos_right m hk
    omega


open Polynomial in
lemma spectrum_LG {d m k : ℕ} (hmk : m + k = d) (hd : 10 ≤ d) (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0)
    (hF : FullColRank U) :
    Multiset.map (LsqSpec U V) Finset.univ.val =
      Multiset.map (fun j => (singVals U j)⁻¹ ^ 2) Finset.univ.val +
        Multiset.replicate (Fintype.card (RestIdx m k) - Fintype.card (SymIdx m)) 1 := by
  obtain ⟨W, lam, hWW, hN, hl⟩ := NN_spec hmk U V hU hV hUV hF
  set N := Nmat U V with hNdef
  have hCh : (Nᵀ * N).IsHermitian := by
    have := Matrix.isHermitian_conjTranspose_mul_self N
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨W', hW'W', hspec⟩ := herm_spec (Nᵀ * N) hCh
  have hLGeq : LGram U V = W' * Matrix.diagonal (fun s => 1 + hCh.eigenvalues s) * W'ᵀ := by
    rw [LGram_eq U V hU hV hUV]
    have h1 : (1 : Matrix (RestIdx m k) (RestIdx m k) ℝ) =
        W' * Matrix.diagonal (fun _ => (1:ℝ)) * W'ᵀ := by
      rw [Matrix.diagonal_one, Matrix.mul_one, mul_eq_one_comm.mp hW'W']
    conv_lhs => rw [h1]; arg 2; rw [hspec]
    rw [← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.diagonal_add]
  have P_LG : (LGram U V).charpoly = ∏ s, (X - C (1 + hCh.eigenvalues s)) := by
    rw [hLGeq]; exact charpoly_conj_diag W' hW'W' _
  have hH := Matrix.isHermitian_conjTranspose_mul_self (Lcols U V)
  have P_LG' : (LGram U V).charpoly = ∏ s, (X - C (LsqSpec U V s)) := by
    have := hH.charpoly_eq
    simpa [LGram, LsqSpec] using this
  have hM1 : Finset.univ.val.map (LsqSpec U V) = Finset.univ.val.map (fun s => 1 + hCh.eigenvalues s) := by
    have := congrArg Polynomial.roots (P_LG'.symm.trans P_LG)
    rwa [roots_prod_lin, roots_prod_lin] at this
  have PC : (Nᵀ * N).charpoly = ∏ s, (X - C (hCh.eigenvalues s)) := by
    conv_lhs => rw [hspec]
    exact charpoly_conj_diag W' hW'W' _
  have PN : (N * Nᵀ).charpoly = ∏ j, (X - C ((lam j)⁻¹ - 1)) := by
    rw [hN]; exact charpoly_conj_diag W hWW _
  have hcomm := Matrix.charpoly_mul_comm' N Nᵀ
  have hne : ∀ {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ), A.charpoly ≠ 0 :=
    fun A => (Matrix.charpoly_monic A).ne_zero
  have hroots := congrArg Polynomial.roots hcomm
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (hne _)),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (hne _)), Polynomial.roots_X_pow,
    Polynomial.roots_X_pow, PC, PN, roots_prod_lin, roots_prod_lin] at hroots
  have hRT := card_T_le_R hmk hd U hF
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hRT
  rw [he, add_nsmul] at hroots
  have hmu : Finset.univ.val.map hCh.eigenvalues =
      Finset.univ.val.map (fun j => (lam j)⁻¹ - 1) + e • ({0} : Multiset ℝ) := by
    have h2 : Fintype.card (SymIdx m) • ({0} : Multiset ℝ) + (e • ({0} : Multiset ℝ) +
        Finset.univ.val.map (fun j => (lam j)⁻¹ - 1)) =
        Fintype.card (SymIdx m) • ({0} : Multiset ℝ) + Finset.univ.val.map hCh.eigenvalues := by
      rw [← add_assoc]; exact hroots
    rw [add_comm]
    exact (add_left_cancel h2).symm
  rw [hM1, he]
  simp only [Nat.add_sub_cancel_left]
  have hs : ∀ j, (singVals U j)⁻¹ ^ 2 = 1 + ((lam j)⁻¹ - 1) := fun j => by
    rw [(hl j).1, inv_pow, Real.sq_sqrt (hl j).2.le]; ring
  simp_rw [hs]
  have : Finset.univ.val.map (fun s => 1 + hCh.eigenvalues s) =
      (Finset.univ.val.map hCh.eigenvalues).map (fun x => 1 + x) := by rw [Multiset.map_map]; rfl
  rw [this, hmu, Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton, Multiset.map_map,
    Multiset.nsmul_singleton]
  simp [Function.comp_def]

end HigherOrderId.Certify.Dev.B5
end

section
open Matrix

namespace HigherOrderId.Certify

theorem chk_lemma_B_5 (d m k : ℕ) (hd : 10 ≤ d) (hmk : m + k = d)
    (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) (hfull : FullColRank U)
    (v : ℝ) (hv : 0 < v) :
    MMadj U V = ((DUmat U)ᴴ * DUmat U)⁻¹ - 1 ∧
    Multiset.map (LsqSpec U V) Finset.univ.val =
      Multiset.map (fun j => (singVals U j)⁻¹ ^ 2) Finset.univ.val +
        Multiset.replicate (Fintype.card (RestIdx m k) - Fintype.card (SymIdx m)) 1 ∧
    (∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Qhat U V (Q * V) = Q) ∧
    (GammaEntry U V v).trace ≤
      2 * v * ((Fintype.card (RestIdx m k) : ℝ) - Fintype.card (SymIdx m) +
        ∑ j, (singVals U j)⁻¹ ^ 2) ∧
    (GammaEntry U V v * GammaEntry U V v).trace ≤
      4 * v ^ 2 * ((Fintype.card (RestIdx m k) : ℝ) - Fintype.card (SymIdx m) +
        ∑ j, (singVals U j)⁻¹ ^ 4) := by
  refine ⟨?_, ?_, fun Q hQ => Dev.B5.Qhat_repro hmk U V hU hV hUV hfull Q hQ, ?_, ?_⟩
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Dev.B5.MMadj_eq hmk U V hU hV hUV hfull
  · exact Dev.B5.spectrum_LG hmk hd U V hU hV hUV hfull
  · have h1 := Dev.B5.trK_le U V hU hV hUV
    have h2 := Dev.B5.trLG hmk U V hU hV hUV hfull
    show (v • (noiseMap U V * (noiseMap U V)ᵀ)).trace ≤ _
    rw [Matrix.trace_smul, smul_eq_mul]
    rw [h2] at h1
    nlinarith [h1, hv]
  · have h1 := Dev.B5.trK2_le U V hU hV hUV
    have h2 := Dev.B5.trLG2 hmk U V hU hV hUV hfull
    show ((v • (noiseMap U V * (noiseMap U V)ᵀ)) * (v • (noiseMap U V * (noiseMap U V)ᵀ))).trace ≤ _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [h2] at h1
    have hv2 : 0 ≤ v * v := mul_self_nonneg v
    nlinarith [mul_le_mul_of_nonneg_left h1 hv2]

end HigherOrderId.Certify
end

theorem solution : type_of% @HigherOrderId.Certify.chk_lemma_B_5 := @HigherOrderId.Certify.chk_lemma_B_5
