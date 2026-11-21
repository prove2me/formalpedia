-- Prove2me | solution 1 for HigherOrderId.Certify.eq_101
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T21:21:59.573866+00:00
-- url     : https://prove2.me/submissions/f04f4e0f-637a-4c0e-b859-883bbe4eedbe

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion
import Definitions.Def_HigherOrderId_Certify_TallCompletion
import Definitions.Def_HigherOrderId_Certify_Release
import Definitions.Def_HigherOrderId_Certify_Fisher
import Theorems.Thm_HigherOrderId_Certify_lemma_B_1
import Theorems.Thm_HigherOrderId_Certify_lemma_B_2
import Theorems.Thm_HigherOrderId_Certify_eq_84_87
import Theorems.Thm_HigherOrderId_Certify_lemma_B_4
import Theorems.Thm_HigherOrderId_Certify_lemma_B_5

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

lemma frobInner_self_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobInner X X :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_self_nonneg _))

lemma frobNorm_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : frobNorm X ^ 2 = frobInner X X := by
  unfold frobNorm; exact Real.sq_sqrt (frobInner_self_nonneg X)

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


end HigherOrderId.Certify.Dev.B5
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.E101
open HigherOrderId.Certify

/-- Bessel's inequality for an orthonormal family of vectors. -/
lemma bessel {ι T : Type*} [Fintype ι] [DecidableEq T] (a : ι → ℝ) (J : Finset T) (q : T → ι → ℝ)
    (horth : ∀ i ∈ J, ∀ j ∈ J, q i ⬝ᵥ q j = if i = j then 1 else 0) :
    ∑ j ∈ J, (a ⬝ᵥ q j) ^ 2 ≤ a ⬝ᵥ a := by
  classical
  set r : ι → ℝ := a - ∑ j ∈ J, (a ⬝ᵥ q j) • q j with hr
  have hrq : ∀ i ∈ J, r ⬝ᵥ q i = 0 := by
    intro i hi
    rw [hr, sub_dotProduct, sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [horth i hi i hi]; simp
    · intro j hj hji; rw [horth j hj i hi, if_neg hji, mul_zero]
    · intro h; exact absurd hi h
  have hrr : r ⬝ᵥ r = a ⬝ᵥ a - ∑ j ∈ J, (a ⬝ᵥ q j) ^ 2 := by
    have h1 : r ⬝ᵥ r = r ⬝ᵥ a := by
      have e : r ⬝ᵥ r = r ⬝ᵥ (a - ∑ j ∈ J, (a ⬝ᵥ q j) • q j) := by rw [← hr]
      rw [e, dotProduct_sub, dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul]
      rw [Finset.sum_eq_zero (fun i hi => by rw [hrq i hi, mul_zero]), sub_zero]
    rw [h1, hr, sub_dotProduct, sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
    congr 1; apply Finset.sum_congr rfl; intro j _; rw [dotProduct_comm (q j) a]; ring
  have : 0 ≤ r ⬝ᵥ r := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  linarith

/-- Flattening of a matrix into a vector. -/
def flat {ι κ : Type*} (X : Matrix ι κ ℝ) : ι × κ → ℝ := fun p => X p.1 p.2

lemma frobInner_flat {ι κ : Type*} [Fintype ι] [Fintype κ] (X Y : Matrix ι κ ℝ) :
    frobInner X Y = flat X ⬝ᵥ flat Y := by
  simp [frobInner, flat, dotProduct, Fintype.sum_prod_type]

lemma flat_vmv {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    flat (vecMulVec a a) ⬝ᵥ flat (vecMulVec b b) = (a ⬝ᵥ b) ^ 2 := by
  simp only [flat, dotProduct, vecMulVec_apply, Fintype.sum_prod_type, sq, Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma flat_vmv_mat {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (b : ι → ℝ) :
    flat S ⬝ᵥ flat (vecMulVec b b) = b ⬝ᵥ (S *ᵥ b) := by
  simp only [flat, dotProduct, vecMulVec_apply, Fintype.sum_prod_type, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma real_star {ι : Type*} (x : ι → ℝ) : star x = x := by
  funext i; simp

/-- Rayleigh / Cauchy–Schwarz: `(qᵀq)² ≤ (qᵀ A q)(qᵀ A⁻¹ q)` for positive definite `A`. -/
lemma rayleigh {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (q : ι → ℝ) : (q ⬝ᵥ q) ^ 2 ≤ (q ⬝ᵥ (A *ᵥ q)) * (q ⬝ᵥ (A⁻¹ *ᵥ q)) := by
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hAT : Aᵀ = A := by
    have := hA.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsym : ∀ x y : ι → ℝ, x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← hAT, Matrix.vecMul_transpose, hAT, dotProduct_comm]
  have hpsd : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    intro x; have := hA.posSemidef.dotProduct_mulVec_nonneg x; rwa [real_star] at this
  set z := A⁻¹ *ᵥ q with hz
  have hAz : A *ᵥ z = q := by rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]
  have hzAq : z ⬝ᵥ (A *ᵥ q) = q ⬝ᵥ q := by rw [hsym, hAz]
  have hzAz : z ⬝ᵥ (A *ᵥ z) = q ⬝ᵥ z := by rw [hAz, dotProduct_comm]
  have hquad : ∀ t : ℝ, 0 ≤ (q ⬝ᵥ z) * (t * t) + (-2 * (q ⬝ᵥ q)) * t + q ⬝ᵥ (A *ᵥ q) := by
    intro t
    have h := hpsd (q - t • z)
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hAz, dotProduct_sub, sub_dotProduct,
      sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul,
      hzAq] at h
    simp only [smul_eq_mul, dotProduct_comm z q] at h
    nlinarith
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith

/-- Lower bound on the Frobenius norm of `A⁻¹` from an orthogonal family of test vectors. -/
lemma frob_inv_lower {ι T : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq T] (A : Matrix ι ι ℝ)
    (hA : A.PosDef) (J : Finset T) (q : T → ι → ℝ)
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → q i ⬝ᵥ q j = 0) (hne : ∀ j ∈ J, q j ≠ 0) :
    ∑ j ∈ J, ((q j ⬝ᵥ q j) / (q j ⬝ᵥ (A *ᵥ q j))) ^ 2 ≤ frobInner A⁻¹ A⁻¹ := by
  classical
  have hpos : ∀ j ∈ J, 0 < q j ⬝ᵥ q j := by
    intro j hj
    have := dotProduct_self_star_pos_iff.mpr (hne j hj)
    rwa [real_star] at this
  have hApos : ∀ j ∈ J, 0 < q j ⬝ᵥ (A *ᵥ q j) := by
    intro j hj; have := hA.dotProduct_mulVec_pos (hne j hj); rwa [real_star] at this
  set n : T → ℝ := fun j => Real.sqrt (q j ⬝ᵥ q j) with hn
  set qh : T → ι → ℝ := fun j => (n j)⁻¹ • q j with hqh
  have hn2 : ∀ j ∈ J, n j * n j = q j ⬝ᵥ q j := fun j hj =>
    Real.mul_self_sqrt (hpos j hj).le
  have hnpos : ∀ j ∈ J, 0 < n j := fun j hj => Real.sqrt_pos.mpr (hpos j hj)
  have horthh : ∀ i ∈ J, ∀ j ∈ J,
      flat (vecMulVec (qh i) (qh i)) ⬝ᵥ flat (vecMulVec (qh j) (qh j)) =
        if i = j then 1 else 0 := by
    intro i hi j hj
    rw [flat_vmv]
    simp only [hqh, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, ← hn2 i hi]
      have := (hnpos i hi).ne'
      field_simp
    · rw [if_neg hij, horth i hi j hj hij]; simp
  have hb := bessel (flat A⁻¹) J (fun j => flat (vecMulVec (qh j) (qh j))) horthh
  rw [← frobInner_flat] at hb
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) hb
  rw [flat_vmv_mat]
  have hr := rayleigh A hA (q j)
  have hqq := hpos j hj
  have hqa := hApos j hj
  have hS : (q j ⬝ᵥ q j) / (q j ⬝ᵥ (A *ᵥ q j)) ≤ qh j ⬝ᵥ (A⁻¹ *ᵥ qh j) := by
    simp only [hqh, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    have hnj := hnpos j hj
    have hnn := hn2 j hj
    rw [div_le_iff₀ hqa]
    have e : (n j)⁻¹ * ((n j)⁻¹ * (q j ⬝ᵥ (A⁻¹ *ᵥ q j))) * (q j ⬝ᵥ (A *ᵥ q j)) =
        ((q j ⬝ᵥ (A *ᵥ q j)) * (q j ⬝ᵥ (A⁻¹ *ᵥ q j))) / (q j ⬝ᵥ q j) := by
      rw [← hnn]; field_simp
    rw [e, le_div_iff₀ hqq]
    nlinarith
  have h0 : 0 ≤ (q j ⬝ᵥ q j) / (q j ⬝ᵥ (A *ᵥ q j)) := div_nonneg hqq.le hqa.le
  exact pow_le_pow_left₀ h0 hS 2

end HigherOrderId.Certify.Dev.E101
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.E101
open HigherOrderId.Certify

/-! ## The `ϑ`-coordinates of a matrix in `S^d_0` and the Fisher quadratic form -/

/-- The `ϑ`-vector of `(0, Q)`: zero `b`-part, entries `Q_ij` for `i < j`. -/
def qv {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) : ThetaIdx d → ℝ :=
  Sum.elim 0 (fun p => Q p.1.1 p.1.2)

/-- The `Q`-part `E_ij + E_ji` of the coordinate `Q_ij`. -/
def Tp {d : ℕ} (p : {p : Fin d × Fin d // p.1 < p.2}) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1

lemma sum_pairs {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) :
    ∑ p : {p : Fin d × Fin d // p.1 < p.2}, Q p.1.1 p.1.2 • Tp p = Q := by
  have hs : ∀ i j, Q j i = Q i j := fun i j => by
    have := congrFun (congrFun hQ.1 i) j; simpa [Matrix.transpose_apply] using this
  ext a b
  rw [Matrix.sum_apply]
  simp only [Tp, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | h | h
  · rw [Finset.sum_eq_single (⟨(a, b), h⟩ : {p : Fin d × Fin d // p.1 < p.2})]
    · simp [h.ne]
    · intro p _ hp
      have h1 : ¬ (p.1.1 = a ∧ p.1.2 = b) := fun hh => hp (Subtype.ext (Prod.ext hh.1 hh.2))
      have h2 : ¬ (p.1.2 = a ∧ p.1.1 = b) := fun hh => by
        have := p.2; rw [hh.1, hh.2] at this; exact absurd h (not_lt.mpr this.le)
      simp [h1, h2]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · subst h
    rw [hQ.2]
    apply Finset.sum_eq_zero; intro p _
    have h1 : ¬ (p.1.1 = a ∧ p.1.2 = a) := fun hh => by
      have := p.2; rw [hh.1, hh.2] at this; exact lt_irrefl _ this
    have h2 : ¬ (p.1.2 = a ∧ p.1.1 = a) := fun hh => h1 ⟨hh.2, hh.1⟩
    simp [h1, h2]
  · rw [Finset.sum_eq_single (⟨(b, a), h⟩ : {p : Fin d × Fin d // p.1 < p.2})]
    · simp [h.ne, hs]
    · intro p _ hp
      have h2 : ¬ (p.1.2 = a ∧ p.1.1 = b) := fun hh => hp (Subtype.ext (Prod.ext hh.2 hh.1))
      have h1 : ¬ (p.1.1 = a ∧ p.1.2 = b) := fun hh => by
        have := p.2; rw [hh.1, hh.2] at this; exact absurd h (not_lt.mpr this.le)
      simp [h1, h2]
    · intro hh; exact absurd (Finset.mem_univ _) hh

/-- `Σ_s q_s thetaB_s` for `q = qv Q`. -/
lemma hq_qv {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) :
    ∑ s, qv Q s • thetaB s = 0 := by
  simp [qv, thetaB, Fintype.sum_sum_type]

lemma Hq_qv {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) :
    ∑ s, qv Q s • thetaQ s = Q := by
  simp only [Fintype.sum_sum_type, qv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul,
    Finset.sum_const_zero, zero_add, thetaQ]
  exact sum_pairs Q hQ

lemma qv_eq_zero {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) (h : qv Q = 0) :
    Q = 0 := by
  rw [← Hq_qv Q hQ, h]; simp

/-- Sums over ordered pairs of a symmetric function vanishing on the diagonal. -/
lemma sum_lt_pairs {d : ℕ} (f : Fin d → Fin d → ℝ) (hf : ∀ i j, f i j = f j i)
    (h0 : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ p : {p : Fin d × Fin d // p.1 < p.2}, f p.1.1 p.1.2 := by
  have h1 : ∑ p : {p : Fin d × Fin d // p.1 < p.2}, f p.1.1 p.1.2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2), f p.1 p.2 :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2))
      (by intro x; simp) (fun p => f p.1 p.2)).symm
  rw [h1, Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ i, ∑ j, f i j =
      ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [h0]
    · simp [h, not_lt.mpr h.le]
  have h3 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [hf]
  rw [h2]
  simp only [Finset.sum_add_distrib]
  rw [h3]; ring

lemma qv_dot {d : ℕ} (Q Q' : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q)
    (hQ' : IsSymZeroDiag Q') : qv Q ⬝ᵥ qv Q' = frobInner Q Q' / 2 := by
  have hs : ∀ (X : Matrix (Fin d) (Fin d) ℝ), IsSymZeroDiag X → ∀ i j, X j i = X i j :=
    fun X hX i j => by
      have := congrFun (congrFun hX.1 i) j; simpa [Matrix.transpose_apply] using this
  have := sum_lt_pairs (fun i j => Q i j * Q' i j) (fun i j => by rw [hs Q hQ, hs Q' hQ'])
    (fun i => by simp [hQ.2])
  simp only [frobInner, this, dotProduct, Fintype.sum_sum_type, qv, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  ring

lemma qv_ne {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) (hne : Q ≠ 0) :
    qv Q ≠ 0 := fun h => hne (qv_eq_zero Q hQ h)

/-! ## The Fisher matrix as a Gram matrix -/

noncomputable def Lm {d E : ℕ} (D : Design d E) : Matrix (Fin E) (ThetaIdx d) ℝ :=
  fun e s => thetaB s ⬝ᵥ D.x e + (1 / 2) * (D.x e ⬝ᵥ (thetaQ s *ᵥ D.x e))

noncomputable def Gm {d E : ℕ} (D : Design d E) : Matrix (Fin E × Fin d) (ThetaIdx d) ℝ :=
  fun p s => thetaB s p.2 + (thetaQ s *ᵥ D.x p.1) p.2

noncomputable def cw {d E : ℕ} (D : Design d E) (σ : ℝ) : Fin E → ℝ :=
  fun e => (D.n e : ℝ) / σ ^ 2

lemma fisher_decomp {d E : ℕ} (D : Design d E) (σ : ℝ) :
    fullFisherMat D σ = (Lm D)ᵀ * Matrix.diagonal (cw D σ) * Lm D +
      (Gm D).transpose * (Matrix.diagonal (fun p : Fin E × Fin d => cw D σ p.1) :
        Matrix (Fin E × Fin d) (Fin E × Fin d) ℝ) * Gm D := by
  ext s s'
  simp only [fullFisherMat, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Fintype.sum_prod_type, Lm, Gm, cw]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro e _
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl; intro i _; ring

lemma quad_gram {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] (A : Matrix R S ℝ)
    (c : R → ℝ) (q : S → ℝ) :
    q ⬝ᵥ ((Aᵀ * Matrix.diagonal c * A) *ᵥ q) = ∑ r, c r * (A *ᵥ q) r ^ 2 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl; intro r _; ring

lemma Lm_qv {d E : ℕ} (D : Design d E) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) :
    Lm D *ᵥ qv Q = fun e => (1 / 2) * (D.x e ⬝ᵥ (Q *ᵥ D.x e)) := by
  funext e
  have h1 : Lm D *ᵥ qv Q = fun e => ∑ s, qv Q s * (thetaB s ⬝ᵥ D.x e) +
      (1 / 2) * ∑ s, qv Q s * (D.x e ⬝ᵥ (thetaQ s *ᵥ D.x e)) := by
    funext e
    change ∑ s, Lm D e s * qv Q s = _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s _; simp only [Lm]; ring
  rw [h1]
  have h2 : ∑ s, qv Q s * (thetaB s ⬝ᵥ D.x e) = (∑ s, qv Q s • thetaB s) ⬝ᵥ D.x e := by
    rw [sum_dotProduct]; simp [smul_dotProduct]
  have h3 : ∑ s, qv Q s * (D.x e ⬝ᵥ (thetaQ s *ᵥ D.x e)) =
      D.x e ⬝ᵥ ((∑ s, qv Q s • thetaQ s) *ᵥ D.x e) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    simp [Matrix.smul_mulVec, dotProduct_smul]
  simp only
  rw [h2, h3, hq_qv, Hq_qv Q hQ]; simp

lemma Gm_qv {d E : ℕ} (D : Design d E) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) :
    Gm D *ᵥ qv Q = fun p => (Q *ᵥ D.x p.1) p.2 := by
  funext p
  have h1 : (Gm D *ᵥ qv Q) p = (∑ s, qv Q s • thetaB s) p.2 +
      ((∑ s, qv Q s • thetaQ s) *ᵥ D.x p.1) p.2 := by
    change ∑ s, Gm D p s * qv Q s = _
    rw [Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s _
    simp only [Gm, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, hq_qv, Hq_qv Q hQ]; simp

/-- The Fisher quadratic form at `qv Q` is the full Fisher information at `(0, Q)`. -/
lemma quad_qv {d E : ℕ} (D : Design d E) (σ : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsSymZeroDiag Q) :
    qv Q ⬝ᵥ (fullFisherMat D σ *ᵥ qv Q) = fullFisher D σ 0 Q := by
  rw [fisher_decomp, Matrix.add_mulVec, dotProduct_add, quad_gram, quad_gram, Lm_qv D Q hQ,
    Gm_qv D Q hQ]
  simp only [fullFisher, gradFisher, valueFisher, cw, Fintype.sum_prod_type, Pi.zero_apply,
    zero_add, zero_dotProduct, Finset.mul_sum]
  ring

end HigherOrderId.Certify.Dev.E101
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.E101
open HigherOrderId.Certify

lemma vmv_conj' {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    vecMulVec (M *ᵥ x) (M *ᵥ x) = M * vecMulVec x x * Mᵀ := by
  rw [← Matrix.mul_vecMulVec, Matrix.mul_assoc, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

lemma sq_sum_trace {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    ∑ i, (M *ᵥ x) i ^ 2 = (M * vecMulVec x x * Mᵀ).trace := by
  rw [← vmv_conj']; simp [Matrix.trace, vecMulVec_apply, sq]

lemma trace_mul_transpose {d k : ℕ} (X : Matrix (Fin d) (Fin k) ℝ) :
    (X * Xᵀ).trace = frobInner X X := by
  simp [Matrix.trace, Matrix.mul_apply, frobInner]

/-- On the design class, `I_grad(0, Q) = ‖Q W‖_F² / v_N`. -/
lemma grad_eq (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1)) (hmd : m < d) (hα : 0 < α)
    (hσ : 0 < σ) (W : Matrix (Fin d) (Fin (d - m)) ℝ)
    (hWx : ((d - m + 1 : ℕ) : ℝ)⁻¹ • ∑ e, vecMulVec (D.x e) (D.x e) =
      (α ^ 2 / ((d - m : ℕ) : ℝ)) • (W * Wᵀ))
    (hdiv : (d - m + 1) ∣ N) (hpos : 0 < N / (d - m + 1)) (hn : ∀ e, D.n e = N / (d - m + 1))
    (Q : Matrix (Fin d) (Fin d) ℝ) :
    gradFisher D σ 0 Q = frobInner (Q * W) (Q * W) / vN d m N α σ := by
  have hN : (N : ℝ) = ((N / (d - m + 1) : ℕ) : ℝ) * ((d - m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_mul_cancel hdiv).symm
  have hEpos : (0 : ℝ) < ((d - m + 1 : ℕ) : ℝ) := by positivity
  have hnpos : (0 : ℝ) < ((N / (d - m + 1) : ℕ) : ℝ) := by exact_mod_cast hpos
  have hk : ((d - m : ℕ) : ℝ) = (d : ℝ) - m := by rw [Nat.cast_sub hmd.le]
  have hkpos : (0 : ℝ) < (d : ℝ) - m := by
    have : (m : ℝ) < d := by exact_mod_cast hmd
    linarith
  have hS : ∑ e, vecMulVec (D.x e) (D.x e) = (((d - m + 1 : ℕ) : ℝ) * (α ^ 2 / ((d - m : ℕ) : ℝ))) •
      (W * Wᵀ) := by
    rw [mul_smul, ← hWx, smul_smul, mul_inv_cancel₀ hEpos.ne', one_smul]
  have h1 : gradFisher D σ 0 Q = (((N / (d - m + 1) : ℕ) : ℝ) / σ ^ 2) * ∑ e, ∑ i, (Q *ᵥ D.x e) i ^ 2 := by
    simp only [gradFisher, hn, Pi.zero_apply, zero_add, Finset.mul_sum]
  have h2 : ∑ e, ∑ i, (Q *ᵥ D.x e) i ^ 2 =
      (((d - m + 1 : ℕ) : ℝ) * (α ^ 2 / ((d - m : ℕ) : ℝ))) * frobInner (Q * W) (Q * W) := by
    simp only [sq_sum_trace]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, hS, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← trace_mul_transpose,
      Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [h1, h2, vN, hN, hk]
  field_simp

/-- `‖X W‖_F² ≤ ‖X‖_F²` for `W` with orthonormal columns (Bessel row by row). -/
lemma frob_W_le {d k : ℕ} (W : Matrix (Fin d) (Fin k) ℝ) (hW : Wᵀ * W = 1)
    (X : Matrix (Fin d) (Fin d) ℝ) : frobInner (X * W) (X * W) ≤ frobInner X X := by
  unfold frobInner
  apply Finset.sum_le_sum; intro a _
  have hb := bessel (X a) (Finset.univ : Finset (Fin k)) (fun l => fun r => W r l)
    (fun i _ j _ => by
      have := congrFun (congrFun hW i) j
      simpa [Matrix.mul_apply, Matrix.one_apply, dotProduct] using this)
  simp only [dotProduct] at hb
  simpa [Matrix.mul_apply, sq] using hb

/-- The class hypotheses used by Lemma B.1. -/
lemma fisher_qv_le (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1)) (hd : 10 ≤ d)
    (hmd : m < d) (hα : 0 < α) (hα1 : α ≤ 1 / 2) (hσ : 0 < σ)
    (hD : InDesignClass d m N α D) (W : Matrix (Fin d) (Fin (d - m)) ℝ)
    (hWx : ((d - m + 1 : ℕ) : ℝ)⁻¹ • ∑ e, vecMulVec (D.x e) (D.x e) =
      (α ^ 2 / ((d - m : ℕ) : ℝ)) • (W * Wᵀ))
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) :
    qv Q ⬝ᵥ (fullFisherMat D σ *ᵥ qv Q) ≤
      (3 / 2) * (frobInner (Q * W) (Q * W) / vN d m N α σ) := by
  obtain ⟨hnorm, hcent, _, hdiv, hpos, hn⟩ := hD
  have hB1 := HigherOrderId.Certify.lemma_B_1 d (d - m + 1) D α σ hd hα hα1 hσ hcent
    (fun e e' => by rw [hn e, hn e']) (fun e => by rw [hn e]; exact hpos)
    (fun e => by rw [hnorm e, Real.sqrt_sq hα.le]) 0 Q hQ
  rw [quad_qv D σ Q hQ, ← grad_eq d m N α σ D hmd hα hσ W hWx hdiv hpos hn Q]
  linarith [hB1.2.1, hB1.2.2]

lemma vN_pos (d m N : ℕ) (α σ : ℝ) (hmd : m < d) (hα : 0 < α) (hσ : 0 < σ) (hN : 0 < N) :
    0 < vN d m N α σ := by
  unfold vN
  have : (m : ℝ) < d := by exact_mod_cast hmd
  have : (0 : ℝ) < N := by exact_mod_cast hN
  apply div_pos
  · apply mul_pos (by positivity); linarith
  · positivity

lemma N_pos (d m N : ℕ) (hpos : 0 < N / (d - m + 1)) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp at hpos
  · exact h

/-- Lower bound of `‖Σ^eff‖_F²` from a Frobenius-orthogonal family in `S^d_0`. -/
lemma family_lower {T : Type*} [DecidableEq T] (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1))
    (hd : 10 ≤ d) (hmd : m < d) (hα : 0 < α) (hα1 : α ≤ 1 / 2) (hσ : 0 < σ)
    (hD : InDesignClass d m N α D) (W : Matrix (Fin d) (Fin (d - m)) ℝ)
    (hWx : ((d - m + 1 : ℕ) : ℝ)⁻¹ • ∑ e, vecMulVec (D.x e) (D.x e) =
      (α ^ 2 / ((d - m : ℕ) : ℝ)) • (W * Wᵀ))
    (hPD : (fullFisherMat D σ).PosDef)
    (J : Finset T) (Q : T → Matrix (Fin d) (Fin d) ℝ) (β : T → ℝ)
    (hQ : ∀ j ∈ J, IsSymZeroDiag (Q j))
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → frobInner (Q i) (Q j) = 0)
    (hne : ∀ j ∈ J, Q j ≠ 0) (hβ : ∀ j ∈ J, 0 < β j)
    (hW : ∀ j ∈ J, frobInner (Q j * W) (Q j * W) ≤ β j * frobInner (Q j) (Q j)) :
    ∑ j ∈ J, (vN d m N α σ / (3 * β j)) ^ 2 ≤ frobInner (SigmaEff D σ) (SigmaEff D σ) := by
  have hv := vN_pos d m N α σ hmd hα hσ (N_pos d m N hD.2.2.2.2.1)
  have hmain := frob_inv_lower (fullFisherMat D σ) hPD J (fun j => qv (Q j))
    (fun i hi j hj hij => by
      rw [qv_dot _ _ (hQ i hi) (hQ j hj), horth i hi j hj hij]; simp)
    (fun j hj => qv_ne _ (hQ j hj) (hne j hj))
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) hmain
  have hqq : qv (Q j) ⬝ᵥ qv (Q j) = frobInner (Q j) (Q j) / 2 := qv_dot _ _ (hQ j hj) (hQ j hj)
  have hF : 0 < frobInner (Q j) (Q j) := by
    have h1 : qv (Q j) ≠ 0 := qv_ne _ (hQ j hj) (hne j hj)
    have := dotProduct_self_star_pos_iff.mpr h1
    rw [real_star, hqq] at this; linarith
  have hIpos : 0 < qv (Q j) ⬝ᵥ (fullFisherMat D σ *ᵥ qv (Q j)) := by
    have := hPD.dotProduct_mulVec_pos (qv_ne _ (hQ j hj) (hne j hj)); rwa [real_star] at this
  have hIle := fisher_qv_le d m N α σ D hd hmd hα hα1 hσ hD W hWx (Q j) (hQ j hj)
  have hbj := hβ j hj
  have hWj := hW j hj
  have hkey : vN d m N α σ / (3 * β j) ≤
      qv (Q j) ⬝ᵥ qv (Q j) / (qv (Q j) ⬝ᵥ (fullFisherMat D σ *ᵥ qv (Q j))) := by
    rw [hqq, div_le_div_iff₀ (by positivity) hIpos]
    have h3 : qv (Q j) ⬝ᵥ (fullFisherMat D σ *ᵥ qv (Q j)) ≤
        (3 / 2) * (β j * frobInner (Q j) (Q j) / vN d m N α σ) := by
      refine le_trans hIle ?_
      gcongr
    have h4 : vN d m N α σ * ((3 / 2) * (β j * frobInner (Q j) (Q j) / vN d m N α σ)) =
        frobInner (Q j) (Q j) / 2 * (3 * β j) := by
      field_simp
    nlinarith
  exact pow_le_pow_left₀ (by positivity) hkey 2

/-- `Q W = 0` forces `Q = 0` when the full Fisher information is positive definite. -/
lemma QW_zero (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1))
    (hd : 10 ≤ d) (hmd : m < d) (hα : 0 < α) (hα1 : α ≤ 1 / 2) (hσ : 0 < σ)
    (hD : InDesignClass d m N α D) (W : Matrix (Fin d) (Fin (d - m)) ℝ)
    (hWx : ((d - m + 1 : ℕ) : ℝ)⁻¹ • ∑ e, vecMulVec (D.x e) (D.x e) =
      (α ^ 2 / ((d - m : ℕ) : ℝ)) • (W * Wᵀ))
    (hPD : (fullFisherMat D σ).PosDef)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) (hQW : Q * W = 0) : Q = 0 := by
  by_contra hne
  have hIpos : 0 < qv Q ⬝ᵥ (fullFisherMat D σ *ᵥ qv Q) := by
    have := hPD.dotProduct_mulVec_pos (qv_ne _ hQ hne); rwa [real_star] at this
  have hIle := fisher_qv_le d m N α σ D hd hmd hα hα1 hσ hD W hWx Q hQ
  rw [hQW] at hIle
  simp [frobInner] at hIle
  linarith

end HigherOrderId.Certify.Dev.E101
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.E101
open HigherOrderId.Certify

lemma Tp_szd {d : ℕ} (p : {p : Fin d × Fin d // p.1 < p.2}) : IsSymZeroDiag (Tp p) := by
  constructor
  · ext i j
    simp only [Tp, Matrix.transpose_apply, Matrix.add_apply, Matrix.single_apply]
    rw [add_comm]; simp only [and_comm]
  · intro i
    have h := p.2
    have h1 : ¬ (p.1.1 = i ∧ p.1.2 = i) := fun hh => by
      rw [hh.1, hh.2] at h; exact lt_irrefl _ h
    have h2 : ¬ (p.1.2 = i ∧ p.1.1 = i) := fun hh => h1 ⟨hh.2, hh.1⟩
    simp [Tp, Matrix.single_apply, h1, h2]

lemma qv_Tp {d : ℕ} (p : {p : Fin d × Fin d // p.1 < p.2}) :
    qv (Tp p) = fun s => if s = Sum.inr p then 1 else 0 := by
  funext s
  rcases s with i | q
  · simp [qv]
  · simp only [qv, Sum.elim_inr, Tp, Matrix.add_apply, Matrix.single_apply, Sum.inr.injEq]
    have h2 : ¬ (p.1.2 = q.1.1 ∧ p.1.1 = q.1.2) := fun hh => by
      have h := p.2; have h' := q.2; rw [hh.1, hh.2] at h; exact absurd h (not_lt.mpr h'.le)
    by_cases h : q = p
    · subst h; simp [ne_of_lt q.2, (ne_of_lt q.2).symm]
    · have h1 : ¬ (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := fun hh =>
        h (Subtype.ext (Prod.ext hh.1.symm hh.2.symm))
      simp [h1, h2, h]

lemma Tp_inner {d : ℕ} (p q : {p : Fin d × Fin d // p.1 < p.2}) :
    frobInner (Tp p) (Tp q) = 2 * (if p = q then 1 else 0) := by
  have h := qv_dot (Tp p) (Tp q) (Tp_szd p) (Tp_szd q)
  have e : qv (Tp p) ⬝ᵥ qv (Tp q) = if p = q then 1 else 0 := by
    rw [qv_Tp, qv_Tp]
    simp only [dotProduct, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp [eq_comm]
  rw [e] at h
  linarith

lemma card_pairs (d : ℕ) :
    (Fintype.card {p : Fin d × Fin d // p.1 < p.2} : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  have h := sum_lt_pairs (d := d) (fun i j => if i = j then 0 else 1)
    (fun i j => by by_cases h : i = j <;> simp [h, eq_comm]) (fun i => by simp)
  have h1 : ∑ p : {p : Fin d × Fin d // p.1 < p.2}, (if p.1.1 = p.1.2 then (0:ℝ) else 1) =
      (Fintype.card {p : Fin d × Fin d // p.1 < p.2} : ℝ) := by
    rw [Finset.sum_congr rfl (fun p _ => if_neg (ne_of_lt p.2))]
    simp
  have h2 : ∀ i : Fin d, ∑ j, (if i = j then (0:ℝ) else 1) = (d : ℝ) - 1 := by
    intro i
    have : ∑ j, (if i = j then (0:ℝ) else 1) = ∑ j, (1 - if i = j then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro j _; by_cases h : i = j <;> simp [h]
    rw [this, Finset.sum_sub_distrib]; simp
  rw [h1] at h
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- The `d²` term: the coordinate directions `Q_ij`. -/
lemma d2_lower (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1))
    (hd : 10 ≤ d) (hmd : m < d) (hα : 0 < α) (hα1 : α ≤ 1 / 2) (hσ : 0 < σ)
    (hD : InDesignClass d m N α D) (hPD : (fullFisherMat D σ).PosDef) :
    (d : ℝ) * ((d : ℝ) - 1) / 2 * (vN d m N α σ / 3) ^ 2 ≤
      frobInner (SigmaEff D σ) (SigmaEff D σ) := by
  obtain ⟨W, hW1, hWx⟩ := hD.2.2.1
  have h := family_lower d m N α σ D hd hmd hα hα1 hσ hD W hWx hPD Finset.univ Tp (fun _ => 1)
    (fun p _ => Tp_szd p)
    (fun p _ q _ hpq => by rw [Tp_inner]; simp [hpq])
    (fun p _ hp => by
      have := Tp_inner p p; rw [hp] at this; simp [frobInner] at this)
    (fun _ _ => one_pos)
    (fun p _ => by rw [one_mul]; exact frob_W_le W hW1 (Tp p))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_pairs] at h
  exact h

/-- An orthonormal complement of the columns of `W`. -/
lemma exists_compl {d k m : ℕ} (hkm : k + m = d) (W : Matrix (Fin d) (Fin k) ℝ)
    (hW : Wᵀ * W = 1) : ∃ U : Matrix (Fin d) (Fin m) ℝ, Uᵀ * U = 1 ∧ Uᵀ * W = 0 := by
  let v : Fin k ⊕ Fin m → EuclideanSpace ℝ (Fin d) :=
    Sum.elim (fun l => WithLp.toLp 2 (fun a => W a l)) (fun _ => 0)
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = Fintype.card (Fin k ⊕ Fin m) := by
    simp [hkm]
  have hv : Orthonormal ℝ ((Set.range (Sum.inl : Fin k → Fin k ⊕ Fin m)).restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨l, rfl⟩ := hi
    obtain ⟨l', rfl⟩ := hj
    show inner ℝ (v (Sum.inl l)) (v (Sum.inl l')) = _
    simp only [v, Sum.elim_inl, EuclideanSpace.inner_toLp_toLp, Subtype.mk.injEq, Sum.inl.injEq]
    have := congrFun (congrFun hW l) l'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    have key : ((fun a => W a l') ⬝ᵥ star fun a => W a l) = ∑ j, W j l * W j l' := by
      simp [dotProduct, mul_comm]
    rw [key, this]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (by subst h1; rfl) h2
    · have := congrArg Subtype.val h2; simp at this; exact absurd this h1
    · rfl
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  have hbo := orthonormal_iff_ite.mp b.orthonormal
  refine ⟨Matrix.of fun a c => (b (Sum.inr c)).ofLp a, ?_, ?_⟩
  · ext c c'
    have := hbo (Sum.inr c) (Sum.inr c')
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Sum.inr.injEq,
      Matrix.of_apply] at this ⊢
    rw [← this]
    simp [dotProduct, mul_comm]
  · ext c l
    have := hbo (Sum.inr c) (Sum.inl l)
    rw [hb (Sum.inl l) ⟨l, rfl⟩, EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [v, Sum.elim_inl, reduceCtorEq, if_false] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Matrix.of_apply]
    rw [← this]
    simp [dotProduct, mul_comm]

end HigherOrderId.Certify.Dev.E101
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.E101
open HigherOrderId.Certify

lemma DU_sum {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (c : SymIdx m → ℝ) :
    DU U (∑ p, c p • symBasis p) = DUmat U *ᵥ c := by
  funext a
  simp only [DU, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mulVec, dotProduct, DUmat]
  apply Finset.sum_congr rfl; intro p _; ring

lemma DUadj_symm {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (y : Fin d → ℝ) :
    (DUadj U y).IsSymm := by
  unfold DUadj Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.transpose_transpose, Matrix.mul_assoc]

lemma DUadj_eq {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (y : Fin d → ℝ) :
    DUadj U y = ∑ p, ((DUmat U)ᵀ *ᵥ y) p • symBasis p := by
  conv_lhs => rw [← Dev.B5.sym_expand (DUadj U y) (DUadj_symm U y)]
  apply Finset.sum_congr rfl; intro p _
  congr 1
  have e1 : ∀ i j, DUadj U y i j = ∑ a, U a i * y a * U a j := by
    intro i j
    simp only [DUadj]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  have e2 : ∀ a, DUmat U a p = ∑ k, ∑ l, U a k * symBasis p k l * U a l := by
    intro a; simp only [DUmat, DU]; exact Dev.E82.quad_gen U (symBasis p) a
  simp only [frobInner, e1, mulVec, dotProduct, Matrix.transpose_apply, e2, Finset.sum_mul]
  calc ∑ i, ∑ j, ∑ a, U a i * y a * U a j * symBasis p i j
      = ∑ i, ∑ a, ∑ j, U a i * y a * U a j * symBasis p i j := by
        apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, U a i * y a * U a j * symBasis p i j := Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _; ring

lemma dot_mulVec_mulVec {R S : Type*} [Fintype R] [Fintype S] (M : Matrix R S ℝ) (x z : S → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ z) = x ⬝ᵥ ((Mᵀ * M) *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Mᵀ, Matrix.vecMul_transpose]

/-- Singular value decomposition of `D_U`: orthonormal symmetric `B_j`, orthonormal `y_j`. -/
lemma svd_family {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hF : FullColRank U) :
    ∃ (B : SymIdx m → Matrix (Fin m) (Fin m) ℝ) (y : SymIdx m → Fin d → ℝ),
      (∀ j, (B j).IsSymm) ∧ (∀ i j, frobInner (B i) (B j) = if i = j then 1 else 0) ∧
      (∀ i j, y i ⬝ᵥ y j = if i = j then 1 else 0) ∧
      (∀ j, DU U (B j) = singVals U j • y j ∧ DUadj U (y j) = singVals U j • B j) := by
  obtain ⟨Wm, lam, hWW, _, hG, hlam⟩ := Dev.B5.G_spec U hF
  have hGW : (DUmat U)ᵀ * DUmat U * Wm = Wm * Matrix.diagonal lam := by
    rw [hG, Matrix.mul_assoc, hWW, Matrix.mul_one]
  set c : SymIdx m → SymIdx m → ℝ := fun j p => Wm p j with hc
  have hGc : ∀ j, ((DUmat U)ᵀ * DUmat U) *ᵥ c j = lam j • c j := by
    intro j; funext p
    have := congrFun (congrFun hGW p) j
    rw [Matrix.mul_diagonal] at this
    show ∑ q, ((DUmat U)ᵀ * DUmat U) p q * Wm q j = lam j * Wm p j
    rw [← Matrix.mul_apply, this]; ring
  have hcc : ∀ i j, c i ⬝ᵥ c j = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hWW i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    rw [← this]; rfl
  have hapos : ∀ j, 0 < singVals U j := fun j => Dev.E82.singVals_pos U hF j
  have hasq : ∀ j, singVals U j * singVals U j = lam j := by
    intro j; rw [(hlam j).2]; exact Real.mul_self_sqrt (hlam j).1.le
  refine ⟨fun j => ∑ p, c j p • symBasis p,
    fun j => (singVals U j)⁻¹ • (DUmat U *ᵥ c j), ?_, ?_, ?_, ?_⟩
  · intro j
    unfold Matrix.IsSymm
    rw [Matrix.transpose_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Matrix.transpose_smul, (Dev.B5.symBasis_symm p).eq]
  · intro i j
    rw [Dev.B5.frobInner_Mmap]
    exact hcc i j
  · intro i j
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [dot_mulVec_mulVec, hGc, dotProduct_smul, hcc, smul_eq_mul]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, ← hasq i]; have := (hapos i).ne'; field_simp
    · rw [if_neg h]; ring
  · intro j
    have ha := (hapos j).ne'
    constructor
    · rw [DU_sum, smul_smul, mul_inv_cancel₀ ha, one_smul]
    · rw [DUadj_eq, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGc, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro p _
      have e : ((singVals U j)⁻¹ • (lam j • c j)) p = singVals U j * c j p := by
        simp only [Pi.smul_apply, smul_eq_mul]; rw [← hasq j]; field_simp
      rw [e, smul_smul]

end HigherOrderId.Certify.Dev.E101
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.E101
open HigherOrderId.Certify

lemma card_sym_le (m : ℕ) : (Fintype.card (SymIdx m) : ℝ) ≤ (m : ℝ) ^ 2 := by
  rw [Dev.B2.card_symIdx, Nat.choose_two_right]
  have h : (m + 1) * (m + 1 - 1) / 2 ≤ m * m := by
    apply Nat.div_le_of_le_mul
    rw [Nat.add_sub_cancel]
    nlinarith
  have : (((m + 1) * (m + 1 - 1) / 2 : ℕ) : ℝ) ≤ ((m * m : ℕ) : ℝ) := by exact_mod_cast h
  rw [sq]; push_cast at this ⊢; linarith

/-- The `m⁶` term (`m ≥ 6`), through the near-null directions of Eqs. (84)–(87). -/
lemma m6_lower : ∃ c : ℝ, 0 < c ∧ ∀ (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1)),
    10 ≤ d → m < d → 6 ≤ m → 0 < α → α ≤ 1 / 2 → 0 < σ → InDesignClass d m N α D →
    (fullFisherMat D σ).PosDef →
    c * vN d m N α σ ^ 2 * (m : ℝ) ^ 6 ≤ frobInner (SigmaEff D σ) (SigmaEff D σ) := by
  obtain ⟨c84, hc84, h84⟩ := HigherOrderId.Certify.eq_84_87
  refine ⟨c84 ^ 2 / 9, by positivity, ?_⟩
  intro d m N α σ D hd hmd h6 hα hα1 hσ hD hPD
  obtain ⟨W, hW1, hWx⟩ := hD.2.2.1
  obtain ⟨U, hU, hUW⟩ := exists_compl (k := d - m) (m := m) (by omega) W hW1
  have hF : FullColRank U :=
    ((HigherOrderId.Certify.lemma_B_2 d m (d - m) hd (by omega) U W hU hW1 hUW).1).mp
      (fun Q hQ hQW => QW_zero d m N α σ D hd hmd hα hα1 hσ hD W hWx hPD Q hQ hQW)
  obtain ⟨B, y, hBs, hBo, hyo, hBy⟩ := svd_family U hF
  have H := h84 d m U hd hU h6 hF
  obtain ⟨I, hIcard, hm2, hIa⟩ := H.2.1
  obtain ⟨_, hr, hQ, horth, _, _, _, h8, h9, h10⟩ := H.2.2 I hIcard hIa B y
    (fun j _ => hBs j) (fun i _ j _ => hBo i j) (fun i _ j _ => hyo i j) (fun j _ => hBy j)
  have hapos : ∀ j, 0 < singVals U j := fun j => Dev.E82.singVals_pos U hF j
  set v := vN d m N α σ with hv
  -- the family lower bound
  have hfam := family_lower d m N α σ D hd hmd hα hα1 hσ hD W hWx hPD I
    (fun j => U * B j * Uᵀ +
      (-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j))
    (fun j => singVals U j ^ 2)
    (fun j hj => (hQ j hj).1)
    (fun i hi j hj hij => (horth i hi j hj hij).1)
    (fun j hj h0 => by
      have h1 := (hQ j hj).2.1
      have h2 := (hQ j hj).2.2.1
      rw [h0] at h1
      simp [frobNorm, frobInner] at h1
      rw [← h1] at h2; linarith)
    (fun j _ => by have := hapos j; positivity)
    (fun j hj => by
      have hQW : (U * B j * Uᵀ +
          (-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) * W =
          ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) * W := by
        rw [Matrix.add_mul, Matrix.mul_assoc (U * B j), hUW, Matrix.mul_zero, zero_add]
      rw [hQW]
      refine le_trans (frob_W_le W hW1 _) ?_
      rw [← Dev.E84.frobNorm_sq, ← Dev.E84.frobNorm_sq, (hr j hj).2.2.2, (hQ j hj).2.1,
        div_eq_mul_inv])
  -- numerics
  have hIpos : (0 : ℝ) < I.card := by
    have : (0 : ℝ) < (m : ℝ) ^ 2 / 4 := by
      have : (6 : ℝ) ≤ m := by exact_mod_cast h6
      positivity
    linarith
  have hIle : (I.card : ℝ) ≤ (m : ℝ) ^ 2 := by
    refine le_trans ?_ (card_sym_le m)
    exact_mod_cast Finset.card_le_univ I
  have hsum2 : c84 * (m : ℝ) ^ 4 ≤ ∑ j ∈ I, (singVals U j)⁻¹ ^ 2 := by linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := I) (f := fun j => (singVals U j)⁻¹ ^ 2)
  have hm0 : (0 : ℝ) < m := by
    have : (6 : ℝ) ≤ m := by exact_mod_cast h6
    linarith
  have hsum4 : c84 ^ 2 * (m : ℝ) ^ 6 ≤ ∑ j ∈ I, ((singVals U j)⁻¹ ^ 2) ^ 2 := by
    have hc4 : 0 ≤ c84 * (m : ℝ) ^ 4 := by positivity
    have e1 : (c84 * (m : ℝ) ^ 4) ^ 2 ≤ (∑ j ∈ I, (singVals U j)⁻¹ ^ 2) ^ 2 :=
      pow_le_pow_left₀ hc4 hsum2 2
    have hS4 : 0 ≤ ∑ j ∈ I, ((singVals U j)⁻¹ ^ 2) ^ 2 :=
      Finset.sum_nonneg (fun j _ => by positivity)
    have e2 : (I.card : ℝ) * ∑ j ∈ I, ((singVals U j)⁻¹ ^ 2) ^ 2 ≤
        (m : ℝ) ^ 2 * ∑ j ∈ I, ((singVals U j)⁻¹ ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hIle hS4
    have e3 : (m : ℝ) ^ 2 * (c84 ^ 2 * (m : ℝ) ^ 6) ≤
        (m : ℝ) ^ 2 * ∑ j ∈ I, ((singVals U j)⁻¹ ^ 2) ^ 2 := by
      have : (m : ℝ) ^ 2 * (c84 ^ 2 * (m : ℝ) ^ 6) = (c84 * (m : ℝ) ^ 4) ^ 2 := by ring
      rw [this]; linarith
    exact le_of_mul_le_mul_left e3 (by positivity)
  have hterm : ∀ j ∈ I, (v / (3 * singVals U j ^ 2)) ^ 2 =
      v ^ 2 / 9 * ((singVals U j)⁻¹ ^ 2) ^ 2 := by
    intro j _
    have := (hapos j).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hfam
  have hv2 : 0 ≤ v ^ 2 / 9 := by positivity
  calc c84 ^ 2 / 9 * v ^ 2 * (m : ℝ) ^ 6 = v ^ 2 / 9 * (c84 ^ 2 * (m : ℝ) ^ 6) := by ring
    _ ≤ v ^ 2 / 9 * ∑ j ∈ I, ((singVals U j)⁻¹ ^ 2) ^ 2 := mul_le_mul_of_nonneg_left hsum4 hv2
    _ ≤ _ := hfam

end HigherOrderId.Certify.Dev.E101
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.E101
open HigherOrderId.Certify

/-- `m ≤ m_d` gives `m(m+1) ≤ 2d`, hence `m < d`. -/
lemma m_bound (d m : ℕ) (hd : 10 ≤ d) (hm : m ≤ md d) : m * (m + 1) ≤ 2 * d ∧ m < d := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt (8 * (d : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hx : 0 ≤ (Real.sqrt (8 * (d : ℝ) + 1) - 1) / 2 := by linarith
  have h1 : (m : ℝ) ≤ (Real.sqrt (8 * (d : ℝ) + 1) - 1) / 2 :=
    le_trans (Nat.cast_le.mpr hm) (Nat.floor_le hx)
  have h2 : 2 * (m : ℝ) + 1 ≤ Real.sqrt (8 * (d : ℝ) + 1) := by linarith
  have h3 : (2 * (m : ℝ) + 1) ^ 2 ≤ 8 * (d : ℝ) + 1 := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have h4 : ((m * (m + 1) : ℕ) : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by push_cast; nlinarith
  have h5 : m * (m + 1) ≤ 2 * d := by exact_mod_cast h4
  refine ⟨h5, ?_⟩
  by_contra hc
  push Not at hc
  nlinarith

lemma sqrt_prod (a v S : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v) (hS : 0 ≤ S) :
    Real.sqrt (a ^ 2 * v ^ 2 * S) = a * v * Real.sqrt S := by
  rw [Real.sqrt_mul (by positivity), ← mul_pow, Real.sqrt_sq (by positivity)]

lemma sum_sub_le {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (g : α → ℝ)
    (hg : ∀ x, 0 ≤ g x) : ∑ p : {x // P x}, g p.1 ≤ ∑ x, g x := by
  have h1 : ∑ p : {x // P x}, g p.1 = ∑ x ∈ Finset.univ.filter P, g x :=
    (Finset.sum_subtype (Finset.univ.filter P) (by intro x; simp) g).symm
  rw [h1]
  exact Finset.sum_le_univ_sum_of_nonneg hg

lemma GammaEntry_symm {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (v : ℝ) (a b : Fin d × Fin d) : GammaEntry U V v b a = GammaEntry U V v a b := by
  simp only [GammaEntry, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply]
  congr 1; apply Finset.sum_congr rfl; intro c _; ring

lemma frob_GammaTheta {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (σ : ℝ) (N : ℕ) (v : ℝ) :
    frobInner (GammaTheta U V σ N v) (GammaTheta U V σ N v) ≤
      (d : ℝ) * (σ ^ 2 / (N : ℝ)) ^ 2 + (GammaEntry U V v * GammaEntry U V v).trace := by
  have htr : (GammaEntry U V v * GammaEntry U V v).trace =
      ∑ a, ∑ b, GammaEntry U V v a b * GammaEntry U V v a b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
    rw [GammaEntry_symm U V v a b]
  have hpairs : ∑ p : {p : Fin d × Fin d // p.1 < p.2}, ∑ q : {p : Fin d × Fin d // p.1 < p.2},
      GammaEntry U V v p.1 q.1 * GammaEntry U V v p.1 q.1 ≤
      ∑ a, ∑ b, GammaEntry U V v a b * GammaEntry U V v a b := by
    refine le_trans (Finset.sum_le_sum fun p _ => sum_sub_le (fun q : Fin d × Fin d => q.1 < q.2)
      (fun b => GammaEntry U V v p.1 b * GammaEntry U V v p.1 b) (fun b => mul_self_nonneg _)) ?_
    exact sum_sub_le (fun q : Fin d × Fin d => q.1 < q.2)
      (fun a => ∑ b, GammaEntry U V v a b * GammaEntry U V v a b)
      (fun a => Finset.sum_nonneg fun b _ => mul_self_nonneg _)
  have hdiag : ∑ i : Fin d, ∑ i' : Fin d, (if i = i' then σ ^ 2 / (N : ℝ) else 0) *
      (if i = i' then σ ^ 2 / (N : ℝ) else 0) = (d : ℝ) * (σ ^ 2 / (N : ℝ)) ^ 2 := by
    simp [ite_mul, sq]
  unfold frobInner
  simp only [Fintype.sum_sum_type, GammaTheta, mul_zero, Finset.sum_const_zero, add_zero,
    zero_add]
  rw [hdiag, htr]
  linarith

/-- Part 2 of Eq. (101): the explicit estimator's covariance. -/
lemma part2 : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (d m N : ℕ) (α σ : ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
      (V : Matrix (Fin d) (Fin (d - m)) ℝ), 10 ≤ d → m ≤ md d → 0 < α → α ≤ 1 / 2 →
      0 < σ → (d - m + 1) ∣ N → 0 < N / (d - m + 1) →
      Uᵀ * U = 1 → Vᵀ * V = 1 → Uᵀ * V = 0 →
      (1 ≤ m → ∃ ι : FrameRows m ↪ Fin d, U = Uw ι ((m : ℝ) ^ ((1 : ℝ) / 4))) →
      frobNorm (GammaTheta U V σ N (vN d m N α σ)) ≤
        C₀ * vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6) := by
  obtain ⟨c₁, C₁, c₂, C₂, _, _, _, hC₂, hB4⟩ := HigherOrderId.Certify.lemma_B_4
  refine ⟨3 + 3 * C₂, by positivity, ?_⟩
  intro d m N α σ U V hd hm hα hα1 hσ hdiv hpos hU hV hUV hUw
  obtain ⟨_, hmd⟩ := m_bound d m hd hm
  have hN := N_pos d m N hpos
  set v := vN d m N α σ with hvdef
  have hv := vN_pos d m N α σ hmd hα hσ hN
  -- full column rank and the spectral sum
  have hspec : FullColRank U ∧ ∑ j, (singVals U j)⁻¹ ^ 4 ≤ 2 * C₂ * (m : ℝ) ^ 6 := by
    rcases Nat.eq_zero_or_pos m with h0 | h1
    · subst h0
      refine ⟨fun B _ _ => by ext i; exact i.elim0, ?_⟩
      rw [Finset.sum_eq_zero (fun j _ => j.1.1.elim0)]; simp
    · obtain ⟨ι, hι⟩ := hUw h1
      subst hι
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
      have hw1 : (1 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hm1 (by norm_num)
      have hwm : (m : ℝ) ^ ((1 : ℝ) / 4) ≤ m := by
        have := Real.rpow_le_rpow_of_exponent_le hm1 (show (1 : ℝ) / 4 ≤ 1 by norm_num)
        rwa [Real.rpow_one] at this
      have hw4 : ((m : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = m := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have H := hB4 d m ι _ hd h1 hw1 hwm
      refine ⟨H.1, ?_⟩
      have h := H.2.2.2.2
      rw [hw4] at h
      have e : (m : ℝ) ^ 6 + (m : ℝ) ^ 7 / m = 2 * (m : ℝ) ^ 6 := by
        field_simp; ring
      rw [e] at h; linarith
  have hB5 := (HigherOrderId.Certify.lemma_B_5 d m (d - m) hd (by omega) U V hU hV hUV
    hspec.1 v hv).2.2.2.2
  have hcardR : (Fintype.card (RestIdx m (d - m)) : ℝ) ≤ (d : ℝ) ^ 2 := by
    have h1 : Fintype.card (RestIdx m (d - m)) ≤ m * (d - m) + (d - m) * (d - m) := by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      have := Fintype.card_subtype_le (fun p : Fin (d - m) × Fin (d - m) => p.1 ≤ p.2)
      rw [Fintype.card_prod, Fintype.card_fin] at this
      omega
    have h2 : m * (d - m) + (d - m) * (d - m) = d * (d - m) := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' hmd.le]
    have h3 : d * (d - m) ≤ d * d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have : Fintype.card (RestIdx m (d - m)) ≤ d * d := by omega
    have : ((Fintype.card (RestIdx m (d - m)) : ℕ) : ℝ) ≤ ((d * d : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this; nlinarith
  have hcardS : (0 : ℝ) ≤ Fintype.card (SymIdx m) := Nat.cast_nonneg _
  have hσN : σ ^ 2 / (N : ℝ) ≤ v := by
    have hk : (1 : ℝ) ≤ (d : ℝ) - m := by
      have : m + 1 ≤ d := hmd
      have : ((m + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast this
      push_cast at this; linarith
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [hvdef, vN, div_le_div_iff₀ hNr (by positivity)]
    have ha2 : α ^ 2 ≤ 1 := by nlinarith
    have : σ ^ 2 * (N : ℝ) * α ^ 2 ≤ σ ^ 2 * ((d : ℝ) - m) * N := by
      have h1 : σ ^ 2 * (N : ℝ) * α ^ 2 ≤ σ ^ 2 * (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left ha2 (by positivity)
      have h2 : σ ^ 2 * (N : ℝ) * 1 ≤ σ ^ 2 * (N : ℝ) * ((d : ℝ) - m) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      linarith
    linarith
  have hσN0 : 0 ≤ σ ^ 2 / (N : ℝ) := by positivity
  have hd1 : (1 : ℝ) ≤ d := by
    have : (10 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hF := frob_GammaTheta U V σ N v
  -- assemble
  set S := (d : ℝ) ^ 2 + (m : ℝ) ^ 6 with hS
  have hm6 : (0 : ℝ) ≤ (m : ℝ) ^ 6 := by positivity
  have hb1 : (d : ℝ) * (σ ^ 2 / (N : ℝ)) ^ 2 ≤ (d : ℝ) ^ 2 * v ^ 2 := by
    have : (σ ^ 2 / (N : ℝ)) ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hσN0 hσN 2
    have h2 : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    calc (d : ℝ) * (σ ^ 2 / (N : ℝ)) ^ 2 ≤ (d : ℝ) * v ^ 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ (d : ℝ) ^ 2 * v ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
  have hb2 : (GammaEntry U V v * GammaEntry U V v).trace ≤
      4 * v ^ 2 * ((d : ℝ) ^ 2 + 2 * C₂ * (m : ℝ) ^ 6) := by
    refine le_trans hB5 ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [hspec.2]
  have htot : frobInner (GammaTheta U V σ N v) (GammaTheta U V σ N v) ≤
      (3 + 3 * C₂) ^ 2 * v ^ 2 * S := by
    have hv2 : 0 ≤ v ^ 2 := by positivity
    have e : (3 + 3 * C₂) ^ 2 * v ^ 2 * S - ((d : ℝ) ^ 2 * v ^ 2 +
        4 * v ^ 2 * ((d : ℝ) ^ 2 + 2 * C₂ * (m : ℝ) ^ 6)) =
        v ^ 2 * ((4 + 18 * C₂ + 9 * C₂ ^ 2) * (d : ℝ) ^ 2 +
          (9 + 10 * C₂ + 9 * C₂ ^ 2) * (m : ℝ) ^ 6) := by
      rw [hS]; ring
    have : 0 ≤ v ^ 2 * ((4 + 18 * C₂ + 9 * C₂ ^ 2) * (d : ℝ) ^ 2 +
          (9 + 10 * C₂ + 9 * C₂ ^ 2) * (m : ℝ) ^ 6) := by positivity
    linarith
  unfold frobNorm
  rw [← sqrt_prod _ _ _ (by positivity) hv.le (by positivity)]
  exact Real.sqrt_le_sqrt htot

end HigherOrderId.Certify.Dev.E101
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.E101
open HigherOrderId.Certify

/-- Part 1 of Eq. (101) with an explicit squared constant. -/
lemma part1 : ∃ κ : ℝ, 0 < κ ∧
    ∀ (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1)), 10 ≤ d → m ≤ md d → 0 < α →
      α ≤ 1 / 2 → 0 < σ → InDesignClass d m N α D → (fullFisherMat D σ).PosDef →
      Real.sqrt κ * vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6) ≤
        frobNorm (SigmaEff D σ) := by
  obtain ⟨c, hc, hm6⟩ := m6_lower
  refine ⟨min (1 / 3160) (c / 2), lt_min (by norm_num) (by positivity), ?_⟩
  intro d m N α σ D hd hm hα hα1 hσ hD hPD
  obtain ⟨_, hmd⟩ := m_bound d m hd hm
  have hv := vN_pos d m N α σ hmd hα hσ (N_pos d m N hD.2.2.2.2.1)
  set v := vN d m N α σ with hvdef
  set κ := min (1 / 3160) (c / 2) with hκ
  have hκ0 : 0 ≤ κ := le_min (by norm_num) (by positivity)
  have hκ1 : κ ≤ 1 / 3160 := min_le_left _ _
  have hκ2 : κ ≤ c / 2 := min_le_right _ _
  set F := frobInner (SigmaEff D σ) (SigmaEff D σ) with hF
  have hd10 : (10 : ℝ) ≤ d := by exact_mod_cast hd
  have hv2 : 0 ≤ v ^ 2 := by positivity
  have hd2 : (d : ℝ) ^ 2 * v ^ 2 / 20 ≤ F := by
    have h := d2_lower d m N α σ D hd hmd hα hα1 hσ hD hPD
    have : (d : ℝ) ^ 2 * v ^ 2 / 20 ≤ (d : ℝ) * ((d : ℝ) - 1) / 2 * (v / 3) ^ 2 := by
      have e : (d : ℝ) * ((d : ℝ) - 1) / 2 * (v / 3) ^ 2 - (d : ℝ) ^ 2 * v ^ 2 / 20 =
          v ^ 2 * ((d : ℝ) * ((d : ℝ) - 10)) / 180 := by ring
      have : 0 ≤ v ^ 2 * ((d : ℝ) * ((d : ℝ) - 10)) / 180 := by
        apply div_nonneg _ (by norm_num)
        apply mul_nonneg hv2
        apply mul_nonneg (by linarith) (by linarith)
      linarith
    linarith
  have hm6' : (0 : ℝ) ≤ (m : ℝ) ^ 6 := by positivity
  have hmain : κ * v ^ 2 * ((d : ℝ) ^ 2 + (m : ℝ) ^ 6) ≤ F := by
    rcases le_or_gt m 5 with h5 | h6
    · have hm5 : (m : ℝ) ≤ 5 := by exact_mod_cast h5
      have : (m : ℝ) ^ 6 ≤ 5 ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hm5 6
      have hS : (d : ℝ) ^ 2 + (m : ℝ) ^ 6 ≤ 158 * (d : ℝ) ^ 2 := by nlinarith
      calc κ * v ^ 2 * ((d : ℝ) ^ 2 + (m : ℝ) ^ 6) ≤ (1 / 3160) * v ^ 2 * (158 * (d : ℝ) ^ 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hκ1 hv2) hS (by positivity)
              (by positivity)
        _ = (d : ℝ) ^ 2 * v ^ 2 / 20 := by ring
        _ ≤ F := hd2
    · have h := hm6 d m N α σ D hd hmd h6 hα hα1 hσ hD hPD
      have e1 : κ * v ^ 2 * (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * v ^ 2 / 40 := by
        have : κ * (v ^ 2 * (d : ℝ) ^ 2) ≤ (1 / 40) * (v ^ 2 * (d : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
      have e2 : κ * v ^ 2 * (m : ℝ) ^ 6 ≤ c / 2 * v ^ 2 * (m : ℝ) ^ 6 := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ2 hv2) hm6'
      have : κ * v ^ 2 * ((d : ℝ) ^ 2 + (m : ℝ) ^ 6) =
          κ * v ^ 2 * (d : ℝ) ^ 2 + κ * v ^ 2 * (m : ℝ) ^ 6 := by ring
      rw [this]
      have : c / 2 * v ^ 2 * (m : ℝ) ^ 6 = (c * v ^ 2 * (m : ℝ) ^ 6) / 2 := by ring
      linarith
  unfold frobNorm
  rw [← sqrt_prod _ _ _ (Real.sqrt_nonneg _) hv.le (by positivity),
    Real.sq_sqrt hκ0]
  exact Real.sqrt_le_sqrt hmain

end HigherOrderId.Certify.Dev.E101

namespace HigherOrderId.Certify
open HigherOrderId.Certify.Dev.E101 in
theorem chk_eq_101 :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      (∀ (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1)), 10 ≤ d → m ≤ md d → 0 < α →
        α ≤ 1 / 2 → 0 < σ → InDesignClass d m N α D → (fullFisherMat D σ).PosDef →
        c₀ * vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6) ≤ frobNorm (SigmaEff D σ)) ∧
      (∀ (d m N : ℕ) (α σ : ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
          (V : Matrix (Fin d) (Fin (d - m)) ℝ), 10 ≤ d → m ≤ md d → 0 < α → α ≤ 1 / 2 →
        0 < σ → (d - m + 1) ∣ N → 0 < N / (d - m + 1) →
        Uᵀ * U = 1 → Vᵀ * V = 1 → Uᵀ * V = 0 →
        (1 ≤ m → ∃ ι : FrameRows m ↪ Fin d, U = Uw ι ((m : ℝ) ^ ((1 : ℝ) / 4))) →
        frobNorm (GammaTheta U V σ N (vN d m N α σ)) ≤
          C₀ * vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6)) := by
  obtain ⟨κ, hκ, h1⟩ := part1
  obtain ⟨C₀, hC₀, h2⟩ := part2
  exact ⟨Real.sqrt κ, C₀, Real.sqrt_pos.mpr hκ, hC₀, h1, h2⟩

end HigherOrderId.Certify
end

theorem solution : type_of% @HigherOrderId.Certify.chk_eq_101 := @HigherOrderId.Certify.chk_eq_101
