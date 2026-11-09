-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T14:04:14.483107+00:00
-- url     : https://prove2.me/submissions/4e7dfc64-c9e1-4d22-83a9-6560646e187a

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E084
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E149
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound1867_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : average (f ∘ e) = average f := by
  simp only [average, Fintype.card_congr e, Function.comp_apply, e.sum_comp]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_add (f g : ι → ℝ) :
    average (fun i => f i + g i) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

theorem sum_split_embedding (e : A ↪ B) (f : B → V) :
    (∑ b, f b) = (∑ a, f (e a)) + ∑ b : {b // b ∉ Set.range e}, f b := by
  classical
  let E : A ⊕ {b // b ∉ Set.range e} ≃ B :=
    (e.toEquivRange.sumCongr (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range e))
  have h := E.sum_comp f
  simpa [E, Fintype.sum_sum_type, Equiv.trans_apply, Equiv.sumCongr_apply] using h.symm

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

theorem sum_samples_split {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin p ↪ B, ∑ b, f e b) =
      (∑ e : Fin p ↪ B, ∑ j, f e (e j)) +
      ∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0) := by
  classical
  calc
    _ = ∑ e : Fin p ↪ B,
        ((∑ j, f e (e j)) + ∑ b : {b // b ∉ Set.range e}, f e b) := by
      apply Finset.sum_congr rfl
      intro e _
      exact sum_split_embedding e (f e)
    _ = _ := by rw [Finset.sum_add_distrib, sum_injective_extension]

theorem sum_contraction {p : ℕ} (f : (Fin p ↪ B) → B → V)
    (h : ∀ e, ∑ b, f e b = 0) :
    (∑ j : Fin p, ∑ e : Fin p ↪ B, f e (e j)) +
      (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) = 0 := by
  classical
  rw [Finset.sum_comm]
  rw [← sum_samples_split]
  simp [h]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SamplingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

theorem unused_card {p n : ℕ} (e : Fin p ↪ Fin n)
    [Fintype {i // i ∉ Set.range e}] :
    Fintype.card {i // i ∉ Set.range e} = n - p := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {i // i ∈ Set.range e} = p := by
    rw [Fintype.card_range, Fintype.card_fin]
  rw [hr, Fintype.card_fin]

theorem embedding_succ_card (p n : ℕ) :
    Fintype.card (Fin (p + 1) ↪ Fin n) =
      Fintype.card (Fin p ↪ Fin n) * (n - p) := by
  rw [Fintype.card_congr (Equiv.embeddingFinSucc p (Fin n)), Fintype.card_sigma]
  simp only [unused_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem sum_dropFirst {p n : ℕ} (f : (Fin p ↪ Fin n) → ℝ) :
    (∑ e : Fin (p + 1) ↪ Fin n, f (dropFirst e)) =
      (n - p : ℕ) * ∑ e, f e := by
  have hs := sum_injective_extension (fun e (_ : Fin n) => f e)
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin, Fintype.card_fin]

/-- Deleting a coordinate of a uniform injection leaves a uniform injection. -/
theorem average_dropFirst {p n : ℕ} (hp : p < n) (f : (Fin p ↪ Fin n) → ℝ) :
    average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e)) = average f := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  unfold average
  rw [embedding_succ_card, Nat.cast_mul, sum_dropFirst, mul_inv_rev]
  calc
    _ = (((n - p : ℕ) : ℝ)⁻¹ * (n - p : ℕ)) *
        ((Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ * ∑ e, f e) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

/-- The normalized counting identity used for an order-one contraction.
At most n rows are sampled; the saturated boundary case is separate. -/
theorem average_contraction {p n : ℕ} (hp : p < n)
    (f : (Fin p ↪ Fin n) → Fin n → ℝ) (h : ∀ e, ∑ b, f e b = 0) :
    ((n - p : ℕ) : ℝ) *
      average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e) (e 0)) +
      (∑ j : Fin p, average (fun e : Fin p ↪ Fin n => f e (e j))) = 0 := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  have hc : ((n - p : ℕ) : ℝ) * (Fintype.card (Fin (p + 1) ↪ Fin n) : ℝ)⁻¹ =
      (Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ := by
    rw [embedding_succ_card, Nat.cast_mul, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hs := sum_contraction f h
  simp only [average]
  rw [← mul_assoc, hc, ← Finset.mul_sum, ← mul_add]
  rw [add_comm] at hs
  rw [hs, mul_zero]

/-- At saturation the old labels exhaust the population, so only the occupied
contractions occur. This statement never defines a seven-row moment. -/
theorem saturated_average_contraction (n : ℕ)
    (f : (Fin n ↪ Fin n) → Fin n → ℝ) (h : ∀ e, ∑ b, f e b = 0) :
    (∑ j : Fin n, average (fun e : Fin n ↪ Fin n => f e (e j))) = 0 := by
  simp only [average]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs : (∑ e : Fin n ↪ Fin n, ∑ j : Fin n, f e (e j)) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have he : Function.Bijective e :=
      ⟨e.injective, Finite.surjective_of_injective e.injective⟩
    rw [he.sum_comp]
    exact h e
  rw [hs, mul_zero]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

/-- The seven-row boundary equation. All six terms are moments of six-row
matrices. There is no term for sampling seven distinct labels from six. -/
theorem injectiveMoment_seven_row_boundary {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin 7) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    (∑ j : Fin 6, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.saturated_average_contraction 6
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord => ∑ j : Fin 6,
      average (fun ρ : Fin 6 ↪ Coord => contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_occupied hH,
    contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4140 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4140 = injectiveMoment H raw4140step0 := by
      have heq : raw4140step0 = (fun i j => raw4140 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4140 permutation18 permutation7
    _ = injectiveMoment H node207 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

theorem canonical4145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4145 = injectiveMoment H node215 := by
  rfl

theorem canonical4147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4147 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw4147 = injectiveMoment H raw4147step0 := by
      have heq : raw4147step0 = -raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4147).symm
    injectiveMoment H raw4147step0 = injectiveMoment H raw4147step1 := by
      have heq : raw4147step1 = (fun i j => raw4147step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4147step0 permutation8 permutation4
    _ = injectiveMoment H node37 := by rfl

theorem canonical4159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4159 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4159 = injectiveMoment H raw4159step0 := by
      have heq : raw4159step0 = -raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4159).symm
    injectiveMoment H raw4159step0 = injectiveMoment H raw4159step1 := by
      have heq : raw4159step1 = (fun i j => raw4159step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4159step0 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6859 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6859 = injectiveMoment H node1867 := by
  calc
    injectiveMoment H raw6859 = injectiveMoment H raw6859step0 := by
      have heq : raw6859step0 = (fun i j => raw6859 (permutation258 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6859 permutation258 permutation4
    _ = injectiveMoment H node1867 := by rfl

theorem canonical6865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6865 = injectiveMoment H node62 := by
  rfl

theorem canonical6868 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6868 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6868 = injectiveMoment H raw6868step0 := by
      have heq : raw6868step0 = (fun i j => raw6868 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6868 permutation11 permutation3
    _ = injectiveMoment H node285 := by rfl

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
  rfl

theorem canonical6872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6872 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6872 = injectiveMoment H raw6872step0 := by
      have heq : raw6872step0 = (fun i j => raw6872 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6872 permutation13 permutation3
    _ = injectiveMoment H node285 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical266
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8543 = injectiveMoment H node1854 := by
  calc
    injectiveMoment H raw8543 = injectiveMoment H raw8543step0 := by
      have heq : raw8543step0 = (fun i j => raw8543 (permutation277 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8543 permutation277 permutation4
    _ = injectiveMoment H node1854 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8703 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw8703 = injectiveMoment H raw8703step0 := by
      have hz : ∀ j, raw8703 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8703step0 = (fun i j => raw8703 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8703 permutation221 hz
    injectiveMoment H raw8703step0 = injectiveMoment H raw8703step1 := by
      have heq : raw8703step1 = (fun i j => raw8703step0 (permutation110 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8703step0 permutation110 permutation4
    _ = injectiveMoment H node559 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical274
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8770 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw8770 = injectiveMoment H raw8770step0 := by
      have hz : ∀ j, raw8770 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8770step0 = (fun i j => raw8770 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8770 permutation241 hz
    injectiveMoment H raw8770step0 = injectiveMoment H raw8770step1 := by
      have heq : raw8770step1 = (fun i j => raw8770step0 (permutation110 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8770step0 permutation110 permutation4
    _ = injectiveMoment H node559 := by rfl

theorem canonical8773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8773 = injectiveMoment H node1405 := by
  calc
    injectiveMoment H raw8773 = injectiveMoment H raw8773step0 := by
      have heq : raw8773step0 = (fun i j => raw8773 (permutation277 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8773 permutation277 permutation4
    _ = injectiveMoment H node1405 := by rfl

theorem canonical8774 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8774 = injectiveMoment H node1887 := by
  calc
    injectiveMoment H raw8774 = injectiveMoment H raw8774step0 := by
      have heq : raw8774step0 = (fun i j => raw8774 (permutation279 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8774 permutation279 permutation4
    _ = injectiveMoment H node1887 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical211
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6764 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6764 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6764 = injectiveMoment H raw6764step0 := by
      have heq : raw6764step0 = (fun i j => raw6764 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6764 permutation18 permutation7
    _ = injectiveMoment H node176 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2778 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw2778 = injectiveMoment H raw2778step0 := by
      have hz : ∀ j, raw2778 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw2778step0 = (fun i j => raw2778 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2778 permutation57 hz
    _ = injectiveMoment H node188 := by rfl

theorem canonical2781 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2781 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2781 = injectiveMoment H raw2781step0 := by
      have heq : raw2781step0 = raw2781.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2781).symm
    injectiveMoment H raw2781step0 = injectiveMoment H raw2781step1 := by
      have hz : ∀ i, raw2781step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw2781step1 = (fun i j => raw2781step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2781step0 permutation15 hz
    injectiveMoment H raw2781step1 = injectiveMoment H raw2781step2 := by
      have heq : raw2781step2 = (fun i j => raw2781step1 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2781step1 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2787 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2787 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw2787 = injectiveMoment H raw2787step0 := by
      have heq : raw2787step0 = (fun i j => raw2787 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2787 permutation39 permutation3
    _ = injectiveMoment H node559 := by rfl

theorem canonical2809 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2809 = injectiveMoment H node573 := by
  rfl

theorem canonical2813 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2813 = injectiveMoment H node575 := by
  rfl

theorem canonical2814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2814 = injectiveMoment H node575 := by
  calc
    injectiveMoment H raw2814 = injectiveMoment H raw2814step0 := by
      have heq : raw2814step0 = (fun i j => raw2814 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2814 permutation34 permutation3
    _ = injectiveMoment H node575 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2817 = injectiveMoment H node180 := by
  rfl

theorem canonical2818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2818 = injectiveMoment H node559 := by
  calc
    injectiveMoment H raw2818 = injectiveMoment H raw2818step0 := by
      have heq : raw2818step0 = (fun i j => raw2818 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2818 permutation45 permutation3
    _ = injectiveMoment H node559 := by rfl

theorem canonical2819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2819 = injectiveMoment H node573 := by
  calc
    injectiveMoment H raw2819 = injectiveMoment H raw2819step0 := by
      have heq : raw2819step0 = (fun i j => raw2819 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2819 permutation37 permutation3
    _ = injectiveMoment H node573 := by rfl

theorem canonical2820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2820 = injectiveMoment H node181 := by
  rfl

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2842 = injectiveMoment H node185 := by
  rfl

theorem canonical2843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2843 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw2843 = injectiveMoment H raw2843step0 := by
      have heq : raw2843step0 = (fun i j => raw2843 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2843 permutation10 permutation3
    _ = injectiveMoment H node185 := by rfl

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

theorem canonical2847 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2847 = injectiveMoment H node187 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2848 = injectiveMoment H node188 := by
  rfl

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
  rfl

theorem canonical2851 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2851 = injectiveMoment H node190 := by
  rfl

theorem canonical2853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2853 = injectiveMoment H node38 := by
  rfl

theorem canonical2860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2860 = injectiveMoment H node40 := by
  rfl

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

theorem canonical2864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2864 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2864 = injectiveMoment H raw2864step0 := by
      have heq : raw2864step0 = raw2864.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2864).symm
    injectiveMoment H raw2864step0 = injectiveMoment H raw2864step1 := by
      have heq : raw2864step1 = (fun i j => raw2864step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2864step0 permutation6 permutation7
    _ = injectiveMoment H node63 := by rfl

theorem canonical2865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2865 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw2865 = injectiveMoment H raw2865step0 := by
      have heq : raw2865step0 = (fun i j => raw2865 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2865 permutation4 permutation3
    _ = injectiveMoment H node40 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical5459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5459 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw5459 = injectiveMoment H raw5459step0 := by
      have heq : raw5459step0 = raw5459.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5459).symm
    injectiveMoment H raw5459step0 = injectiveMoment H raw5459step1 := by
      have heq : raw5459step1 = (fun i j => raw5459step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5459step0 permutation5 permutation2
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5550 = injectiveMoment H node53 := by
  rfl

theorem canonical5552 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5552 = injectiveMoment H node54 := by
  rfl

theorem canonical5556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5556 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw5556 = injectiveMoment H raw5556step0 := by
      have heq : raw5556step0 = raw5556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5556).symm
    injectiveMoment H raw5556step0 = injectiveMoment H raw5556step1 := by
      have heq : raw5556step1 = (fun i j => raw5556step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5556step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5986 = injectiveMoment H node59 := by
  rfl

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical7988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7988 = injectiveMoment H node2 := by
  calc
    injectiveMoment H raw7988 = injectiveMoment H raw7988step0 := by
      have hz : ∀ i, raw7988 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw7988step0 = (fun i j => raw7988 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7988 permutation3 hz
    _ = injectiveMoment H node2 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8005 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8005 = injectiveMoment H raw8005step0 := by
      have hz : ∀ i, raw8005 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8005step0 = (fun i j => raw8005 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8005 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw840 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw840 = injectiveMoment H raw840step0 := by
      have heq : raw840step0 = (fun i j => raw840 (permutation5 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw840 permutation5 permutation7
    _ = injectiveMoment H node43 := by rfl

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw928 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw928 = injectiveMoment H raw928step0 := by
      have heq : raw928step0 = raw928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw928).symm
    injectiveMoment H raw928step0 = injectiveMoment H raw928step1 := by
      have heq : raw928step1 = (fun i j => raw928step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw928step0 permutation6 permutation2
    _ = injectiveMoment H node8 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

theorem sound3 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node3 = Sparse.eval value3 (momentVector H) := by
  have hc : momentVector H 2 = injectiveMoment H node3 := rfl
  simp [value3, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

theorem sound10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node10 = Sparse.eval value10 (momentVector H) := by
  have heq : pivotMatrix10 = (fun u v => node10 (pivotPermutation10 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node10 = injectiveMoment H pivotMatrix10 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix10 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix10 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (0 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (1 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node10 + (injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value10, value3, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound18 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node18 = Sparse.eval value18 (momentVector H) := by
  have hc : momentVector H 60 = injectiveMoment H node18 := rfl
  simp [value18, Sparse.eval, hc]

theorem sound21 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node21 = Sparse.eval value21 (momentVector H) := by
  have hc : momentVector H 34 = injectiveMoment H node21 := rfl
  simp [value21, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound33 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node33 = Sparse.eval value33 (momentVector H) := by
  have hc : momentVector H 82 = injectiveMoment H node33 := rfl
  simp [value33, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound38 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node38 = Sparse.eval value38 (momentVector H) := by
  have hc : momentVector H 128 = injectiveMoment H node38 := rfl
  simp [value38, Sparse.eval, hc]

theorem sound40 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node40 = Sparse.eval value40 (momentVector H) := by
  have hc : momentVector H 52 = injectiveMoment H node40 := rfl
  simp [value40, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound53 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node53 = Sparse.eval value53 (momentVector H) := by
  have heq : pivotMatrix53 = (fun u v => node53 (pivotPermutation53 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node53 = injectiveMoment H pivotMatrix53 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix53 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix53 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node53 + (injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value53, value3, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound54 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node54 = Sparse.eval value54 (momentVector H) := by
  have heq : pivotMatrix54 = (fun u v => node54 (pivotPermutation54 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node54 = injectiveMoment H pivotMatrix54 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix54 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix54 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix54 (0 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix54 (0 : Fin 2) = raw7988 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7988 hH).trans (sound2 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix54 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix54 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node54 + (injectiveMoment H (mergeFirst pivotMatrix54 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix54 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value54, value2, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound58 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node58 = Sparse.eval value58 (momentVector H) := by
  have heq : pivotMatrix58 = (fun u v => node58 (pivotPermutation58 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node58 = injectiveMoment H pivotMatrix58 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix58 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix58 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node58 + (injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value58, value10, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound59 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node59 = Sparse.eval value59 (momentVector H) := by
  have heq : pivotMatrix59 = (fun u v => node59.transpose (pivotPermutation59 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node59 = injectiveMoment H pivotMatrix59 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix59 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix59 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (0 : Fin 2) = raw928 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical928 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (1 : Fin 2) = raw5459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5459 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node59 + (injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value59, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw320 = injectiveMoment H node18 := by
  rfl

theorem canonical325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw325 = injectiveMoment H node90 := by
  rfl

theorem canonical326 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw326 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw326 = injectiveMoment H raw326step0 := by
      have heq : raw326step0 = -raw326 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw326).symm
    injectiveMoment H raw326step0 = injectiveMoment H raw326step1 := by
      have heq : raw326step1 = (fun i j => raw326step0 (permutation32 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw326step0 permutation32 permutation5
    _ = injectiveMoment H node173 := by rfl

theorem canonical328 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw328 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw328 = injectiveMoment H raw328step0 := by
      have heq : raw328step0 = raw328.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw328).symm
    injectiveMoment H raw328step0 = injectiveMoment H raw328step1 := by
      have heq : raw328step1 = -raw328step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw328step0).symm
    injectiveMoment H raw328step1 = injectiveMoment H raw328step2 := by
      have heq : raw328step2 = (fun i j => raw328step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw328step1 permutation4 permutation6
    _ = injectiveMoment H node59 := by rfl

theorem canonical329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw329 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw329 = injectiveMoment H raw329step0 := by
      have heq : raw329step0 = -raw329 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw329).symm
    injectiveMoment H raw329step0 = injectiveMoment H raw329step1 := by
      have heq : raw329step1 = (fun i j => raw329step0 (permutation30 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw329step0 permutation30 permutation5
    _ = injectiveMoment H node173 := by rfl

theorem canonical333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw333 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw333 = injectiveMoment H raw333step0 := by
      have heq : raw333step0 = -raw333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw333).symm
    injectiveMoment H raw333step0 = injectiveMoment H raw333step1 := by
      have heq : raw333step1 = (fun i j => raw333step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw333step0 permutation6 permutation5
    _ = injectiveMoment H node40 := by rfl

theorem canonical336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw336 = injectiveMoment H node38 := by
  calc
    injectiveMoment H raw336 = injectiveMoment H raw336step0 := by
      have heq : raw336step0 = raw336.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw336).symm
    injectiveMoment H raw336step0 = injectiveMoment H raw336step1 := by
      have heq : raw336step1 = (fun i j => raw336step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw336step0 permutation6 permutation5
    _ = injectiveMoment H node38 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

theorem canonical4161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4161 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4161 = injectiveMoment H raw4161step0 := by
      have heq : raw4161step0 = -raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4161).symm
    injectiveMoment H raw4161step0 = injectiveMoment H raw4161step1 := by
      have heq : raw4161step1 = (fun i j => raw4161step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4161step0 permutation5 permutation5
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical578 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw578 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw578 = injectiveMoment H raw578step0 := by
      have heq : raw578step0 = -raw578 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw578).symm
    injectiveMoment H raw578step0 = injectiveMoment H raw578step1 := by
      have heq : raw578step1 = (fun i j => raw578step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw578step0 permutation27 permutation5
    _ = injectiveMoment H node188 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

theorem canonical5982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5982 = injectiveMoment H node58 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1411 = injectiveMoment H node445 := by
  rfl

theorem canonical1416 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1416 = injectiveMoment H node149 := by
  rfl

theorem canonical1437 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1437 = injectiveMoment H node155 := by
  rfl

theorem canonical1438 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1438 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw1438 = injectiveMoment H raw1438step0 := by
      have heq : raw1438step0 = (fun i j => raw1438 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1438 permutation10 permutation3
    _ = injectiveMoment H node155 := by rfl

theorem canonical1439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1439 = injectiveMoment H node32 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1441 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1441 = injectiveMoment H node157 := by
  rfl

theorem canonical1442 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1442 = injectiveMoment H node33 := by
  rfl

theorem canonical1446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1446 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1446 = injectiveMoment H raw1446step0 := by
      have heq : raw1446step0 = raw1446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1446).symm
    injectiveMoment H raw1446step0 = injectiveMoment H raw1446step1 := by
      have heq : raw1446step1 = (fun i j => raw1446step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1446step0 permutation6 permutation5
    _ = injectiveMoment H node59 := by rfl

theorem canonical1447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1447 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1447 = injectiveMoment H raw1447step0 := by
      have heq : raw1447step0 = raw1447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1447).symm
    injectiveMoment H raw1447step0 = injectiveMoment H raw1447step1 := by
      have heq : raw1447step1 = (fun i j => raw1447step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1447step0 permutation8 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1450 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1450 = injectiveMoment H raw1450step0 := by
      have heq : raw1450step0 = raw1450.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1450).symm
    injectiveMoment H raw1450step0 = injectiveMoment H raw1450step1 := by
      have heq : raw1450step1 = (fun i j => raw1450step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1450step0 permutation8 permutation8
    _ = injectiveMoment H node52 := by rfl

theorem canonical1451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1451 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1451 = injectiveMoment H raw1451step0 := by
      have heq : raw1451step0 = raw1451.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1451).symm
    injectiveMoment H raw1451step0 = injectiveMoment H raw1451step1 := by
      have heq : raw1451step1 = (fun i j => raw1451step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1451step0 permutation6 permutation7
    _ = injectiveMoment H node59 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound149 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node149 = Sparse.eval value149 (momentVector H) := by
  have heq : pivotMatrix149 = (fun u v => node149 (pivotPermutation149 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node149 = injectiveMoment H pivotMatrix149 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix149 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix149 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix149 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix149 (0 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix149 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix149 (1 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix149 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix149 (2 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node149 + (injectiveMoment H (mergeFirst pivotMatrix149 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix149 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix149 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value149, value52, value59, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node155 = Sparse.eval value155 (momentVector H) := by
  have heq : pivotMatrix155 = (fun u v => node155 (pivotPermutation155 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node155 = injectiveMoment H pivotMatrix155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix155 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix155 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (0 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (1 : Fin 3) = raw1450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1450 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node155 + (injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value155, value32, value52, value53, Sparse.eval] at hc ⊢
  linarith

theorem sound157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node157 = Sparse.eval value157 (momentVector H) := by
  have heq : pivotMatrix157 = (fun u v => node157 (pivotPermutation157 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node157 = injectiveMoment H pivotMatrix157 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix157 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix157 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix157 (0 : Fin 3)) =
      Sparse.eval value54 (momentVector H) := by
    have heq : mergeFirst pivotMatrix157 (0 : Fin 3) = raw5552 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5552 hH).trans (sound54 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix157 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix157 (1 : Fin 3) = raw1451 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1451 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix157 (2 : Fin 3)) =
      Sparse.eval value33 (momentVector H) := by
    have heq : mergeFirst pivotMatrix157 (2 : Fin 3) = raw1442 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1442 hH).trans (sound33 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node157 + (injectiveMoment H (mergeFirst pivotMatrix157 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix157 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix157 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value157, value33, value54, value59, Sparse.eval] at hc ⊢
  linarith

theorem sound170 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node170 = Sparse.eval value170 (momentVector H) := by
  have heq : pivotMatrix170 = (fun u v => node170 (pivotPermutation170 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node170 = injectiveMoment H pivotMatrix170 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix170 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix170 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix170 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix170 (0 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix170 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix170 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix170 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix170 (2 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node170 + (injectiveMoment H (mergeFirst pivotMatrix170 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix170 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix170 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value170, value32, value36, value37, Sparse.eval] at hc ⊢
  linarith

theorem sound173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node173 = Sparse.eval value173 (momentVector H) := by
  have heq : pivotMatrix173 = (fun u v => node173 (pivotPermutation173 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node173 = injectiveMoment H pivotMatrix173 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix173 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix173 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix173 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (0 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix173 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (1 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix173 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node173 + (injectiveMoment H (mergeFirst pivotMatrix173 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix173 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix173 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value173, value40, value59, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node176 = Sparse.eval value176 (momentVector H) := by
  have heq : pivotMatrix176 = (fun u v => node176 (pivotPermutation176 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node176 = injectiveMoment H pivotMatrix176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix176 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node176 + (injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value176, value36, value57, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound180 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node180 = Sparse.eval value180 (momentVector H) := by
  have heq : pivotMatrix180 = (fun u v => node180 (pivotPermutation180 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node180 = injectiveMoment H pivotMatrix180 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix180 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix180 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix180 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (0 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix180 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (1 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix180 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (2 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node180 + (injectiveMoment H (mergeFirst pivotMatrix180 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix180 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix180 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value180, value36, value40, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node187 = Sparse.eval value187 (momentVector H) := by
  have heq : pivotMatrix187 = (fun u v => node187 (pivotPermutation187 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node187 = injectiveMoment H pivotMatrix187 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix187 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix187 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix187 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix187 (0 : Fin 3) = raw6870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix187 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix187 (1 : Fin 3) = raw2865 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2865 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix187 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix187 (2 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node187 + (injectiveMoment H (mergeFirst pivotMatrix187 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix187 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix187 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value187, value37, value40, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node188 = Sparse.eval value188 (momentVector H) := by
  have heq : pivotMatrix188 = (fun u v => node188 (pivotPermutation188 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node188 = injectiveMoment H pivotMatrix188 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix188 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix188 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix188 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (0 : Fin 3) = raw5982 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix188 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (1 : Fin 3) = raw2864 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2864 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix188 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (2 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node188 + (injectiveMoment H (mergeFirst pivotMatrix188 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix188 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix188 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value188, value37, value58, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound190 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node190 = Sparse.eval value190 (momentVector H) := by
  have heq : pivotMatrix190 = (fun u v => node190 (pivotPermutation190 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node190 = injectiveMoment H pivotMatrix190 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix190 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix190 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix190 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix190 (0 : Fin 3) = raw5986 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5986 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix190 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix190 (1 : Fin 3) = raw2865 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2865 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix190 (2 : Fin 3)) =
      Sparse.eval value38 (momentVector H) := by
    have heq : mergeFirst pivotMatrix190 (2 : Fin 3) = raw2853 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2853 hH).trans (sound38 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node190 + (injectiveMoment H (mergeFirst pivotMatrix190 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix190 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix190 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value190, value38, value40, value59, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node207 = Sparse.eval value207 (momentVector H) := by
  have heq : pivotMatrix207 = (fun u v => node207 (pivotPermutation207 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node207 = injectiveMoment H pivotMatrix207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix207 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix207 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (0 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (2 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node207 + (injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value207, value41, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound215 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node215 = Sparse.eval value215 (momentVector H) := by
  have heq : pivotMatrix215 = (fun u v => node215 (pivotPermutation215 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node215 = injectiveMoment H pivotMatrix215 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix215 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix215 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (0 : Fin 3) = raw6870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (1 : Fin 3) = raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4161 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (2 : Fin 3) = raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4147 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node215 + (injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value215, value36, value37, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw522 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw522 = injectiveMoment H raw522step0 := by
      have heq : raw522step0 = (fun i j => raw522 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw522 permutation27 permutation6
    _ = injectiveMoment H node188 := by rfl

theorem canonical530 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw530 = injectiveMoment H node349 := by
  rfl

theorem canonical533 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw533 = injectiveMoment H node349 := by
  calc
    injectiveMoment H raw533 = injectiveMoment H raw533step0 := by
      have heq : raw533step0 = (fun i j => raw533 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw533 permutation35 permutation3
    _ = injectiveMoment H node349 := by rfl

theorem canonical534 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw534 = injectiveMoment H node1139 := by
  calc
    injectiveMoment H raw534 = injectiveMoment H raw534step0 := by
      have heq : raw534step0 = -raw534 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw534).symm
    injectiveMoment H raw534step0 = injectiveMoment H raw534step1 := by
      have heq : raw534step1 = (fun i j => raw534step0 (permutation133 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw534step0 permutation133 permutation5
    _ = injectiveMoment H node1139 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical574 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw574 = injectiveMoment H node87 := by
  calc
    injectiveMoment H raw574 = injectiveMoment H raw574step0 := by
      have heq : raw574step0 = -raw574 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw574).symm
    injectiveMoment H raw574step0 = injectiveMoment H raw574step1 := by
      have heq : raw574step1 = (fun i j => raw574step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw574step0 permutation28 permutation5
    _ = injectiveMoment H node87 := by rfl

theorem canonical575 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw575 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw575 = injectiveMoment H raw575step0 := by
      have heq : raw575step0 = -raw575 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw575).symm
    injectiveMoment H raw575step0 = injectiveMoment H raw575step1 := by
      have heq : raw575step1 = (fun i j => raw575step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw575step0 permutation31 permutation5
    _ = injectiveMoment H node170 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw293 = injectiveMoment H node320 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical771 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw771 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw771 = injectiveMoment H raw771step0 := by
      have heq : raw771step0 = -raw771 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw771).symm
    injectiveMoment H raw771step0 = injectiveMoment H raw771step1 := by
      have heq : raw771step1 = (fun i j => raw771step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw771step0 permutation13 permutation8
    _ = injectiveMoment H node188 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw804 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw804 = injectiveMoment H raw804step0 := by
      have heq : raw804step0 = (fun i j => raw804 (permutation32 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw804 permutation32 permutation7
    _ = injectiveMoment H node109 := by rfl

theorem canonical813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw813 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw813 = injectiveMoment H raw813step0 := by
      have heq : raw813step0 = -raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw813).symm
    injectiveMoment H raw813step0 = injectiveMoment H raw813step1 := by
      have heq : raw813step1 = (fun i j => raw813step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw813step0 permutation4 permutation8
    _ = injectiveMoment H node36 := by rfl

theorem canonical814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw814 = injectiveMoment H node21 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound87 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node87 = Sparse.eval value87 (momentVector H) := by
  have heq : pivotMatrix87 = (fun u v => node87 (pivotPermutation87 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node87 = injectiveMoment H pivotMatrix87 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix87 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix87 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix87 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix87 (0 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix87 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix87 (1 : Fin 3) = raw333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical333 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix87 (2 : Fin 3)) =
      Sparse.eval value18 (momentVector H) := by
    have heq : mergeFirst pivotMatrix87 (2 : Fin 3) = raw320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical320 hH).trans (sound18 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node87 + (injectiveMoment H (mergeFirst pivotMatrix87 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix87 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix87 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value87, value18, value32, value40, Sparse.eval] at hc ⊢
  linarith

theorem sound90 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node90 = Sparse.eval value90 (momentVector H) := by
  have heq : pivotMatrix90 = (fun u v => node90 (pivotPermutation90 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node90 = injectiveMoment H pivotMatrix90 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix90 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix90 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix90 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix90 (0 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix90 (1 : Fin 3)) =
      Sparse.eval value38 (momentVector H) := by
    have heq : mergeFirst pivotMatrix90 (1 : Fin 3) = raw336 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical336 hH).trans (sound38 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix90 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix90 (2 : Fin 3) = raw328 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical328 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node90 + (injectiveMoment H (mergeFirst pivotMatrix90 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix90 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix90 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value90, value38, value59, Sparse.eval] at hc ⊢
  linarith

theorem sound109 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node109 = Sparse.eval value109 (momentVector H) := by
  have heq : pivotMatrix109 = (fun u v => node109 (pivotPermutation109 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node109 = injectiveMoment H pivotMatrix109 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix109 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix109 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix109 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix109 (0 : Fin 3) = raw840 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical840 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix109 (1 : Fin 3)) =
      Sparse.eval value21 (momentVector H) := by
    have heq : mergeFirst pivotMatrix109 (1 : Fin 3) = raw814 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical814 hH).trans (sound21 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix109 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix109 (2 : Fin 3) = raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical813 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node109 + (injectiveMoment H (mergeFirst pivotMatrix109 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix109 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix109 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value109, value21, value36, value43, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound285 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node285 = Sparse.eval value285 (momentVector H) := by
  have heq : pivotMatrix285 = (fun u v => node285 (pivotPermutation285 u) v) := by apply Matrix.ext; unfold pivotMatrix285 node285 pivotPermutation285; decide +kernel
  have hmoment : injectiveMoment H node285 = injectiveMoment H pivotMatrix285 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix285 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix285 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix285 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix285 (0 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix285 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix285 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix285 (1 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix285 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix285 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix285 (2 : Fin 3) = raw6870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix285 raw6870; decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node285 + (injectiveMoment H (mergeFirst pivotMatrix285 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix285 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix285 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value285, value58, value62, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound17
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1139 = Sparse.eval value1139 (momentVector H) := by
  have heq : pivotMatrix1139 = (fun u v => node1139 (pivotPermutation1139 u) v) := by apply Matrix.ext; unfold pivotMatrix1139 node1139 pivotPermutation1139; decide +kernel
  have hmoment : injectiveMoment H node1139 = injectiveMoment H pivotMatrix1139 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1139 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1139 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1139 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1139 (0 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1139 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1139 (1 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1139 (1 : Fin 4) = raw6764 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1139 raw6764; decide +kernel
    rw [heq]
    exact (canonical6764 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1139 (2 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1139 (2 : Fin 4) = raw6868 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1139 raw6868; decide +kernel
    rw [heq]
    exact (canonical6868 hH).trans (sound285 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1139 (3 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1139 (3 : Fin 4) = raw6872 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1139 raw6872; decide +kernel
    rw [heq]
    exact (canonical6872 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1139 + (injectiveMoment H (mergeFirst pivotMatrix1139 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1139 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1139 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1139 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1139, value176, value188, value285, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical511 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw511 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw511 = injectiveMoment H raw511step0 := by
      have heq : raw511step0 = -raw511 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw511).symm
    injectiveMoment H raw511step0 = injectiveMoment H raw511step1 := by
      have hz : ∀ j, raw511step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw511step1 = (fun i j => raw511step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw511step0 permutation57 hz
    injectiveMoment H raw511step1 = injectiveMoment H raw511step2 := by
      have heq : raw511step2 = (fun i j => raw511step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw511step1 permutation27 permutation5
    _ = injectiveMoment H node188 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical755 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw755 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw755 = injectiveMoment H raw755step0 := by
      have heq : raw755step0 = raw755.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw755).symm
    injectiveMoment H raw755step0 = injectiveMoment H raw755step1 := by
      have hz : ∀ i, raw755step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw755step1 = (fun i j => raw755step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw755step0 permutation15 hz
    injectiveMoment H raw755step1 = injectiveMoment H raw755step2 := by
      have heq : raw755step2 = (fun i j => raw755step1 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw755step1 permutation7 permutation6
    _ = injectiveMoment H node63 := by rfl

theorem canonical763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw763 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw763 = injectiveMoment H raw763step0 := by
      have heq : raw763step0 = raw763.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw763).symm
    injectiveMoment H raw763step0 = injectiveMoment H raw763step1 := by
      have hz : ∀ i, raw763step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw763step1 = (fun i j => raw763step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw763step0 permutation21 hz
    injectiveMoment H raw763step1 = injectiveMoment H raw763step2 := by
      have heq : raw763step2 = (fun i j => raw763step1 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw763step1 permutation7 permutation6
    _ = injectiveMoment H node63 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound5
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node320 = Sparse.eval value320 (momentVector H) := by
  have heq : pivotMatrix320 = (fun u v => node320 (pivotPermutation320 u) v) := by apply Matrix.ext; unfold pivotMatrix320 node320 pivotPermutation320; decide +kernel
  have hmoment : injectiveMoment H node320 = injectiveMoment H pivotMatrix320 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix320 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix320 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix320 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix320 (0 : Fin 4) = raw578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix320 raw578; decide +kernel
    rw [heq]
    exact (canonical578 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix320 (1 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix320 (1 : Fin 4) = raw329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix320 raw329; decide +kernel
    rw [heq]
    exact (canonical329 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix320 (2 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix320 (2 : Fin 4) = raw326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix320 raw326; decide +kernel
    rw [heq]
    exact (canonical326 hH).trans (sound173 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix320 (3 : Fin 4)) =
      Sparse.eval value90 (momentVector H) := by
    have heq : mergeFirst pivotMatrix320 (3 : Fin 4) = raw325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix320 raw325; decide +kernel
    rw [heq]
    exact (canonical325 hH).trans (sound90 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node320 + (injectiveMoment H (mergeFirst pivotMatrix320 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix320 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix320 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix320 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value320, value173, value188, value90, Sparse.eval] at hc ⊢
  linarith

theorem sound349 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node349 = Sparse.eval value349 (momentVector H) := by
  have heq : pivotMatrix349 = (fun u v => node349 (pivotPermutation349 u) v) := by apply Matrix.ext; unfold pivotMatrix349 node349 pivotPermutation349; decide +kernel
  have hmoment : injectiveMoment H node349 = injectiveMoment H pivotMatrix349 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix349 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix349 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix349 (0 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix349 (0 : Fin 4) = raw804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix349 raw804; decide +kernel
    rw [heq]
    exact (canonical804 hH).trans (sound109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix349 (1 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix349 (1 : Fin 4) = raw578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix349 raw578; decide +kernel
    rw [heq]
    exact (canonical578 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix349 (2 : Fin 4)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix349 (2 : Fin 4) = raw575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix349 raw575; decide +kernel
    rw [heq]
    exact (canonical575 hH).trans (sound170 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix349 (3 : Fin 4)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix349 (3 : Fin 4) = raw574 := by apply Matrix.ext; unfold mergeFirst pivotMatrix349 raw574; decide +kernel
    rw [heq]
    exact (canonical574 hH).trans (sound87 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node349 + (injectiveMoment H (mergeFirst pivotMatrix349 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix349 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix349 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix349 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value349, value109, value170, value188, value87, Sparse.eval] at hc ⊢
  linarith

theorem sound364 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node364 = Sparse.eval value364 (momentVector H) := by
  have heq : pivotMatrix364 = (fun u v => node364 (pivotPermutation364 u) v) := by apply Matrix.ext; unfold pivotMatrix364 node364 pivotPermutation364; decide +kernel
  have hmoment : injectiveMoment H node364 = injectiveMoment H pivotMatrix364 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix364 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix364 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix364 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix364 (0 : Fin 4) = raw522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix364 raw522; decide +kernel
    rw [heq]
    exact (canonical522 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix364 (1 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix364 (1 : Fin 4) = raw755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix364 raw755; decide +kernel
    rw [heq]
    exact (canonical755 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix364 (2 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix364 (2 : Fin 4) = raw763 := by apply Matrix.ext; unfold mergeFirst pivotMatrix364 raw763; decide +kernel
    rw [heq]
    exact (canonical763 hH).trans (sound63 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix364 (3 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix364 (3 : Fin 4) = raw771 := by apply Matrix.ext; unfold mergeFirst pivotMatrix364 raw771; decide +kernel
    rw [heq]
    exact (canonical771 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node364 + (injectiveMoment H (mergeFirst pivotMatrix364 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix364 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix364 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix364 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value364, value188, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound6
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound445 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node445 = Sparse.eval value445 (momentVector H) := by
  have heq : pivotMatrix445 = (fun u v => node445 (pivotPermutation445 u) v) := by apply Matrix.ext; unfold pivotMatrix445 node445 pivotPermutation445; decide +kernel
  have hmoment : injectiveMoment H node445 = injectiveMoment H pivotMatrix445 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix445 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix445 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix445 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix445 (0 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix445 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix445 (1 : Fin 4)) =
      Sparse.eval value157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix445 (1 : Fin 4) = raw1441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix445 raw1441; decide +kernel
    rw [heq]
    exact (canonical1441 hH).trans (sound157 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix445 (2 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix445 (2 : Fin 4) = raw1438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix445 raw1438; decide +kernel
    rw [heq]
    exact (canonical1438 hH).trans (sound155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix445 (3 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix445 (3 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix445 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node445 + (injectiveMoment H (mergeFirst pivotMatrix445 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix445 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix445 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix445 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value445, value155, value157, value188, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2671 = injectiveMoment H node364 := by
  calc
    injectiveMoment H raw2671 = injectiveMoment H raw2671step0 := by
      have heq : raw2671step0 = (fun i j => raw2671 (permutation136 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2671 permutation136 permutation7
    _ = injectiveMoment H node364 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound8
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound559 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node559 = Sparse.eval value559 (momentVector H) := by
  have heq : pivotMatrix559 = (fun u v => node559 (pivotPermutation559 u) v) := by apply Matrix.ext; unfold pivotMatrix559 node559 pivotPermutation559; decide +kernel
  have hmoment : injectiveMoment H node559 = injectiveMoment H pivotMatrix559 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix559 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix559 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix559 (0 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix559 (0 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix559 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix559 (1 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix559 (1 : Fin 4) = raw2781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix559 raw2781; decide +kernel
    rw [heq]
    exact (canonical2781 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix559 (2 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix559 (2 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix559 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix559 (3 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix559 (3 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix559 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node559 + (injectiveMoment H (mergeFirst pivotMatrix559 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix559 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix559 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix559 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value559, value149, value180, value181, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound573 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node573 = Sparse.eval value573 (momentVector H) := by
  have heq : pivotMatrix573 = (fun u v => node573 (pivotPermutation573 u) v) := by apply Matrix.ext; unfold pivotMatrix573 node573 pivotPermutation573; decide +kernel
  have hmoment : injectiveMoment H node573 = injectiveMoment H pivotMatrix573 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix573 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix573 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix573 (0 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (0 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix573 (1 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (1 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix573 (2 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (2 : Fin 4) = raw2843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw2843; decide +kernel
    rw [heq]
    exact (canonical2843 hH).trans (sound185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix573 (3 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (3 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node573 + (injectiveMoment H (mergeFirst pivotMatrix573 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix573 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix573 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix573 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value573, value185, value188, value207, Sparse.eval] at hc ⊢
  linarith

theorem sound575 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node575 = Sparse.eval value575 (momentVector H) := by
  have heq : pivotMatrix575 = (fun u v => node575 (pivotPermutation575 u) v) := by apply Matrix.ext; unfold pivotMatrix575 node575 pivotPermutation575; decide +kernel
  have hmoment : injectiveMoment H node575 = injectiveMoment H pivotMatrix575 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix575 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix575 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix575 (0 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix575 (0 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix575 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix575 (1 : Fin 4)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix575 (1 : Fin 4) = raw2851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix575 raw2851; decide +kernel
    rw [heq]
    exact (canonical2851 hH).trans (sound190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix575 (2 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix575 (2 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix575 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix575 (3 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix575 (3 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix575 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node575 + (injectiveMoment H (mergeFirst pivotMatrix575 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix575 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix575 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix575 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value575, value187, value188, value190, value215, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound21
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1405 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1405 = Sparse.eval value1405 (momentVector H) := by
  have heq : pivotMatrix1405 = (fun u v => node1405 (pivotPermutation1405 u) v) := by apply Matrix.ext; unfold pivotMatrix1405 node1405 pivotPermutation1405; decide +kernel
  have hmoment : injectiveMoment H node1405 = injectiveMoment H pivotMatrix1405 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1405 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1405 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1405 (0 : Fin 5)) =
      Sparse.eval value320 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (0 : Fin 5) = raw293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw293; decide +kernel
    rw [heq]
    exact (canonical293 hH).trans (sound320 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1405 (1 : Fin 5)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (1 : Fin 5) = raw511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw511; decide +kernel
    rw [heq]
    exact (canonical511 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1405 (2 : Fin 5)) =
      Sparse.eval value349 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (2 : Fin 5) = raw530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw530; decide +kernel
    rw [heq]
    exact (canonical530 hH).trans (sound349 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1405 (3 : Fin 5)) =
      Sparse.eval value349 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (3 : Fin 5) = raw533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw533; decide +kernel
    rw [heq]
    exact (canonical533 hH).trans (sound349 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1405 (4 : Fin 5)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (4 : Fin 5) = raw534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw534; decide +kernel
    rw [heq]
    exact (canonical534 hH).trans (sound1139 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1405 + (injectiveMoment H (mergeFirst pivotMatrix1405 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1405 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1405 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1405 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1405 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1405, value1139, value188, value320, value349, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound28
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1854 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1854 = Sparse.eval value1854 (momentVector H) := by
  have heq : pivotMatrix1854 = (fun u v => node1854 (pivotPermutation1854 u) v) := by apply Matrix.ext; unfold pivotMatrix1854 node1854 pivotPermutation1854; decide +kernel
  have hmoment : injectiveMoment H node1854 = injectiveMoment H pivotMatrix1854 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1854 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1854 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1854 (0 : Fin 5)) =
      Sparse.eval value320 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (0 : Fin 5) = raw293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw293; decide +kernel
    rw [heq]
    exact (canonical293 hH).trans (sound320 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1854 (1 : Fin 5)) =
      Sparse.eval value364 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (1 : Fin 5) = raw2671 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw2671; decide +kernel
    rw [heq]
    exact (canonical2671 hH).trans (sound364 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1854 (2 : Fin 5)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (2 : Fin 5) = raw2787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw2787; decide +kernel
    rw [heq]
    exact (canonical2787 hH).trans (sound559 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1854 (3 : Fin 5)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (3 : Fin 5) = raw2818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw2818; decide +kernel
    rw [heq]
    exact (canonical2818 hH).trans (sound559 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1854 (4 : Fin 5)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (4 : Fin 5) = raw2819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw2819; decide +kernel
    rw [heq]
    exact (canonical2819 hH).trans (sound573 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1854 + (injectiveMoment H (mergeFirst pivotMatrix1854 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1854 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1854 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1854 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1854 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1854, value320, value364, value559, value573, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound29
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1887 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1887 = Sparse.eval value1887 (momentVector H) := by
  have heq : pivotMatrix1887 = (fun u v => node1887 (pivotPermutation1887 u) v) := by apply Matrix.ext; unfold pivotMatrix1887 node1887 pivotPermutation1887; decide +kernel
  have hmoment : injectiveMoment H node1887 = injectiveMoment H pivotMatrix1887 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1887 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1887 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1887 (0 : Fin 5)) =
      Sparse.eval value445 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1887 (0 : Fin 5) = raw1411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1887 raw1411; decide +kernel
    rw [heq]
    exact (canonical1411 hH).trans (sound445 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1887 (1 : Fin 5)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1887 (1 : Fin 5) = raw2778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1887 raw2778; decide +kernel
    rw [heq]
    exact (canonical2778 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1887 (2 : Fin 5)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1887 (2 : Fin 5) = raw2809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1887 raw2809; decide +kernel
    rw [heq]
    exact (canonical2809 hH).trans (sound573 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1887 (3 : Fin 5)) =
      Sparse.eval value575 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1887 (3 : Fin 5) = raw2813 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1887 raw2813; decide +kernel
    rw [heq]
    exact (canonical2813 hH).trans (sound575 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1887 (4 : Fin 5)) =
      Sparse.eval value575 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1887 (4 : Fin 5) = raw2814 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1887 raw2814; decide +kernel
    rw [heq]
    exact (canonical2814 hH).trans (sound575 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1887 + (injectiveMoment H (mergeFirst pivotMatrix1887 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1887 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1887 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1887 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1887 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1887, value188, value445, value573, value575, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound286 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow286 (momentVector H) = 0 := by
  have hshape : boundaryMatrix286 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix286 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix286 (0 : Fin 6)) =
      Sparse.eval value1867 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (0 : Fin 6) = raw6859 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6859 hH).trans (sound1867_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix286 (1 : Fin 6)) =
      Sparse.eval value1854 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (1 : Fin 6) = raw8543 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8543 hH).trans (sound1854 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix286 (2 : Fin 6)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (2 : Fin 6) = raw8703 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8703 hH).trans (sound559 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix286 (3 : Fin 6)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (3 : Fin 6) = raw8770 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8770 hH).trans (sound559 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix286 (4 : Fin 6)) =
      Sparse.eval value1405 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (4 : Fin 6) = raw8773 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8773 hH).trans (sound1405 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix286 (5 : Fin 6)) =
      Sparse.eval value1887 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (5 : Fin 6) = raw8774 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8774 hH).trans (sound1887 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix286 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow286, value1405, value1854, value1867, value1887, value559, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck163 : Integer.Sparse.reindex coordinateMap (PairData.rows 163) =
    PairSemantics.boundaryRow286 := by decide +kernel

theorem rowSound163_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 163) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck163]
  exact PairSemantics.boundarySound286 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e_oai
