-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T14:44:52.819433+00:00
-- url     : https://prove2.me/submissions/5e71f8ac-6d82-448f-8d92-fb8741ce5699

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2444_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3021_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3151_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3194_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3202_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3348_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8080 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8080 = injectiveMoment H node3151 := by
  calc
    injectiveMoment H raw8080 = injectiveMoment H raw8080step0 := by
      have heq : raw8080step0 = (fun i j => raw8080 (permutation183 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8080 permutation183 permutation15
    _ = injectiveMoment H node3151 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8099 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8099 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8099 = injectiveMoment H raw8099step0 := by
      have heq : raw8099step0 = -raw8099 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8099).symm
    injectiveMoment H raw8099step0 = injectiveMoment H raw8099step1 := by
      have hz : ∀ i, raw8099step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8099step1 = (fun i j => raw8099step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8099step0 permutation9 hz
    injectiveMoment H raw8099step1 = injectiveMoment H raw8099step2 := by
      have heq : raw8099step2 = (fun i j => raw8099step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8099step1 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

theorem canonical8111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8111 = injectiveMoment H node2717 := by
  calc
    injectiveMoment H raw8111 = injectiveMoment H raw8111step0 := by
      have heq : raw8111step0 = (fun i j => raw8111 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8111 permutation57 permutation9
    _ = injectiveMoment H node2717 := by rfl

theorem canonical8124 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8124 = injectiveMoment H node2779 := by
  calc
    injectiveMoment H raw8124 = injectiveMoment H raw8124step0 := by
      have heq : raw8124step0 = -raw8124 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8124).symm
    injectiveMoment H raw8124step0 = injectiveMoment H raw8124step1 := by
      have heq : raw8124step1 = (fun i j => raw8124step0 (permutation147 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8124step0 permutation147 permutation10
    _ = injectiveMoment H node2779 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8384 = injectiveMoment H node3194 := by
  calc
    injectiveMoment H raw8384 = injectiveMoment H raw8384step0 := by
      have heq : raw8384step0 = (fun i j => raw8384 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8384 permutation277 permutation9
    _ = injectiveMoment H node3194 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical263
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8441 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8441 = injectiveMoment H node3348 := by
  calc
    injectiveMoment H raw8441 = injectiveMoment H raw8441step0 := by
      have heq : raw8441step0 = -raw8441 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8441).symm
    injectiveMoment H raw8441step0 = injectiveMoment H raw8441step1 := by
      have heq : raw8441step1 = (fun i j => raw8441step0 (permutation380 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8441step0 permutation380 permutation15
    _ = injectiveMoment H node3348 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical264
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8453 = injectiveMoment H node3202 := by
  calc
    injectiveMoment H raw8453 = injectiveMoment H raw8453step0 := by
      have heq : raw8453step0 = (fun i j => raw8453 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8453 permutation258 permutation9
    _ = injectiveMoment H node3202 := by rfl

theorem canonical8455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8455 = injectiveMoment H node3021 := by
  calc
    injectiveMoment H raw8455 = injectiveMoment H raw8455step0 := by
      have heq : raw8455step0 = (fun i j => raw8455 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8455 permutation258 permutation9
    _ = injectiveMoment H node3021 := by rfl

theorem canonical8457 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8457 = injectiveMoment H node3430 := by
  calc
    injectiveMoment H raw8457 = injectiveMoment H raw8457step0 := by
      have heq : raw8457step0 = (fun i j => raw8457 (permutation184 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8457 permutation184 permutation15
    _ = injectiveMoment H node3430 := by rfl

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4965 = injectiveMoment H node43 := by
  rfl

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
  rfl

theorem canonical4967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4967 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw4967 = injectiveMoment H raw4967step0 := by
      have heq : raw4967step0 = -raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4967).symm
    injectiveMoment H raw4967step0 = injectiveMoment H raw4967step1 := by
      have heq : raw4967step1 = (fun i j => raw4967step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4967step0 permutation4 permutation6
    _ = injectiveMoment H node61 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5725 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5725 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw5725 = injectiveMoment H raw5725step0 := by
      have heq : raw5725step0 = raw5725.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5725).symm
    injectiveMoment H raw5725step0 = injectiveMoment H raw5725step1 := by
      have heq : raw5725step1 = (fun i j => raw5725step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5725step0 permutation30 permutation8
    _ = injectiveMoment H node185 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5750 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5750 = injectiveMoment H node2444 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5777 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5777 = injectiveMoment H node845 := by
  rfl

theorem canonical5778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5778 = injectiveMoment H node846 := by
  rfl

theorem canonical5780 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5780 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw5780 = injectiveMoment H raw5780step0 := by
      have heq : raw5780step0 = raw5780.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5780).symm
    injectiveMoment H raw5780step0 = injectiveMoment H raw5780step1 := by
      have heq : raw5780step1 = (fun i j => raw5780step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5780step0 permutation21 permutation5
    _ = injectiveMoment H node229 := by rfl

theorem canonical5783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5783 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw5783 = injectiveMoment H raw5783step0 := by
      have heq : raw5783step0 = raw5783.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5783).symm
    injectiveMoment H raw5783step0 = injectiveMoment H raw5783step1 := by
      have heq : raw5783step1 = (fun i j => raw5783step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5783step0 permutation31 permutation26
    _ = injectiveMoment H node1044 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5797 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5797 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5797 = injectiveMoment H raw5797step0 := by
      have heq : raw5797step0 = raw5797.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5797).symm
    injectiveMoment H raw5797step0 = injectiveMoment H raw5797step1 := by
      have heq : raw5797step1 = -raw5797step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5797step0).symm
    injectiveMoment H raw5797step1 = injectiveMoment H raw5797step2 := by
      have heq : raw5797step2 = (fun i j => raw5797step1 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5797step1 permutation16 permutation6
    _ = injectiveMoment H node203 := by rfl

theorem canonical5806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5806 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw5806 = injectiveMoment H raw5806step0 := by
      have heq : raw5806step0 = raw5806.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5806).symm
    injectiveMoment H raw5806step0 = injectiveMoment H raw5806step1 := by
      have heq : raw5806step1 = (fun i j => raw5806step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5806step0 permutation28 permutation8
    _ = injectiveMoment H node210 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6292 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6292 = injectiveMoment H raw6292step0 := by
      have heq : raw6292step0 = raw6292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6292).symm
    injectiveMoment H raw6292step0 = injectiveMoment H raw6292step1 := by
      have heq : raw6292step1 = (fun i j => raw6292step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6292step0 permutation27 permutation6
    _ = injectiveMoment H node176 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6324 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6324 = injectiveMoment H raw6324step0 := by
      have heq : raw6324step0 = raw6324.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6324).symm
    injectiveMoment H raw6324step0 = injectiveMoment H raw6324step1 := by
      have heq : raw6324step1 = (fun i j => raw6324step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6324step0 permutation28 permutation6
    _ = injectiveMoment H node271 := by rfl

theorem canonical6326 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6326 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6326 = injectiveMoment H raw6326step0 := by
      have heq : raw6326step0 = raw6326.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6326).symm
    injectiveMoment H raw6326step0 = injectiveMoment H raw6326step1 := by
      have heq : raw6326step1 = (fun i j => raw6326step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6326step0 permutation30 permutation8
    _ = injectiveMoment H node271 := by rfl

theorem canonical6331 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6331 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6331 = injectiveMoment H raw6331step0 := by
      have heq : raw6331step0 = raw6331.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6331).symm
    injectiveMoment H raw6331step0 = injectiveMoment H raw6331step1 := by
      have heq : raw6331step1 = -raw6331step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6331step0).symm
    injectiveMoment H raw6331step1 = injectiveMoment H raw6331step2 := by
      have heq : raw6331step2 = (fun i j => raw6331step1 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6331step1 permutation15 permutation6
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6532 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6532 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6532 = injectiveMoment H raw6532step0 := by
      have heq : raw6532step0 = raw6532.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6532).symm
    injectiveMoment H raw6532step0 = injectiveMoment H raw6532step1 := by
      have heq : raw6532step1 = -raw6532step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6532step0).symm
    injectiveMoment H raw6532step1 = injectiveMoment H raw6532step2 := by
      have heq : raw6532step2 = (fun i j => raw6532step1 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6532step1 permutation32 permutation3
    _ = injectiveMoment H node185 := by rfl

theorem canonical6540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6540 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw6540 = injectiveMoment H raw6540step0 := by
      have heq : raw6540step0 = raw6540.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6540).symm
    injectiveMoment H raw6540step0 = injectiveMoment H raw6540step1 := by
      have heq : raw6540step1 = (fun i j => raw6540step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6540step0 permutation22 permutation5
    _ = injectiveMoment H node294 := by rfl

theorem canonical6543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6543 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw6543 = injectiveMoment H raw6543step0 := by
      have hz : ∀ i, raw6543 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw6543step0 = (fun i j => raw6543 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6543 permutation21 hz
    _ = injectiveMoment H node61 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical207
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6640 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6640 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6640 = injectiveMoment H raw6640step0 := by
      have heq : raw6640step0 = raw6640.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6640).symm
    injectiveMoment H raw6640step0 = injectiveMoment H raw6640step1 := by
      have heq : raw6640step1 = -raw6640step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6640step0).symm
    injectiveMoment H raw6640step1 = injectiveMoment H raw6640step2 := by
      have heq : raw6640step2 = (fun i j => raw6640step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6640step1 permutation27 permutation5
    _ = injectiveMoment H node176 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2638 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2638 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2638 = injectiveMoment H raw2638step0 := by
      have heq : raw2638step0 = raw2638.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2638).symm
    injectiveMoment H raw2638step0 = injectiveMoment H raw2638step1 := by
      have heq : raw2638step1 = -raw2638step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2638step0).symm
    injectiveMoment H raw2638step1 = injectiveMoment H raw2638step2 := by
      have heq : raw2638step2 = (fun i j => raw2638step1 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2638step1 permutation15 permutation5
    _ = injectiveMoment H node111 := by rfl

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

theorem canonical6910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6910 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6910 = injectiveMoment H raw6910step0 := by
      have heq : raw6910step0 = raw6910.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6910).symm
    injectiveMoment H raw6910step0 = injectiveMoment H raw6910step1 := by
      have heq : raw6910step1 = -raw6910step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6910step0).symm
    injectiveMoment H raw6910step1 = injectiveMoment H raw6910step2 := by
      have heq : raw6910step2 = (fun i j => raw6910step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6910step1 permutation25 permutation4
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7462 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7462 = injectiveMoment H raw7462step0 := by
      have hz : ∀ i, raw7462 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7462step0 = (fun i j => raw7462 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7462 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8938 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8938 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw8938 = injectiveMoment H raw8938step0 := by
      have heq : raw8938step0 = (fun i j => raw8938 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8938 permutation15 permutation9
    _ = injectiveMoment H node1249 := by rfl

theorem canonical8939 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8939 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw8939 = injectiveMoment H raw8939step0 := by
      have heq : raw8939step0 = raw8939.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8939).symm
    injectiveMoment H raw8939step0 = injectiveMoment H raw8939step1 := by
      have heq : raw8939step1 = -raw8939step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8939step0).symm
    injectiveMoment H raw8939step1 = injectiveMoment H raw8939step2 := by
      have heq : raw8939step2 = (fun i j => raw8939step1 (permutation19 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8939step1 permutation19 permutation6
    _ = injectiveMoment H node226 := by rfl

theorem canonical8941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8941 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw8941 = injectiveMoment H raw8941step0 := by
      have heq : raw8941step0 = raw8941.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8941).symm
    injectiveMoment H raw8941step0 = injectiveMoment H raw8941step1 := by
      have heq : raw8941step1 = (fun i j => raw8941step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8941step0 permutation21 permutation18
    _ = injectiveMoment H node939 := by rfl

theorem canonical8944 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8944 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw8944 = injectiveMoment H raw8944step0 := by
      have heq : raw8944step0 = -raw8944 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8944).symm
    injectiveMoment H raw8944step0 = injectiveMoment H raw8944step1 := by
      have hz : ∀ i, raw8944step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8944step1 = (fun i j => raw8944step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8944step0 permutation9 hz
    injectiveMoment H raw8944step1 = injectiveMoment H raw8944step2 := by
      have heq : raw8944step2 = (fun i j => raw8944step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8944step1 permutation24 permutation4
    _ = injectiveMoment H node229 := by rfl

theorem canonical8945 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8945 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw8945 = injectiveMoment H raw8945step0 := by
      have heq : raw8945step0 = -raw8945 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8945).symm
    injectiveMoment H raw8945step0 = injectiveMoment H raw8945step1 := by
      have hz : ∀ i, raw8945step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8945step1 = (fun i j => raw8945step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8945step0 permutation9 hz
    injectiveMoment H raw8945step1 = injectiveMoment H raw8945step2 := by
      have heq : raw8945step2 = (fun i j => raw8945step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8945step1 permutation5 permutation3
    _ = injectiveMoment H node43 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

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

theorem sound61 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node61 = Sparse.eval value61 (momentVector H) := by
  have heq : pivotMatrix61 = (fun u v => node61 (pivotPermutation61 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node61 = injectiveMoment H pivotMatrix61 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix61 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix61 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (0 : Fin 2) = raw7462 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7462 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node61 + (injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value61, value11, value5, Sparse.eval] at hc ⊢
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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node111 = Sparse.eval value111 (momentVector H) := by
  have hc : momentVector H 33 = injectiveMoment H node111 := rfl
  simp [value111, Sparse.eval, hc]

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

theorem canonical5972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5972 = injectiveMoment H node56 := by
  rfl

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

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

theorem canonical6858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6858 = injectiveMoment H node61 := by
  rfl

theorem canonical6865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6865 = injectiveMoment H node62 := by
  rfl

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

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4922 = injectiveMoment H node226 := by
  rfl

theorem canonical4925 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4925 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4925 = injectiveMoment H raw4925step0 := by
      have heq : raw4925step0 = -raw4925 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4925).symm
    injectiveMoment H raw4925step0 = injectiveMoment H raw4925step1 := by
      have heq : raw4925step1 = (fun i j => raw4925step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4925step0 permutation8 permutation3
    _ = injectiveMoment H node36 := by rfl

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

theorem canonical4945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4945 = injectiveMoment H node229 := by
  rfl

theorem canonical4946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4946 = injectiveMoment H node230 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7419 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7419 = injectiveMoment H raw7419step0 := by
      have heq : raw7419step0 = -raw7419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7419).symm
    injectiveMoment H raw7419step0 = injectiveMoment H raw7419step1 := by
      have heq : raw7419step1 = (fun i j => raw7419step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7419step0 permutation8 permutation3
    _ = injectiveMoment H node57 := by rfl

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

theorem sound203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node203 = Sparse.eval value203 (momentVector H) := by
  have heq : pivotMatrix203 = (fun u v => node203 (pivotPermutation203 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node203 = injectiveMoment H pivotMatrix203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix203 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (1 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (2 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node203 + (injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value203, value36, value41, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound210 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node210 = Sparse.eval value210 (momentVector H) := by
  have heq : pivotMatrix210 = (fun u v => node210 (pivotPermutation210 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node210 = injectiveMoment H pivotMatrix210 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix210 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix210 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (0 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (1 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node210 + (injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value210, value36, value44, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node226 = Sparse.eval value226 (momentVector H) := by
  have heq : pivotMatrix226 = (fun u v => node226 (pivotPermutation226 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node226 = injectiveMoment H pivotMatrix226 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix226 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix226 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix226 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (0 : Fin 3) = raw7419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7419 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix226 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (1 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix226 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (2 : Fin 3) = raw4925 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4925 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node226 + (injectiveMoment H (mergeFirst pivotMatrix226 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix226 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix226 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value226, value36, value43, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node229 = Sparse.eval value229 (momentVector H) := by
  have heq : pivotMatrix229 = (fun u v => node229 (pivotPermutation229 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node229 = injectiveMoment H pivotMatrix229 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix229 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix229 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix229 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (0 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix229 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (1 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix229 (2 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (2 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node229 + (injectiveMoment H (mergeFirst pivotMatrix229 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix229 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix229 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value229, value36, value43, value44, Sparse.eval] at hc ⊢
  linarith

theorem sound230 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node230 = Sparse.eval value230 (momentVector H) := by
  have heq : pivotMatrix230 = (fun u v => node230 (pivotPermutation230 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node230 = injectiveMoment H pivotMatrix230 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix230 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix230 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (1 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (2 : Fin 3) = raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4967 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node230 + (injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value230, value44, value61, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5836 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw5836 = injectiveMoment H raw5836step0 := by
      have heq : raw5836step0 = raw5836.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5836).symm
    injectiveMoment H raw5836step0 = injectiveMoment H raw5836step1 := by
      have heq : raw5836step1 = (fun i j => raw5836step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5836step0 permutation31 permutation26
    _ = injectiveMoment H node1110 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8545 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw8545 = injectiveMoment H raw8545step0 := by
      have heq : raw8545step0 = (fun i j => raw8545 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8545 permutation5 permutation4
    _ = injectiveMoment H node61 := by rfl

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

theorem canonical8778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8778 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8778 = injectiveMoment H raw8778step0 := by
      have hz : ∀ i, raw8778 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8778step0 = (fun i j => raw8778 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8778 permutation3 hz
    injectiveMoment H raw8778step0 = injectiveMoment H raw8778step1 := by
      have heq : raw8778step1 = (fun i j => raw8778step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8778step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem sound271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node271 = Sparse.eval value271 (momentVector H) := by
  have heq : pivotMatrix271 = (fun u v => node271 (pivotPermutation271 u) v) := by apply Matrix.ext; unfold pivotMatrix271 node271 pivotPermutation271; decide +kernel
  have hmoment : injectiveMoment H node271 = injectiveMoment H pivotMatrix271 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix271 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix271 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix271 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (0 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix271 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix271 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (2 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node271 + (injectiveMoment H (mergeFirst pivotMatrix271 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix271 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix271 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value271, value56, value57, value61, Sparse.eval] at hc ⊢
  linarith

theorem sound294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node294 = Sparse.eval value294 (momentVector H) := by
  have heq : pivotMatrix294 = (fun u v => node294 (pivotPermutation294 u) v) := by apply Matrix.ext; unfold pivotMatrix294 node294 pivotPermutation294; decide +kernel
  have hmoment : injectiveMoment H node294 = injectiveMoment H pivotMatrix294 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix294 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix294 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (0 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (1 : Fin 3) = raw8545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8545; decide +kernel
    rw [heq]
    exact (canonical8545 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (2 : Fin 3) = raw8778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8778; decide +kernel
    rw [heq]
    exact (canonical8778 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node294 + (injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value294, value11, value61, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical194
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6225 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6225 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6225 = injectiveMoment H raw6225step0 := by
      have heq : raw6225step0 = raw6225.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6225).symm
    injectiveMoment H raw6225step0 = injectiveMoment H raw6225step1 := by
      have heq : raw6225step1 = -raw6225step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6225step0).symm
    injectiveMoment H raw6225step1 = injectiveMoment H raw6225step2 := by
      have heq : raw6225step2 = (fun i j => raw6225step1 (permutation21 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6225step1 permutation21 permutation6
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6566 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6566 = injectiveMoment H raw6566step0 := by
      have heq : raw6566step0 = raw6566.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6566).symm
    injectiveMoment H raw6566step0 = injectiveMoment H raw6566step1 := by
      have heq : raw6566step1 = -raw6566step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6566step0).symm
    injectiveMoment H raw6566step1 = injectiveMoment H raw6566step2 := by
      have heq : raw6566step2 = (fun i j => raw6566step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6566step1 permutation31 permutation3
    _ = injectiveMoment H node185 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6938 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6938 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw6938 = injectiveMoment H raw6938step0 := by
      have heq : raw6938step0 = raw6938.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6938).symm
    injectiveMoment H raw6938step0 = injectiveMoment H raw6938step1 := by
      have heq : raw6938step1 = -raw6938step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6938step0).symm
    injectiveMoment H raw6938step1 = injectiveMoment H raw6938step2 := by
      have heq : raw6938step2 = (fun i j => raw6938step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6938step1 permutation25 permutation4
    _ = injectiveMoment H node226 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7106 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7106 = injectiveMoment H raw7106step0 := by
      have hz : ∀ i, raw7106 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7106step0 = (fun i j => raw7106 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7106 permutation15 hz
    _ = injectiveMoment H node57 := by rfl

theorem canonical7119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7119 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw7119 = injectiveMoment H raw7119step0 := by
      have heq : raw7119step0 = raw7119.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7119).symm
    injectiveMoment H raw7119step0 = injectiveMoment H raw7119step1 := by
      have heq : raw7119step1 = (fun i j => raw7119step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7119step0 permutation27 permutation6
    _ = injectiveMoment H node181 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7171 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7171 = injectiveMoment H node1203 := by
  calc
    injectiveMoment H raw7171 = injectiveMoment H raw7171step0 := by
      have heq : raw7171step0 = -raw7171 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7171).symm
    injectiveMoment H raw7171step0 = injectiveMoment H raw7171step1 := by
      have heq : raw7171step1 = (fun i j => raw7171step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7171step0 permutation25 permutation15
    _ = injectiveMoment H node1203 := by rfl

theorem canonical7181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7181 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw7181 = injectiveMoment H raw7181step0 := by
      have heq : raw7181step0 = raw7181.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7181).symm
    injectiveMoment H raw7181step0 = injectiveMoment H raw7181step1 := by
      have heq : raw7181step1 = -raw7181step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7181step0).symm
    injectiveMoment H raw7181step1 = injectiveMoment H raw7181step2 := by
      have heq : raw7181step2 = (fun i j => raw7181step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7181step1 permutation29 permutation4
    _ = injectiveMoment H node230 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7499 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7499 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw7499 = injectiveMoment H raw7499step0 := by
      have heq : raw7499step0 = -raw7499 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7499).symm
    injectiveMoment H raw7499step0 = injectiveMoment H raw7499step1 := by
      have hz : ∀ i, raw7499step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7499step1 = (fun i j => raw7499step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7499step0 permutation15 hz
    injectiveMoment H raw7499step1 = injectiveMoment H raw7499step2 := by
      have heq : raw7499step2 = (fun i j => raw7499step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7499step1 permutation8 permutation3
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound14
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound939 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node939 = Sparse.eval value939 (momentVector H) := by
  have heq : pivotMatrix939 = (fun u v => node939 (pivotPermutation939 u) v) := by apply Matrix.ext; unfold pivotMatrix939 node939 pivotPermutation939; decide +kernel
  have hmoment : injectiveMoment H node939 = injectiveMoment H pivotMatrix939 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix939 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix939 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix939 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix939 (0 : Fin 3) = raw5725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix939 raw5725; decide +kernel
    rw [heq]
    exact (canonical5725 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix939 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix939 (1 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix939 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix939 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix939 (2 : Fin 3) = raw6331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix939 raw6331; decide +kernel
    rw [heq]
    exact (canonical6331 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node939 + (injectiveMoment H (mergeFirst pivotMatrix939 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix939 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix939 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value939, value185, value229, value271, Sparse.eval] at hc ⊢
  linarith

theorem sound942 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node942 = Sparse.eval value942 (momentVector H) := by
  have heq : pivotMatrix942 = (fun u v => node942 (pivotPermutation942 u) v) := by apply Matrix.ext; unfold pivotMatrix942 node942 pivotPermutation942; decide +kernel
  have hmoment : injectiveMoment H node942 = injectiveMoment H pivotMatrix942 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix942 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix942 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix942 (0 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix942 (0 : Fin 3) = raw7181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix942 raw7181; decide +kernel
    rw [heq]
    exact (canonical7181 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix942 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix942 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix942 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix942 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix942 (2 : Fin 3) = raw6225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix942 raw6225; decide +kernel
    rw [heq]
    exact (canonical6225 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node942 + (injectiveMoment H (mergeFirst pivotMatrix942 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix942 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix942 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value942, value176, value229, value230, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical209
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6693 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw6693 = injectiveMoment H raw6693step0 := by
      have heq : raw6693step0 = raw6693.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6693).symm
    injectiveMoment H raw6693step0 = injectiveMoment H raw6693step1 := by
      have heq : raw6693step1 = (fun i j => raw6693step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6693step0 permutation21 permutation5
    _ = injectiveMoment H node230 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound16
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1044 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1044 = Sparse.eval value1044 (momentVector H) := by
  have heq : pivotMatrix1044 = (fun u v => node1044 (pivotPermutation1044 u) v) := by apply Matrix.ext; unfold pivotMatrix1044 node1044 pivotPermutation1044; decide +kernel
  have hmoment : injectiveMoment H node1044 = injectiveMoment H pivotMatrix1044 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1044 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1044 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1044 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1044 (0 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1044 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1044 (1 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1044 (1 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1044 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1044 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1044 (2 : Fin 3) = raw6543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1044 raw6543; decide +kernel
    rw [heq]
    exact (canonical6543 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1044 + (injectiveMoment H (mergeFirst pivotMatrix1044 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1044 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1044 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1044, value271, value294, value61, Sparse.eval] at hc ⊢
  linarith

theorem sound1079 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1079 = Sparse.eval value1079 (momentVector H) := by
  have heq : pivotMatrix1079 = (fun u v => node1079 (pivotPermutation1079 u) v) := by apply Matrix.ext; unfold pivotMatrix1079 node1079 pivotPermutation1079; decide +kernel
  have hmoment : injectiveMoment H node1079 = injectiveMoment H pivotMatrix1079 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1079 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1079 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1079 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1079 (0 : Fin 3) = raw8099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1079 raw8099; decide +kernel
    rw [heq]
    exact (canonical8099 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1079 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1079 (1 : Fin 3) = raw6566 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1079 raw6566; decide +kernel
    rw [heq]
    exact (canonical6566 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1079 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1079 (2 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1079 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1079 + (injectiveMoment H (mergeFirst pivotMatrix1079 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1079 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1079 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1079, value185, value36, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6966 = injectiveMoment H node942 := by
  calc
    injectiveMoment H raw6966 = injectiveMoment H raw6966step0 := by
      have heq : raw6966step0 = (fun i j => raw6966 (permutation11 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6966 permutation11 permutation13
    _ = injectiveMoment H node942 := by rfl

theorem canonical6967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6967 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6967 = injectiveMoment H raw6967step0 := by
      have heq : raw6967step0 = raw6967.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6967).symm
    injectiveMoment H raw6967step0 = injectiveMoment H raw6967step1 := by
      have heq : raw6967step1 = -raw6967step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6967step0).symm
    injectiveMoment H raw6967step1 = injectiveMoment H raw6967step2 := by
      have heq : raw6967step2 = (fun i j => raw6967step1 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6967step1 permutation16 permutation6
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical244
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7809 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7809 = injectiveMoment H node1283 := by
  calc
    injectiveMoment H raw7809 = injectiveMoment H raw7809step0 := by
      have heq : raw7809step0 = -raw7809 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7809).symm
    injectiveMoment H raw7809step0 = injectiveMoment H raw7809step1 := by
      have heq : raw7809step1 = (fun i j => raw7809step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7809step0 permutation32 permutation10
    _ = injectiveMoment H node1283 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical278
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8898 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8898 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw8898 = injectiveMoment H raw8898step0 := by
      have heq : raw8898step0 = raw8898.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8898).symm
    injectiveMoment H raw8898step0 = injectiveMoment H raw8898step1 := by
      have heq : raw8898step1 = -raw8898step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8898step0).symm
    injectiveMoment H raw8898step1 = injectiveMoment H raw8898step2 := by
      have heq : raw8898step2 = (fun i j => raw8898step1 (permutation22 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8898step1 permutation22 permutation4
    _ = injectiveMoment H node226 := by rfl

theorem canonical8911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8911 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw8911 = injectiveMoment H raw8911step0 := by
      have heq : raw8911step0 = raw8911.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8911).symm
    injectiveMoment H raw8911step0 = injectiveMoment H raw8911step1 := by
      have heq : raw8911step1 = -raw8911step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8911step0).symm
    injectiveMoment H raw8911step1 = injectiveMoment H raw8911step2 := by
      have heq : raw8911step2 = (fun i j => raw8911step1 (permutation22 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8911step1 permutation22 permutation4
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound18
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1203 = Sparse.eval value1203 (momentVector H) := by
  have heq : pivotMatrix1203 = (fun u v => node1203 (pivotPermutation1203 u) v) := by apply Matrix.ext; unfold pivotMatrix1203 node1203 pivotPermutation1203; decide +kernel
  have hmoment : injectiveMoment H node1203 = injectiveMoment H pivotMatrix1203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1203 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1203 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1203 (0 : Fin 3) = raw6326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1203 raw6326; decide +kernel
    rw [heq]
    exact (canonical6326 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1203 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1203 (1 : Fin 3) = raw7106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1203 raw7106; decide +kernel
    rw [heq]
    exact (canonical7106 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1203 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1203 (2 : Fin 3) = raw7119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1203 raw7119; decide +kernel
    rw [heq]
    exact (canonical7119 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1203 + (injectiveMoment H (mergeFirst pivotMatrix1203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1203, value181, value271, value57, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound19
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1249 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1249 = Sparse.eval value1249 (momentVector H) := by
  have heq : pivotMatrix1249 = (fun u v => node1249.transpose (pivotPermutation1249 u) v) := by apply Matrix.ext; unfold pivotMatrix1249 node1249 pivotPermutation1249; decide +kernel
  have hmoment : injectiveMoment H node1249 = injectiveMoment H pivotMatrix1249 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1249 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1249 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1249 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1249 (0 : Fin 3) = raw6910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1249 raw6910; decide +kernel
    rw [heq]
    exact (canonical6910 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1249 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1249 (1 : Fin 3) = raw8898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1249 raw8898; decide +kernel
    rw [heq]
    exact (canonical8898 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1249 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1249 (2 : Fin 3) = raw8911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1249 raw8911; decide +kernel
    rw [heq]
    exact (canonical8911 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1249 + (injectiveMoment H (mergeFirst pivotMatrix1249 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1249 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1249 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1249, value226, value229, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4088 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4088 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw4088 = injectiveMoment H raw4088step0 := by
      have heq : raw4088step0 = -raw4088 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4088).symm
    injectiveMoment H raw4088step0 = injectiveMoment H raw4088step1 := by
      have heq : raw4088step1 = (fun i j => raw4088step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4088step0 permutation28 permutation5
    _ = injectiveMoment H node185 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node708 = Sparse.eval value708 (momentVector H) := by
  have heq : pivotMatrix708 = (fun u v => node708 (pivotPermutation708 u) v) := by apply Matrix.ext; unfold pivotMatrix708 node708 pivotPermutation708; decide +kernel
  have hmoment : injectiveMoment H node708 = injectiveMoment H pivotMatrix708 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix708 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix708 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix708 (0 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (0 : Fin 4) = raw4088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4088; decide +kernel
    rw [heq]
    exact (canonical4088 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix708 (1 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (1 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix708 (2 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (2 : Fin 4) = raw4945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4945; decide +kernel
    rw [heq]
    exact (canonical4945 hH).trans (sound229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix708 (3 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (3 : Fin 4) = raw4946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4946; decide +kernel
    rw [heq]
    exact (canonical4946 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node708 + (injectiveMoment H (mergeFirst pivotMatrix708 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix708 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix708 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix708 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value708, value185, value226, value229, value230, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical254
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8134 = injectiveMoment H node2447 := by
  calc
    injectiveMoment H raw8134 = injectiveMoment H raw8134step0 := by
      have heq : raw8134step0 = (fun i j => raw8134 (permutation116 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8134 permutation116 permutation13
    _ = injectiveMoment H node2447 := by rfl

theorem canonical8137 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8137 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw8137 = injectiveMoment H raw8137step0 := by
      have hz : ∀ i, raw8137 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8137step0 = (fun i j => raw8137 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8137 permutation9 hz
    injectiveMoment H raw8137step0 = injectiveMoment H raw8137step1 := by
      have heq : raw8137step1 = (fun i j => raw8137step0 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8137step0 permutation37 permutation3
    _ = injectiveMoment H node708 := by rfl

theorem canonical8157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8157 = injectiveMoment H node44 := by
  calc
    injectiveMoment H raw8157 = injectiveMoment H raw8157step0 := by
      have hz : ∀ i, raw8157 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8157step0 = (fun i j => raw8157 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8157 permutation9 hz
    _ = injectiveMoment H node44 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound13
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound845 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node845 = Sparse.eval value845 (momentVector H) := by
  have heq : pivotMatrix845 = (fun u v => node845 (pivotPermutation845 u) v) := by apply Matrix.ext; unfold pivotMatrix845 node845 pivotPermutation845; decide +kernel
  have hmoment : injectiveMoment H node845 = injectiveMoment H pivotMatrix845 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix845 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix845 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix845 (0 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix845 (0 : Fin 3) = raw6693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix845 raw6693; decide +kernel
    rw [heq]
    exact (canonical6693 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix845 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix845 (1 : Fin 3) = raw5797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix845 raw5797; decide +kernel
    rw [heq]
    exact (canonical5797 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix845 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix845 (2 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix845 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node845 + (injectiveMoment H (mergeFirst pivotMatrix845 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix845 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix845 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value845, value203, value229, value230, Sparse.eval] at hc ⊢
  linarith

theorem sound846 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node846 = Sparse.eval value846 (momentVector H) := by
  have heq : pivotMatrix846 = (fun u v => node846 (pivotPermutation846 u) v) := by apply Matrix.ext; unfold pivotMatrix846 node846 pivotPermutation846; decide +kernel
  have hmoment : injectiveMoment H node846 = injectiveMoment H pivotMatrix846 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix846 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix846 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix846 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix846 (0 : Fin 3) = raw8157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix846 raw8157; decide +kernel
    rw [heq]
    exact (canonical8157 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix846 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix846 (1 : Fin 3) = raw5806 := by apply Matrix.ext; unfold mergeFirst pivotMatrix846 raw5806; decide +kernel
    rw [heq]
    exact (canonical5806 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix846 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix846 (2 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix846 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node846 + (injectiveMoment H (mergeFirst pivotMatrix846 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix846 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix846 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value846, value210, value229, value44, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound15
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1016 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1016 = Sparse.eval value1016 (momentVector H) := by
  have heq : pivotMatrix1016 = (fun u v => node1016.transpose (pivotPermutation1016 u) v) := by apply Matrix.ext; unfold pivotMatrix1016 node1016 pivotPermutation1016; decide +kernel
  have hmoment : injectiveMoment H node1016 = injectiveMoment H pivotMatrix1016 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1016 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1016 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1016 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1016 (0 : Fin 3) = raw2638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1016 raw2638; decide +kernel
    rw [heq]
    exact (canonical2638 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1016 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1016 (1 : Fin 3) = raw6910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1016 raw6910; decide +kernel
    rw [heq]
    exact (canonical6910 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1016 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1016 (2 : Fin 3) = raw6938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1016 raw6938; decide +kernel
    rw [heq]
    exact (canonical6938 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1016 + (injectiveMoment H (mergeFirst pivotMatrix1016 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1016 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1016 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1016, value111, value226, value229, Sparse.eval] at hc ⊢
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

theorem sound1110 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1110 = Sparse.eval value1110 (momentVector H) := by
  have heq : pivotMatrix1110 = (fun u v => node1110 (pivotPermutation1110 u) v) := by apply Matrix.ext; unfold pivotMatrix1110 node1110 pivotPermutation1110; decide +kernel
  have hmoment : injectiveMoment H node1110 = injectiveMoment H pivotMatrix1110 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1110 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1110 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1110 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1110 (0 : Fin 3) = raw7499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1110 raw7499; decide +kernel
    rw [heq]
    exact (canonical7499 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1110 (1 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1110 (1 : Fin 3) = raw6693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1110 raw6693; decide +kernel
    rw [heq]
    exact (canonical6693 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1110 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1110 (2 : Fin 3) = raw6640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1110 raw6640; decide +kernel
    rw [heq]
    exact (canonical6640 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1110 + (injectiveMoment H (mergeFirst pivotMatrix1110 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1110 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1110 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1110, value176, value230, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound20
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1283 = Sparse.eval value1283 (momentVector H) := by
  have heq : pivotMatrix1283 = (fun u v => node1283 (pivotPermutation1283 u) v) := by apply Matrix.ext; unfold pivotMatrix1283 node1283 pivotPermutation1283; decide +kernel
  have hmoment : injectiveMoment H node1283 = injectiveMoment H pivotMatrix1283 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1283 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1283 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1283 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1283 (0 : Fin 3) = raw6967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1283 raw6967; decide +kernel
    rw [heq]
    exact (canonical6967 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1283 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1283 (1 : Fin 3) = raw8939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1283 raw8939; decide +kernel
    rw [heq]
    exact (canonical8939 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1283 (2 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1283 (2 : Fin 3) = raw8945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1283 raw8945; decide +kernel
    rw [heq]
    exact (canonical8945 hH).trans (sound43 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1283 + (injectiveMoment H (mergeFirst pivotMatrix1283 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1283 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1283 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1283, value226, value229, value43, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound38
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2447 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2447 = Sparse.eval value2447 (momentVector H) := by
  have heq : pivotMatrix2447 = (fun u v => node2447 (pivotPermutation2447 u) v) := by apply Matrix.ext; unfold pivotMatrix2447 node2447 pivotPermutation2447; decide +kernel
  have hmoment : injectiveMoment H node2447 = injectiveMoment H pivotMatrix2447 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2447 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2447 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2447 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2447 (0 : Fin 4) = raw5836 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2447 raw5836; decide +kernel
    rw [heq]
    exact (canonical5836 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2447 (1 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2447 (1 : Fin 4) = raw5783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2447 raw5783; decide +kernel
    rw [heq]
    exact (canonical5783 hH).trans (sound1044 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2447 (2 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2447 (2 : Fin 4) = raw5778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2447 raw5778; decide +kernel
    rw [heq]
    exact (canonical5778 hH).trans (sound846 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2447 (3 : Fin 4)) =
      Sparse.eval value845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2447 (3 : Fin 4) = raw5777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2447 raw5777; decide +kernel
    rw [heq]
    exact (canonical5777 hH).trans (sound845 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2447 + (injectiveMoment H (mergeFirst pivotMatrix2447 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2447 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2447 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2447 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2447, value1044, value1110, value845, value846, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical223
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7158 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7158 = injectiveMoment H node1016 := by
  calc
    injectiveMoment H raw7158 = injectiveMoment H raw7158step0 := by
      have heq : raw7158step0 = -raw7158 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7158).symm
    injectiveMoment H raw7158step0 = injectiveMoment H raw7158step1 := by
      have heq : raw7158step1 = (fun i j => raw7158step0 (permutation32 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7158step0 permutation32 permutation10
    _ = injectiveMoment H node1016 := by rfl

theorem canonical7159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7159 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw7159 = injectiveMoment H raw7159step0 := by
      have heq : raw7159step0 = (fun i j => raw7159 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7159 permutation9 permutation11
    _ = injectiveMoment H node1079 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound42
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2717 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2717 = Sparse.eval value2717 (momentVector H) := by
  have heq : pivotMatrix2717 = (fun u v => node2717 (pivotPermutation2717 u) v) := by apply Matrix.ext; unfold pivotMatrix2717 node2717 pivotPermutation2717; decide +kernel
  have hmoment : injectiveMoment H node2717 = injectiveMoment H pivotMatrix2717 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2717 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2717 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2717 (0 : Fin 4)) =
      Sparse.eval value1283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2717 (0 : Fin 4) = raw7809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2717 raw7809; decide +kernel
    rw [heq]
    exact (canonical7809 hH).trans (sound1283 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2717 (1 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2717 (1 : Fin 4) = raw7171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2717 raw7171; decide +kernel
    rw [heq]
    exact (canonical7171 hH).trans (sound1203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2717 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2717 (2 : Fin 4) = raw7159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2717 raw7159; decide +kernel
    rw [heq]
    exact (canonical7159 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2717 (3 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2717 (3 : Fin 4) = raw7158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2717 raw7158; decide +kernel
    rw [heq]
    exact (canonical7158 hH).trans (sound1016 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2717 + (injectiveMoment H (mergeFirst pivotMatrix2717 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2717 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2717 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2717 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2717, value1016, value1079, value1203, value1283, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound43
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2779 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2779 = Sparse.eval value2779 (momentVector H) := by
  have heq : pivotMatrix2779 = (fun u v => node2779 (pivotPermutation2779 u) v) := by apply Matrix.ext; unfold pivotMatrix2779 node2779 pivotPermutation2779; decide +kernel
  have hmoment : injectiveMoment H node2779 = injectiveMoment H pivotMatrix2779 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2779 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2779 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2779 (0 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2779 (0 : Fin 4) = raw6966 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2779 raw6966; decide +kernel
    rw [heq]
    exact (canonical6966 hH).trans (sound942 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2779 (1 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2779 (1 : Fin 4) = raw8938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2779 raw8938; decide +kernel
    rw [heq]
    exact (canonical8938 hH).trans (sound1249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2779 (2 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2779 (2 : Fin 4) = raw8941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2779 raw8941; decide +kernel
    rw [heq]
    exact (canonical8941 hH).trans (sound939 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2779 (3 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2779 (3 : Fin 4) = raw8944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2779 raw8944; decide +kernel
    rw [heq]
    exact (canonical8944 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2779 + (injectiveMoment H (mergeFirst pivotMatrix2779 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2779 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2779 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2779 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2779, value1249, value229, value939, value942, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound53
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3430 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3430 = Sparse.eval value3430 (momentVector H) := by
  have heq : pivotMatrix3430 = (fun u v => node3430 (pivotPermutation3430 u) v) := by apply Matrix.ext; unfold pivotMatrix3430 node3430 pivotPermutation3430; decide +kernel
  have hmoment : injectiveMoment H node3430 = injectiveMoment H pivotMatrix3430 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3430 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3430 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3430 (0 : Fin 5)) =
      Sparse.eval value2444 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3430 (0 : Fin 5) = raw5750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3430 raw5750; decide +kernel
    rw [heq]
    exact (canonical5750 hH).trans (sound2444_e hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3430 (1 : Fin 5)) =
      Sparse.eval value2717 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3430 (1 : Fin 5) = raw8111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3430 raw8111; decide +kernel
    rw [heq]
    exact (canonical8111 hH).trans (sound2717 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3430 (2 : Fin 5)) =
      Sparse.eval value2779 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3430 (2 : Fin 5) = raw8124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3430 raw8124; decide +kernel
    rw [heq]
    exact (canonical8124 hH).trans (sound2779 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3430 (3 : Fin 5)) =
      Sparse.eval value2447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3430 (3 : Fin 5) = raw8134 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3430 raw8134; decide +kernel
    rw [heq]
    exact (canonical8134 hH).trans (sound2447 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3430 (4 : Fin 5)) =
      Sparse.eval value708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3430 (4 : Fin 5) = raw8137 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3430 raw8137; decide +kernel
    rw [heq]
    exact (canonical8137 hH).trans (sound708 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3430 + (injectiveMoment H (mergeFirst pivotMatrix3430 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3430 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3430 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3430 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3430 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3430, value2444, value2447, value2717, value2779, value708, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary13
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound385 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow385 (momentVector H) = 0 := by
  have hshape : boundaryMatrix385 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix385 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix385 (0 : Fin 6)) =
      Sparse.eval value3151 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (0 : Fin 6) = raw8080 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8080 hH).trans (sound3151_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix385 (1 : Fin 6)) =
      Sparse.eval value3194 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (1 : Fin 6) = raw8384 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8384 hH).trans (sound3194_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix385 (2 : Fin 6)) =
      Sparse.eval value3348 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (2 : Fin 6) = raw8441 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8441 hH).trans (sound3348_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix385 (3 : Fin 6)) =
      Sparse.eval value3202 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (3 : Fin 6) = raw8453 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8453 hH).trans (sound3202_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix385 (4 : Fin 6)) =
      Sparse.eval value3021 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (4 : Fin 6) = raw8455 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8455 hH).trans (sound3021_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix385 (5 : Fin 6)) =
      Sparse.eval value3430 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix385 (5 : Fin 6) = raw8457 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8457 hH).trans (sound3430 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix385 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix385 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow385, value3021, value3151, value3194, value3202, value3348, value3430, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck213 : Integer.Sparse.reindex coordinateMap (PairData.rows 213) =
    PairSemantics.boundaryRow385 := by decide +kernel

theorem rowSound213_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 213) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck213]
  exact PairSemantics.boundarySound385 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e_oai
