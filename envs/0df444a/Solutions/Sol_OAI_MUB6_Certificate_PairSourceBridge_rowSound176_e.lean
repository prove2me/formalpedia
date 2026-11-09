-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T13:44:39.959213+00:00
-- url     : https://prove2.me/submissions/5427ce92-9db6-4e86-995e-1dd70b1d16e3

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2897_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2989_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2992_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3400_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical286
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9161 = injectiveMoment H node2982 := by
  calc
    injectiveMoment H raw9161 = injectiveMoment H raw9161step0 := by
      have heq : raw9161step0 = (fun i j => raw9161 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9161 permutation259 permutation9
    _ = injectiveMoment H node2982 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical299
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9579 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9579 = injectiveMoment H node2989 := by
  calc
    injectiveMoment H raw9579 = injectiveMoment H raw9579step0 := by
      have heq : raw9579step0 = (fun i j => raw9579 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9579 permutation259 permutation9
    _ = injectiveMoment H node2989 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical300
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9615 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9615 = injectiveMoment H node2989 := by
  calc
    injectiveMoment H raw9615 = injectiveMoment H raw9615step0 := by
      have heq : raw9615step0 = (fun i j => raw9615 (permutation265 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9615 permutation265 permutation9
    _ = injectiveMoment H node2989 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical301
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9633 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9633 = injectiveMoment H node2992 := by
  calc
    injectiveMoment H raw9633 = injectiveMoment H raw9633step0 := by
      have heq : raw9633step0 = (fun i j => raw9633 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9633 permutation259 permutation9
    _ = injectiveMoment H node2992 := by rfl

theorem canonical9640 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9640 = injectiveMoment H node2897 := by
  calc
    injectiveMoment H raw9640 = injectiveMoment H raw9640step0 := by
      have heq : raw9640step0 = (fun i j => raw9640 (permutation258 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9640 permutation258 permutation11
    _ = injectiveMoment H node2897 := by rfl

theorem canonical9641 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9641 = injectiveMoment H node3400 := by
  calc
    injectiveMoment H raw9641 = injectiveMoment H raw9641step0 := by
      have heq : raw9641step0 = -raw9641 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9641).symm
    injectiveMoment H raw9641step0 = injectiveMoment H raw9641step1 := by
      have heq : raw9641step1 = (fun i j => raw9641step0 (permutation380 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9641step0 permutation380 permutation21
    _ = injectiveMoment H node3400 := by rfl

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

theorem canonical5703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5703 = injectiveMoment H node816 := by
  rfl

theorem canonical5705 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5705 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw5705 = injectiveMoment H raw5705step0 := by
      have heq : raw5705step0 = raw5705.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5705).symm
    injectiveMoment H raw5705step0 = injectiveMoment H raw5705step1 := by
      have heq : raw5705step1 = (fun i j => raw5705step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5705step0 permutation21 permutation5
    _ = injectiveMoment H node206 := by rfl

theorem canonical5722 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5722 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw5722 = injectiveMoment H raw5722step0 := by
      have heq : raw5722step0 = raw5722.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5722).symm
    injectiveMoment H raw5722step0 = injectiveMoment H raw5722step1 := by
      have heq : raw5722step1 = (fun i j => raw5722step0 (permutation26 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5722step0 permutation26 permutation7
    _ = injectiveMoment H node215 := by rfl

theorem canonical5727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5727 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw5727 = injectiveMoment H raw5727step0 := by
      have heq : raw5727step0 = raw5727.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5727).symm
    injectiveMoment H raw5727step0 = injectiveMoment H raw5727step1 := by
      have heq : raw5727step1 = (fun i j => raw5727step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5727step0 permutation23 permutation7
    _ = injectiveMoment H node201 := by rfl

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

theorem canonical1420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1420 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1420 = injectiveMoment H raw1420step0 := by
      have heq : raw1420step0 = raw1420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1420).symm
    injectiveMoment H raw1420step0 = injectiveMoment H raw1420step1 := by
      have heq : raw1420step1 = (fun i j => raw1420step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1420step0 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

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

theorem canonical344 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw344 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw344 = injectiveMoment H raw344step0 := by
      have heq : raw344step0 = raw344.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw344).symm
    injectiveMoment H raw344step0 = injectiveMoment H raw344step1 := by
      have heq : raw344step1 = -raw344step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw344step0).symm
    injectiveMoment H raw344step1 = injectiveMoment H raw344step2 := by
      have heq : raw344step2 = (fun i j => raw344step1 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw344step1 permutation25 permutation5
    _ = injectiveMoment H node163 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical365 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw365 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw365 = injectiveMoment H raw365step0 := by
      have heq : raw365step0 = raw365.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw365).symm
    injectiveMoment H raw365step0 = injectiveMoment H raw365step1 := by
      have heq : raw365step1 = (fun i j => raw365step0 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw365step0 permutation17 permutation5
    _ = injectiveMoment H node212 := by rfl

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

theorem canonical4157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4157 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4157 = injectiveMoment H raw4157step0 := by
      have heq : raw4157step0 = raw4157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4157).symm
    injectiveMoment H raw4157step0 = injectiveMoment H raw4157step1 := by
      have heq : raw4157step1 = -raw4157step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4157step0).symm
    injectiveMoment H raw4157step1 = injectiveMoment H raw4157step2 := by
      have heq : raw4157step2 = (fun i j => raw4157step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4157step1 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

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

theorem canonical4181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4181 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw4181 = injectiveMoment H raw4181step0 := by
      have heq : raw4181step0 = raw4181.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4181).symm
    injectiveMoment H raw4181step0 = injectiveMoment H raw4181step1 := by
      have heq : raw4181step1 = (fun i j => raw4181step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4181step0 permutation10 permutation3
    _ = injectiveMoment H node197 := by rfl

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

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5647 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5647 = injectiveMoment H node791 := by
  rfl

theorem canonical5649 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5649 = injectiveMoment H node795 := by
  rfl

theorem canonical5650 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5650 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw5650 = injectiveMoment H raw5650step0 := by
      have heq : raw5650step0 = raw5650.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5650).symm
    injectiveMoment H raw5650step0 = injectiveMoment H raw5650step1 := by
      have heq : raw5650step1 = -raw5650step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5650step0).symm
    injectiveMoment H raw5650step1 = injectiveMoment H raw5650step2 := by
      have heq : raw5650step2 = (fun i j => raw5650step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5650step1 permutation27 permutation5
    _ = injectiveMoment H node120 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical955 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw955 = injectiveMoment H node27 := by
  rfl

theorem canonical958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw958 = injectiveMoment H node28 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2127 = injectiveMoment H node496 := by
  calc
    injectiveMoment H raw2127 = injectiveMoment H raw2127step0 := by
      have heq : raw2127step0 = (fun i j => raw2127 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2127 permutation12 permutation9
    _ = injectiveMoment H node496 := by rfl

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

theorem canonical2860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2860 = injectiveMoment H node40 := by
  rfl

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

theorem canonical8216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8216 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8216 = injectiveMoment H raw8216step0 := by
      have hz : ∀ j, raw8216 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw8216step0 = (fun i j => raw8216 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8216 permutation7 hz
    injectiveMoment H raw8216step0 = injectiveMoment H raw8216step1 := by
      have hz : ∀ i, raw8216step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8216step1 = (fun i j => raw8216step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8216step0 permutation3 hz
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

theorem sound27 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node27 = Sparse.eval value27 (momentVector H) := by
  have hc : momentVector H 69 = injectiveMoment H node27 := rfl
  simp [value27, Sparse.eval, hc]

theorem sound28 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node28 = Sparse.eval value28 (momentVector H) := by
  have hc : momentVector H 70 = injectiveMoment H node28 := rfl
  simp [value28, Sparse.eval, hc]

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound40 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node40 = Sparse.eval value40 (momentVector H) := by
  have hc : momentVector H 52 = injectiveMoment H node40 := rfl
  simp [value40, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4048 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw4048 = injectiveMoment H raw4048step0 := by
      have heq : raw4048step0 = -raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4048).symm
    injectiveMoment H raw4048step0 = injectiveMoment H raw4048step1 := by
      have heq : raw4048step1 = (fun i j => raw4048step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4048step0 permutation8 permutation3
    _ = injectiveMoment H node31 := by rfl

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

theorem sound120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node120 = Sparse.eval value120 (momentVector H) := by
  have heq : pivotMatrix120 = (fun u v => node120 (pivotPermutation120 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node120 = injectiveMoment H pivotMatrix120 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix120 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix120 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix120 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix120 (0 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix120 (1 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix120 (1 : Fin 3) = raw958 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical958 hH).trans (sound28 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix120 (2 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix120 (2 : Fin 3) = raw955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical955 hH).trans (sound27 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node120 + (injectiveMoment H (mergeFirst pivotMatrix120 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix120 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix120 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value120, value27, value28, value31, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6789 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6789 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw6789 = injectiveMoment H raw6789step0 := by
      have heq : raw6789step0 = -raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6789).symm
    injectiveMoment H raw6789step0 = injectiveMoment H raw6789step1 := by
      have heq : raw6789step1 = (fun i j => raw6789step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6789step0 permutation8 permutation3
    _ = injectiveMoment H node52 := by rfl

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

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
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

theorem sound145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node145 = Sparse.eval value145 (momentVector H) := by
  have heq : pivotMatrix145 = (fun u v => node145 (pivotPermutation145 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node145 = injectiveMoment H pivotMatrix145 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix145 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix145 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (0 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (1 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (2 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node145 + (injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value145, value31, value52, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node163 = Sparse.eval value163 (momentVector H) := by
  have hc : momentVector H 125 = injectiveMoment H node163 := rfl
  simp [value163, Sparse.eval, hc]

theorem sound167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node167 = Sparse.eval value167 (momentVector H) := by
  have hc : momentVector H 126 = injectiveMoment H node167 := rfl
  simp [value167, Sparse.eval, hc]

theorem sound169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node169 = Sparse.eval value169 (momentVector H) := by
  have heq : pivotMatrix169 = (fun u v => node169 (pivotPermutation169 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node169 = injectiveMoment H pivotMatrix169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix169 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (0 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (1 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node169 + (injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value169, value31, value36, value57, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node197 = Sparse.eval value197 (momentVector H) := by
  have hc : momentVector H 23 = injectiveMoment H node197 := rfl
  simp [value197, Sparse.eval, hc]

theorem sound198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node198 = Sparse.eval value198 (momentVector H) := by
  have hc : momentVector H 54 = injectiveMoment H node198 := rfl
  simp [value198, Sparse.eval, hc]

theorem sound201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node201 = Sparse.eval value201 (momentVector H) := by
  have heq : pivotMatrix201 = (fun u v => node201 (pivotPermutation201 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node201 = injectiveMoment H pivotMatrix201 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix201 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix201 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (0 : Fin 3) = raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (2 : Fin 3) = raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4048 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node201 + (injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value201, value31, value32, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node202 = Sparse.eval value202 (momentVector H) := by
  have hc : momentVector H 24 = injectiveMoment H node202 := rfl
  simp [value202, Sparse.eval, hc]

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

theorem sound206 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node206 = Sparse.eval value206 (momentVector H) := by
  have heq : pivotMatrix206 = (fun u v => node206 (pivotPermutation206 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node206 = injectiveMoment H pivotMatrix206 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix206 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix206 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix206 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (0 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix206 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix206 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node206 + (injectiveMoment H (mergeFirst pivotMatrix206 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix206 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix206 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value206, value32, value36, value40, Sparse.eval] at hc ⊢
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

theorem sound212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node212 = Sparse.eval value212 (momentVector H) := by
  have hc : momentVector H 55 = injectiveMoment H node212 := rfl
  simp [value212, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8167 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8167 = injectiveMoment H raw8167step0 := by
      have heq : raw8167step0 = (fun i j => raw8167 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8167 permutation5 permutation4
    _ = injectiveMoment H node62 := by rfl

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

theorem sound284 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node284 = Sparse.eval value284 (momentVector H) := by
  have heq : pivotMatrix284 = (fun u v => node284 (pivotPermutation284 u) v) := by apply Matrix.ext; unfold pivotMatrix284 node284 pivotPermutation284; decide +kernel
  have hmoment : injectiveMoment H node284 = injectiveMoment H pivotMatrix284 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix284 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix284 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix284 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix284 (0 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix284 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix284 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix284 (1 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix284 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix284 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix284 (2 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix284 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node284 + (injectiveMoment H (mergeFirst pivotMatrix284 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix284 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix284 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value284, value57, value61, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node291 = Sparse.eval value291 (momentVector H) := by
  have heq : pivotMatrix291 = (fun u v => node291 (pivotPermutation291 u) v) := by apply Matrix.ext; unfold pivotMatrix291 node291 pivotPermutation291; decide +kernel
  have hmoment : injectiveMoment H node291 = injectiveMoment H pivotMatrix291 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix291 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix291 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (0 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (1 : Fin 3) = raw8167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8167; decide +kernel
    rw [heq]
    exact (canonical8167 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (2 : Fin 3) = raw8216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8216; decide +kernel
    rw [heq]
    exact (canonical8216 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node291 + (injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value291, value4, value57, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3649 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3649 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw3649 = injectiveMoment H raw3649step0 := by
      have heq : raw3649step0 = raw3649.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3649).symm
    injectiveMoment H raw3649step0 = injectiveMoment H raw3649step1 := by
      have heq : raw3649step1 = (fun i j => raw3649step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3649step0 permutation10 permutation3
    _ = injectiveMoment H node167 := by rfl

theorem canonical3675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3675 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw3675 = injectiveMoment H raw3675step0 := by
      have heq : raw3675step0 = raw3675.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3675).symm
    injectiveMoment H raw3675step0 = injectiveMoment H raw3675step1 := by
      have heq : raw3675step1 = -raw3675step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3675step0).symm
    injectiveMoment H raw3675step1 = injectiveMoment H raw3675step2 := by
      have heq : raw3675step2 = (fun i j => raw3675step1 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3675step1 permutation25 permutation5
    _ = injectiveMoment H node169 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4197 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw4197 = injectiveMoment H raw4197step0 := by
      have heq : raw4197step0 = raw4197.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4197).symm
    injectiveMoment H raw4197step0 = injectiveMoment H raw4197step1 := by
      have heq : raw4197step1 = (fun i j => raw4197step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4197step0 permutation13 permutation3
    _ = injectiveMoment H node197 := by rfl

theorem canonical4208 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4208 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4208 = injectiveMoment H raw4208step0 := by
      have heq : raw4208step0 = raw4208.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4208).symm
    injectiveMoment H raw4208step0 = injectiveMoment H raw4208step1 := by
      have heq : raw4208step1 = -raw4208step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4208step0).symm
    injectiveMoment H raw4208step1 = injectiveMoment H raw4208step2 := by
      have heq : raw4208step2 = (fun i j => raw4208step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4208step1 permutation26 permutation3
    _ = injectiveMoment H node203 := by rfl

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

theorem canonical5728 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5728 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw5728 = injectiveMoment H raw5728step0 := by
      have heq : raw5728step0 = raw5728.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5728).symm
    injectiveMoment H raw5728step0 = injectiveMoment H raw5728step1 := by
      have heq : raw5728step1 = (fun i j => raw5728step0 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5728step0 permutation23 permutation5
    _ = injectiveMoment H node201 := by rfl

theorem canonical5732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5732 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw5732 = injectiveMoment H raw5732step0 := by
      have heq : raw5732step0 = raw5732.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5732).symm
    injectiveMoment H raw5732step0 = injectiveMoment H raw5732step1 := by
      have heq : raw5732step1 = (fun i j => raw5732step0 (permutation26 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5732step0 permutation26 permutation5
    _ = injectiveMoment H node215 := by rfl

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

theorem canonical5813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5813 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw5813 = injectiveMoment H raw5813step0 := by
      have heq : raw5813step0 = raw5813.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5813).symm
    injectiveMoment H raw5813step0 = injectiveMoment H raw5813step1 := by
      have heq : raw5813step1 = -raw5813step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5813step0).symm
    injectiveMoment H raw5813step1 = injectiveMoment H raw5813step2 := by
      have heq : raw5813step2 = (fun i j => raw5813step1 (permutation9 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5813step1 permutation9 permutation7
    _ = injectiveMoment H node111 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical201
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6434 = injectiveMoment H node831 := by
  calc
    injectiveMoment H raw6434 = injectiveMoment H raw6434step0 := by
      have heq : raw6434step0 = -raw6434 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6434).symm
    injectiveMoment H raw6434step0 = injectiveMoment H raw6434step1 := by
      have heq : raw6434step1 = (fun i j => raw6434step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6434step0 permutation32 permutation11
    _ = injectiveMoment H node831 := by rfl

theorem canonical6437 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6437 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw6437 = injectiveMoment H raw6437step0 := by
      have heq : raw6437step0 = raw6437.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6437).symm
    injectiveMoment H raw6437step0 = injectiveMoment H raw6437step1 := by
      have heq : raw6437step1 = -raw6437step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6437step0).symm
    injectiveMoment H raw6437step1 = injectiveMoment H raw6437step2 := by
      have heq : raw6437step2 = (fun i j => raw6437step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6437step1 permutation27 permutation5
    _ = injectiveMoment H node145 := by rfl

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

theorem canonical6552 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6552 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6552 = injectiveMoment H raw6552step0 := by
      have heq : raw6552step0 = raw6552.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6552).symm
    injectiveMoment H raw6552step0 = injectiveMoment H raw6552step1 := by
      have heq : raw6552step1 = -raw6552step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6552step0).symm
    injectiveMoment H raw6552step1 = injectiveMoment H raw6552step2 := by
      have heq : raw6552step2 = (fun i j => raw6552step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6552step1 permutation31 permutation4
    _ = injectiveMoment H node185 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical8069 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8069 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw8069 = injectiveMoment H raw8069step0 := by
      have heq : raw8069step0 = -raw8069 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8069).symm
    injectiveMoment H raw8069step0 = injectiveMoment H raw8069step1 := by
      have hz : ∀ i, raw8069step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8069step1 = (fun i j => raw8069step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8069step0 permutation9 hz
    injectiveMoment H raw8069step1 = injectiveMoment H raw8069step2 := by
      have heq : raw8069step2 = (fun i j => raw8069step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8069step1 permutation8 permutation3
    _ = injectiveMoment H node31 := by rfl

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound12
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound791 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node791 = Sparse.eval value791 (momentVector H) := by
  have heq : pivotMatrix791 = (fun u v => node791.transpose (pivotPermutation791 u) v) := by apply Matrix.ext; unfold pivotMatrix791 node791 pivotPermutation791; decide +kernel
  have hmoment : injectiveMoment H node791 = injectiveMoment H pivotMatrix791 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix791 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix791 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix791 (0 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix791 (0 : Fin 3) = raw344 := by apply Matrix.ext; unfold mergeFirst pivotMatrix791 raw344; decide +kernel
    rw [heq]
    exact (canonical344 hH).trans (sound163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix791 (1 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix791 (1 : Fin 3) = raw3649 := by apply Matrix.ext; unfold mergeFirst pivotMatrix791 raw3649; decide +kernel
    rw [heq]
    exact (canonical3649 hH).trans (sound167 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix791 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix791 (2 : Fin 3) = raw3675 := by apply Matrix.ext; unfold mergeFirst pivotMatrix791 raw3675; decide +kernel
    rw [heq]
    exact (canonical3675 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node791 + (injectiveMoment H (mergeFirst pivotMatrix791 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix791 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix791 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value791, value163, value167, value169, Sparse.eval] at hc ⊢
  linarith

theorem sound795 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node795 = Sparse.eval value795 (momentVector H) := by
  have heq : pivotMatrix795 = (fun u v => node795 (pivotPermutation795 u) v) := by apply Matrix.ext; unfold pivotMatrix795 node795 pivotPermutation795; decide +kernel
  have hmoment : injectiveMoment H node795 = injectiveMoment H pivotMatrix795 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix795 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix795 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix795 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix795 (0 : Fin 3) = raw8069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix795 raw8069; decide +kernel
    rw [heq]
    exact (canonical8069 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix795 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix795 (1 : Fin 3) = raw5728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix795 raw5728; decide +kernel
    rw [heq]
    exact (canonical5728 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix795 (2 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix795 (2 : Fin 3) = raw5650 := by apply Matrix.ext; unfold mergeFirst pivotMatrix795 raw5650; decide +kernel
    rw [heq]
    exact (canonical5650 hH).trans (sound120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node795 + (injectiveMoment H (mergeFirst pivotMatrix795 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix795 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix795 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value795, value120, value201, value31, Sparse.eval] at hc ⊢
  linarith

theorem sound816 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node816 = Sparse.eval value816 (momentVector H) := by
  have heq : pivotMatrix816 = (fun u v => node816 (pivotPermutation816 u) v) := by apply Matrix.ext; unfold pivotMatrix816 node816 pivotPermutation816; decide +kernel
  have hmoment : injectiveMoment H node816 = injectiveMoment H pivotMatrix816 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix816 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix816 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix816 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix816 (0 : Fin 3) = raw8099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix816 raw8099; decide +kernel
    rw [heq]
    exact (canonical8099 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix816 (1 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix816 (1 : Fin 3) = raw5732 := by apply Matrix.ext; unfold mergeFirst pivotMatrix816 raw5732; decide +kernel
    rw [heq]
    exact (canonical5732 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix816 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix816 (2 : Fin 3) = raw5705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix816 raw5705; decide +kernel
    rw [heq]
    exact (canonical5705 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node816 + (injectiveMoment H (mergeFirst pivotMatrix816 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix816 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix816 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value816, value206, value215, value36, Sparse.eval] at hc ⊢
  linarith

theorem sound819 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node819 = Sparse.eval value819 (momentVector H) := by
  have heq : pivotMatrix819 = (fun u v => node819 (pivotPermutation819 u) v) := by apply Matrix.ext; unfold pivotMatrix819 node819 pivotPermutation819; decide +kernel
  have hmoment : injectiveMoment H node819 = injectiveMoment H pivotMatrix819 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix819 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix819 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix819 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix819 (0 : Fin 3) = raw6552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix819 raw6552; decide +kernel
    rw [heq]
    exact (canonical6552 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix819 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix819 (1 : Fin 3) = raw5727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix819 raw5727; decide +kernel
    rw [heq]
    exact (canonical5727 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix819 (2 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix819 (2 : Fin 3) = raw5722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix819 raw5722; decide +kernel
    rw [heq]
    exact (canonical5722 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node819 + (injectiveMoment H (mergeFirst pivotMatrix819 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix819 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix819 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value819, value185, value201, value215, Sparse.eval] at hc ⊢
  linarith

theorem sound831 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node831 = Sparse.eval value831 (momentVector H) := by
  have heq : pivotMatrix831 = (fun u v => node831.transpose (pivotPermutation831 u) v) := by apply Matrix.ext; unfold pivotMatrix831 node831 pivotPermutation831; decide +kernel
  have hmoment : injectiveMoment H node831 = injectiveMoment H pivotMatrix831 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix831 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix831 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix831 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix831 (0 : Fin 3) = raw365 := by apply Matrix.ext; unfold mergeFirst pivotMatrix831 raw365; decide +kernel
    rw [heq]
    exact (canonical365 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix831 (1 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix831 (1 : Fin 3) = raw4181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix831 raw4181; decide +kernel
    rw [heq]
    exact (canonical4181 hH).trans (sound197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix831 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix831 (2 : Fin 3) = raw4208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix831 raw4208; decide +kernel
    rw [heq]
    exact (canonical4208 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node831 + (injectiveMoment H (mergeFirst pivotMatrix831 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix831 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix831 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value831, value197, value203, value212, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical6935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6935 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw6935 = injectiveMoment H raw6935step0 := by
      have heq : raw6935step0 = raw6935.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6935).symm
    injectiveMoment H raw6935step0 = injectiveMoment H raw6935step1 := by
      have heq : raw6935step1 = (fun i j => raw6935step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6935step0 permutation28 permutation5
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8227 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw8227 = injectiveMoment H raw8227step0 := by
      have heq : raw8227step0 = raw8227.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8227).symm
    injectiveMoment H raw8227step0 = injectiveMoment H raw8227step1 := by
      have heq : raw8227step1 = (fun i j => raw8227step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8227step0 permutation19 permutation4
    _ = injectiveMoment H node198 := by rfl

theorem canonical8235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8235 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw8235 = injectiveMoment H raw8235step0 := by
      have heq : raw8235step0 = raw8235.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8235).symm
    injectiveMoment H raw8235step0 = injectiveMoment H raw8235step1 := by
      have heq : raw8235step1 = (fun i j => raw8235step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8235step0 permutation19 permutation4
    _ = injectiveMoment H node203 := by rfl

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

theorem canonical7511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7511 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7511 = injectiveMoment H raw7511step0 := by
      have heq : raw7511step0 = raw7511.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7511).symm
    injectiveMoment H raw7511step0 = injectiveMoment H raw7511step1 := by
      have heq : raw7511step1 = (fun i j => raw7511step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7511step0 permutation13 permutation3
    _ = injectiveMoment H node291 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7539 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7539 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw7539 = injectiveMoment H raw7539step0 := by
      have heq : raw7539step0 = raw7539.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7539).symm
    injectiveMoment H raw7539step0 = injectiveMoment H raw7539step1 := by
      have heq : raw7539step1 = -raw7539step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7539step0).symm
    injectiveMoment H raw7539step1 = injectiveMoment H raw7539step2 := by
      have heq : raw7539step2 = (fun i j => raw7539step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7539step1 permutation23 permutation3
    _ = injectiveMoment H node202 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical200
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6431 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6431 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw6431 = injectiveMoment H raw6431step0 := by
      have heq : raw6431step0 = (fun i j => raw6431 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6431 permutation10 permutation15
    _ = injectiveMoment H node1032 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical203
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6509 = injectiveMoment H node1059 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7333 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7333 = injectiveMoment H raw7333step0 := by
      have heq : raw7333step0 = -raw7333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7333).symm
    injectiveMoment H raw7333step0 = injectiveMoment H raw7333step1 := by
      have hz : ∀ i, raw7333step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7333step1 = (fun i j => raw7333step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7333step0 permutation15 hz
    injectiveMoment H raw7333step1 = injectiveMoment H raw7333step2 := by
      have heq : raw7333step2 = (fun i j => raw7333step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7333step1 permutation8 permutation3
    _ = injectiveMoment H node57 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8368 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8368 = injectiveMoment H node1311 := by
  calc
    injectiveMoment H raw8368 = injectiveMoment H raw8368step0 := by
      have heq : raw8368step0 = (fun i j => raw8368 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8368 permutation15 permutation9
    _ = injectiveMoment H node1311 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7585 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7585 = injectiveMoment H raw7585step0 := by
      have heq : raw7585step0 = raw7585.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7585).symm
    injectiveMoment H raw7585step0 = injectiveMoment H raw7585step1 := by
      have heq : raw7585step1 = (fun i j => raw7585step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7585step0 permutation28 permutation5
    _ = injectiveMoment H node284 := by rfl

theorem canonical7590 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7590 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw7590 = injectiveMoment H raw7590step0 := by
      have heq : raw7590step0 = raw7590.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7590).symm
    injectiveMoment H raw7590step0 = injectiveMoment H raw7590step1 := by
      have heq : raw7590step1 = -raw7590step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7590step0).symm
    injectiveMoment H raw7590step1 = injectiveMoment H raw7590step2 := by
      have heq : raw7590step2 = (fun i j => raw7590step1 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7590step1 permutation15 permutation5
    _ = injectiveMoment H node210 := by rfl

theorem canonical7591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7591 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw7591 = injectiveMoment H raw7591step0 := by
      have heq : raw7591step0 = raw7591.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7591).symm
    injectiveMoment H raw7591step0 = injectiveMoment H raw7591step1 := by
      have heq : raw7591step1 = (fun i j => raw7591step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7591step0 permutation28 permutation5
    _ = injectiveMoment H node169 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical265
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8489 = injectiveMoment H node1316 := by
  calc
    injectiveMoment H raw8489 = injectiveMoment H raw8489step0 := by
      have heq : raw8489step0 = (fun i j => raw8489 (permutation21 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8489 permutation21 permutation11
    _ = injectiveMoment H node1316 := by rfl

theorem canonical8498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8498 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw8498 = injectiveMoment H raw8498step0 := by
      have hz : ∀ i, raw8498 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8498step0 = (fun i j => raw8498 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8498 permutation9 hz
    injectiveMoment H raw8498step0 = injectiveMoment H raw8498step1 := by
      have heq : raw8498step1 = (fun i j => raw8498step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8498step0 permutation28 permutation5
    _ = injectiveMoment H node169 := by rfl

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

theorem sound1032 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1032 = Sparse.eval value1032 (momentVector H) := by
  have heq : pivotMatrix1032 = (fun u v => node1032 (pivotPermutation1032 u) v) := by apply Matrix.ext; unfold pivotMatrix1032 node1032 pivotPermutation1032; decide +kernel
  have hmoment : injectiveMoment H node1032 = injectiveMoment H pivotMatrix1032 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1032 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1032 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1032 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1032 (0 : Fin 3) = raw7333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1032 raw7333; decide +kernel
    rw [heq]
    exact (canonical7333 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1032 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1032 (1 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1032 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1032 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1032 (2 : Fin 3) = raw6437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1032 raw6437; decide +kernel
    rw [heq]
    exact (canonical6437 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1032 + (injectiveMoment H (mergeFirst pivotMatrix1032 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1032 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1032 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1032, value145, value185, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound1059 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1059 = Sparse.eval value1059 (momentVector H) := by
  have heq : pivotMatrix1059 = (fun u v => node1059.transpose (pivotPermutation1059 u) v) := by apply Matrix.ext; unfold pivotMatrix1059 node1059 pivotPermutation1059; decide +kernel
  have hmoment : injectiveMoment H node1059 = injectiveMoment H pivotMatrix1059 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1059 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1059 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1059 (0 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1059 (0 : Fin 3) = raw4197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1059 raw4197; decide +kernel
    rw [heq]
    exact (canonical4197 hH).trans (sound197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1059 (1 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1059 (1 : Fin 3) = raw7539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1059 raw7539; decide +kernel
    rw [heq]
    exact (canonical7539 hH).trans (sound202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1059 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1059 (2 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1059 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1059 + (injectiveMoment H (mergeFirst pivotMatrix1059 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1059 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1059 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1059, value169, value197, value202, Sparse.eval] at hc ⊢
  linarith

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

theorem sound1190 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1190 = Sparse.eval value1190 (momentVector H) := by
  have heq : pivotMatrix1190 = (fun u v => node1190.transpose (pivotPermutation1190 u) v) := by apply Matrix.ext; unfold pivotMatrix1190 node1190 pivotPermutation1190; decide +kernel
  have hmoment : injectiveMoment H node1190 = injectiveMoment H pivotMatrix1190 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1190 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1190 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1190 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1190 (0 : Fin 3) = raw5813 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1190 raw5813; decide +kernel
    rw [heq]
    exact (canonical5813 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1190 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1190 (1 : Fin 3) = raw8227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1190 raw8227; decide +kernel
    rw [heq]
    exact (canonical8227 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1190 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1190 (2 : Fin 3) = raw8235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1190 raw8235; decide +kernel
    rw [heq]
    exact (canonical8235 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1190 + (injectiveMoment H (mergeFirst pivotMatrix1190 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1190 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1190 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1190, value111, value198, value203, Sparse.eval] at hc ⊢
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

theorem sound1311 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1311 = Sparse.eval value1311 (momentVector H) := by
  have heq : pivotMatrix1311 = (fun u v => node1311 (pivotPermutation1311 u) v) := by apply Matrix.ext; unfold pivotMatrix1311 node1311 pivotPermutation1311; decide +kernel
  have hmoment : injectiveMoment H node1311 = injectiveMoment H pivotMatrix1311 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1311 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1311 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1311 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1311 (0 : Fin 3) = raw6935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1311 raw6935; decide +kernel
    rw [heq]
    exact (canonical6935 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1311 (1 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1311 (1 : Fin 3) = raw7585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1311 raw7585; decide +kernel
    rw [heq]
    exact (canonical7585 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1311 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1311 (2 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1311 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1311 + (injectiveMoment H (mergeFirst pivotMatrix1311 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1311 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1311 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1311, value169, value203, value284, Sparse.eval] at hc ⊢
  linarith

theorem sound1316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1316 = Sparse.eval value1316 (momentVector H) := by
  have heq : pivotMatrix1316 = (fun u v => node1316 (pivotPermutation1316 u) v) := by apply Matrix.ext; unfold pivotMatrix1316 node1316 pivotPermutation1316; decide +kernel
  have hmoment : injectiveMoment H node1316 = injectiveMoment H pivotMatrix1316 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1316 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1316 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1316 (0 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1316 (0 : Fin 3) = raw7511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1316 raw7511; decide +kernel
    rw [heq]
    exact (canonical7511 hH).trans (sound291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1316 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1316 (1 : Fin 3) = raw7590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1316 raw7590; decide +kernel
    rw [heq]
    exact (canonical7590 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1316 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1316 (2 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1316 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1316 + (injectiveMoment H (mergeFirst pivotMatrix1316 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1316 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1316 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1316, value169, value210, value291, Sparse.eval] at hc ⊢
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

theorem sound406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node406 = Sparse.eval value406 (momentVector H) := by
  have hc : momentVector H 291 = injectiveMoment H node406 := rfl
  simp [value406, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound7
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound479 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node479 = Sparse.eval value479 (momentVector H) := by
  have hc : momentVector H 379 = injectiveMoment H node479 := rfl
  simp [value479, Sparse.eval, hc]

theorem sound488 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node488 = Sparse.eval value488 (momentVector H) := by
  have hc : momentVector H 100 = injectiveMoment H node488 := rfl
  simp [value488, Sparse.eval, hc]

theorem sound496 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node496 = Sparse.eval value496 (momentVector H) := by
  have hc : momentVector H 104 = injectiveMoment H node496 := rfl
  simp [value496, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound37
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2406 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2406 = Sparse.eval value2406 (momentVector H) := by
  have heq : pivotMatrix2406 = (fun u v => node2406 (pivotPermutation2406 u) v) := by apply Matrix.ext; unfold pivotMatrix2406 node2406 pivotPermutation2406; decide +kernel
  have hmoment : injectiveMoment H node2406 = injectiveMoment H pivotMatrix2406 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2406 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2406 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2406 (0 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2406 (0 : Fin 4) = raw6431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2406 raw6431; decide +kernel
    rw [heq]
    exact (canonical6431 hH).trans (sound1032 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2406 (1 : Fin 4)) =
      Sparse.eval value816 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2406 (1 : Fin 4) = raw5703 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2406 raw5703; decide +kernel
    rw [heq]
    exact (canonical5703 hH).trans (sound816 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2406 (2 : Fin 4)) =
      Sparse.eval value795 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2406 (2 : Fin 4) = raw5649 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2406 raw5649; decide +kernel
    rw [heq]
    exact (canonical5649 hH).trans (sound795 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2406 (3 : Fin 4)) =
      Sparse.eval value791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2406 (3 : Fin 4) = raw5647 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2406 raw5647; decide +kernel
    rw [heq]
    exact (canonical5647 hH).trans (sound791 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2406 + (injectiveMoment H (mergeFirst pivotMatrix2406 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2406 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2406 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2406 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2406, value1032, value791, value795, value816, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2101 = injectiveMoment H node1190 := by
  calc
    injectiveMoment H raw2101 = injectiveMoment H raw2101step0 := by
      have heq : raw2101step0 = raw2101.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2101).symm
    injectiveMoment H raw2101step0 = injectiveMoment H raw2101step1 := by
      have heq : raw2101step1 = (fun i j => raw2101step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2101step0 permutation32 permutation30
    _ = injectiveMoment H node1190 := by rfl

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

theorem sound2762 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2762 = Sparse.eval value2762 (momentVector H) := by
  have heq : pivotMatrix2762 = (fun u v => node2762 (pivotPermutation2762 u) v) := by apply Matrix.ext; unfold pivotMatrix2762 node2762 pivotPermutation2762; decide +kernel
  have hmoment : injectiveMoment H node2762 = injectiveMoment H pivotMatrix2762 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2762 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2762 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2762 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2762 (0 : Fin 4) = raw6509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2762 raw6509; decide +kernel
    rw [heq]
    exact (canonical6509 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2762 (1 : Fin 4)) =
      Sparse.eval value1311 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2762 (1 : Fin 4) = raw8368 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2762 raw8368; decide +kernel
    rw [heq]
    exact (canonical8368 hH).trans (sound1311 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2762 (2 : Fin 4)) =
      Sparse.eval value1316 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2762 (2 : Fin 4) = raw8489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2762 raw8489; decide +kernel
    rw [heq]
    exact (canonical8489 hH).trans (sound1316 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2762 (3 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2762 (3 : Fin 4) = raw8498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2762 raw8498; decide +kernel
    rw [heq]
    exact (canonical8498 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2762 + (injectiveMoment H (mergeFirst pivotMatrix2762 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2762 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2762 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2762 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2762, value1059, value1311, value1316, value169, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1807 = injectiveMoment H node1661 := by
  rfl

theorem canonical1808 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1808 = injectiveMoment H node2406 := by
  calc
    injectiveMoment H raw1808 = injectiveMoment H raw1808step0 := by
      have heq : raw1808step0 = (fun i j => raw1808 (permutation38 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1808 permutation38 permutation15
    _ = injectiveMoment H node2406 := by rfl

theorem canonical1812 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1812 = injectiveMoment H node1662 := by
  rfl

theorem canonical1813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1813 = injectiveMoment H node406 := by
  calc
    injectiveMoment H raw1813 = injectiveMoment H raw1813step0 := by
      have heq : raw1813step0 = -raw1813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1813).symm
    injectiveMoment H raw1813step0 = injectiveMoment H raw1813step1 := by
      have heq : raw1813step1 = (fun i j => raw1813step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1813step0 permutation32 permutation11
    _ = injectiveMoment H node406 := by rfl

theorem canonical1817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1817 = injectiveMoment H node479 := by
  rfl

theorem canonical1818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1818 = injectiveMoment H node791 := by
  calc
    injectiveMoment H raw1818 = injectiveMoment H raw1818step0 := by
      have heq : raw1818step0 = (fun i j => raw1818 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1818 permutation9 permutation15
    _ = injectiveMoment H node791 := by rfl

theorem canonical1819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1819 = injectiveMoment H node479 := by
  calc
    injectiveMoment H raw1819 = injectiveMoment H raw1819step0 := by
      have heq : raw1819step0 = (fun i j => raw1819 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1819 permutation10 permutation9
    _ = injectiveMoment H node479 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3433 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3433 = injectiveMoment H node2762 := by
  calc
    injectiveMoment H raw3433 = injectiveMoment H raw3433step0 := by
      have heq : raw3433step0 = -raw3433 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3433).symm
    injectiveMoment H raw3433step0 = injectiveMoment H raw3433step1 := by
      have heq : raw3433step1 = (fun i j => raw3433step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3433step0 permutation100 permutation15
    _ = injectiveMoment H node2762 := by rfl

theorem canonical3449 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3449 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw3449 = injectiveMoment H raw3449step0 := by
      have heq : raw3449step0 = -raw3449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3449).symm
    injectiveMoment H raw3449step0 = injectiveMoment H raw3449step1 := by
      have heq : raw3449step1 = (fun i j => raw3449step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3449step0 permutation29 permutation15
    _ = injectiveMoment H node1059 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1989 = injectiveMoment H node1710 := by
  rfl

theorem canonical2000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2000 = injectiveMoment H node488 := by
  rfl

theorem canonical2004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2004 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw2004 = injectiveMoment H raw2004step0 := by
      have heq : raw2004step0 = (fun i j => raw2004 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2004 permutation14 permutation15
    _ = injectiveMoment H node819 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound25
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1661 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1661 = Sparse.eval value1661 (momentVector H) := by
  have heq : pivotMatrix1661 = (fun u v => node1661 (pivotPermutation1661 u) v) := by apply Matrix.ext; unfold pivotMatrix1661 node1661 pivotPermutation1661; decide +kernel
  have hmoment : injectiveMoment H node1661 = injectiveMoment H pivotMatrix1661 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1661 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1661 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1661 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1661 (0 : Fin 4) = raw3449 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1661 raw3449; decide +kernel
    rw [heq]
    exact (canonical3449 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1661 (1 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1661 (1 : Fin 4) = raw2000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1661 raw2000; decide +kernel
    rw [heq]
    exact (canonical2000 hH).trans (sound488 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1661 (2 : Fin 4)) =
      Sparse.eval value791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1661 (2 : Fin 4) = raw1818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1661 raw1818; decide +kernel
    rw [heq]
    exact (canonical1818 hH).trans (sound791 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1661 (3 : Fin 4)) =
      Sparse.eval value479 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1661 (3 : Fin 4) = raw1817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1661 raw1817; decide +kernel
    rw [heq]
    exact (canonical1817 hH).trans (sound479 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1661 + (injectiveMoment H (mergeFirst pivotMatrix1661 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1661 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1661 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1661 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1661, value1059, value479, value488, value791, Sparse.eval] at hc ⊢
  linarith

theorem sound1662 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1662 = Sparse.eval value1662 (momentVector H) := by
  have heq : pivotMatrix1662 = (fun u v => node1662 (pivotPermutation1662 u) v) := by apply Matrix.ext; unfold pivotMatrix1662 node1662 pivotPermutation1662; decide +kernel
  have hmoment : injectiveMoment H node1662 = injectiveMoment H pivotMatrix1662 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1662 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1662 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1662 (0 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1662 (0 : Fin 4) = raw6434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1662 raw6434; decide +kernel
    rw [heq]
    exact (canonical6434 hH).trans (sound831 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1662 (1 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1662 (1 : Fin 4) = raw2127 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1662 raw2127; decide +kernel
    rw [heq]
    exact (canonical2127 hH).trans (sound496 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1662 (2 : Fin 4)) =
      Sparse.eval value479 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1662 (2 : Fin 4) = raw1819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1662 raw1819; decide +kernel
    rw [heq]
    exact (canonical1819 hH).trans (sound479 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1662 (3 : Fin 4)) =
      Sparse.eval value406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1662 (3 : Fin 4) = raw1813 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1662 raw1813; decide +kernel
    rw [heq]
    exact (canonical1813 hH).trans (sound406 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1662 + (injectiveMoment H (mergeFirst pivotMatrix1662 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1662 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1662 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1662 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1662, value406, value479, value496, value831, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3545 = injectiveMoment H node1311 := by
  calc
    injectiveMoment H raw3545 = injectiveMoment H raw3545step0 := by
      have heq : raw3545step0 = -raw3545 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3545).symm
    injectiveMoment H raw3545step0 = injectiveMoment H raw3545step1 := by
      have heq : raw3545step1 = (fun i j => raw3545step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3545step0 permutation19 permutation15
    _ = injectiveMoment H node1311 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound26
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1710 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1710 = Sparse.eval value1710 (momentVector H) := by
  have heq : pivotMatrix1710 = (fun u v => node1710 (pivotPermutation1710 u) v) := by apply Matrix.ext; unfold pivotMatrix1710 node1710 pivotPermutation1710; decide +kernel
  have hmoment : injectiveMoment H node1710 = injectiveMoment H pivotMatrix1710 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1710 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1710 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1710 (0 : Fin 4)) =
      Sparse.eval value1311 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1710 (0 : Fin 4) = raw3545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1710 raw3545; decide +kernel
    rw [heq]
    exact (canonical3545 hH).trans (sound1311 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1710 (1 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1710 (1 : Fin 4) = raw2101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1710 raw2101; decide +kernel
    rw [heq]
    exact (canonical2101 hH).trans (sound1190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1710 (2 : Fin 4)) =
      Sparse.eval value819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1710 (2 : Fin 4) = raw2004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1710 raw2004; decide +kernel
    rw [heq]
    exact (canonical2004 hH).trans (sound819 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1710 (3 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1710 (3 : Fin 4) = raw2000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1710 raw2000; decide +kernel
    rw [heq]
    exact (canonical2000 hH).trans (sound488 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1710 + (injectiveMoment H (mergeFirst pivotMatrix1710 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1710 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1710 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1710 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1710, value1190, value1311, value488, value819, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound46
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2982 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2982 = Sparse.eval value2982 (momentVector H) := by
  have heq : pivotMatrix2982 = (fun u v => node2982 (pivotPermutation2982 u) v) := by apply Matrix.ext; unfold pivotMatrix2982 node2982 pivotPermutation2982; decide +kernel
  have hmoment : injectiveMoment H node2982 = injectiveMoment H pivotMatrix2982 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2982 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2982 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2982 (0 : Fin 5)) =
      Sparse.eval value2762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (0 : Fin 5) = raw3433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw3433; decide +kernel
    rw [heq]
    exact (canonical3433 hH).trans (sound2762 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2982 (1 : Fin 5)) =
      Sparse.eval value1710 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (1 : Fin 5) = raw1989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw1989; decide +kernel
    rw [heq]
    exact (canonical1989 hH).trans (sound1710 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2982 (2 : Fin 5)) =
      Sparse.eval value1662 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (2 : Fin 5) = raw1812 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw1812; decide +kernel
    rw [heq]
    exact (canonical1812 hH).trans (sound1662 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2982 (3 : Fin 5)) =
      Sparse.eval value2406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (3 : Fin 5) = raw1808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw1808; decide +kernel
    rw [heq]
    exact (canonical1808 hH).trans (sound2406 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2982 (4 : Fin 5)) =
      Sparse.eval value1661 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (4 : Fin 5) = raw1807 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw1807; decide +kernel
    rw [heq]
    exact (canonical1807 hH).trans (sound1661 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2982 + (injectiveMoment H (mergeFirst pivotMatrix2982 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2982 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2982 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2982 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2982 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2982, value1661, value1662, value1710, value2406, value2762, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound311 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow311 (momentVector H) = 0 := by
  have hshape : boundaryMatrix311 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix311 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix311 (0 : Fin 6)) =
      Sparse.eval value2982 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (0 : Fin 6) = raw9161 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9161 hH).trans (sound2982 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix311 (1 : Fin 6)) =
      Sparse.eval value2989 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (1 : Fin 6) = raw9579 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9579 hH).trans (sound2989_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix311 (2 : Fin 6)) =
      Sparse.eval value2989 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (2 : Fin 6) = raw9615 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9615 hH).trans (sound2989_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix311 (3 : Fin 6)) =
      Sparse.eval value2992 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (3 : Fin 6) = raw9633 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9633 hH).trans (sound2992_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix311 (4 : Fin 6)) =
      Sparse.eval value2897 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (4 : Fin 6) = raw9640 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9640 hH).trans (sound2897_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix311 (5 : Fin 6)) =
      Sparse.eval value3400 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix311 (5 : Fin 6) = raw9641 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9641 hH).trans (sound3400_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix311 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix311 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow311, value2897, value2982, value2989, value2992, value3400, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck176 : Integer.Sparse.reindex coordinateMap (PairData.rows 176) =
    PairSemantics.boundaryRow311 := by decide +kernel

theorem rowSound176_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 176) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck176]
  exact PairSemantics.boundarySound311 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e_oai
