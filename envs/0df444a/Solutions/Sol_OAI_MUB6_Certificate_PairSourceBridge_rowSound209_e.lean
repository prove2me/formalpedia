-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T14:13:02.872289+00:00
-- url     : https://prove2.me/submissions/f95dcf56-d203-494a-b7b4-02d3a6cacbe0

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2902_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2906_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2916_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3371_e

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

theorem canonical8074 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8074 = injectiveMoment H node2902 := by
  calc
    injectiveMoment H raw8074 = injectiveMoment H raw8074step0 := by
      have heq : raw8074step0 = -raw8074 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8074).symm
    injectiveMoment H raw8074step0 = injectiveMoment H raw8074step1 := by
      have heq : raw8074step1 = (fun i j => raw8074step0 (permutation380 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8074step0 permutation380 permutation15
    _ = injectiveMoment H node2902 := by rfl

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

theorem canonical8380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8380 = injectiveMoment H node2916 := by
  calc
    injectiveMoment H raw8380 = injectiveMoment H raw8380step0 := by
      have heq : raw8380step0 = -raw8380 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8380).symm
    injectiveMoment H raw8380step0 = injectiveMoment H raw8380step1 := by
      have heq : raw8380step1 = (fun i j => raw8380step0 (permutation387 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8380step0 permutation387 permutation15
    _ = injectiveMoment H node2916 := by rfl

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

theorem canonical8425 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8425 = injectiveMoment H node2916 := by
  calc
    injectiveMoment H raw8425 = injectiveMoment H raw8425step0 := by
      have heq : raw8425step0 = -raw8425 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8425).symm
    injectiveMoment H raw8425step0 = injectiveMoment H raw8425step1 := by
      have heq : raw8425step1 = (fun i j => raw8425step0 (permutation381 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8425step0 permutation381 permutation15
    _ = injectiveMoment H node2916 := by rfl

theorem canonical8435 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8435 = injectiveMoment H node2932 := by
  calc
    injectiveMoment H raw8435 = injectiveMoment H raw8435step0 := by
      have heq : raw8435step0 = -raw8435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8435).symm
    injectiveMoment H raw8435step0 = injectiveMoment H raw8435step1 := by
      have heq : raw8435step1 = (fun i j => raw8435step0 (permutation342 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8435step0 permutation342 permutation15
    _ = injectiveMoment H node2932 := by rfl

theorem canonical8440 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8440 = injectiveMoment H node2906 := by
  calc
    injectiveMoment H raw8440 = injectiveMoment H raw8440step0 := by
      have heq : raw8440step0 = -raw8440 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8440).symm
    injectiveMoment H raw8440step0 = injectiveMoment H raw8440step1 := by
      have heq : raw8440step1 = (fun i j => raw8440step0 (permutation379 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8440step0 permutation379 permutation15
    _ = injectiveMoment H node2906 := by rfl

theorem canonical8442 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8442 = injectiveMoment H node3371 := by
  calc
    injectiveMoment H raw8442 = injectiveMoment H raw8442step0 := by
      have heq : raw8442step0 = -raw8442 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8442).symm
    injectiveMoment H raw8442step0 = injectiveMoment H raw8442step1 := by
      have heq : raw8442step1 = (fun i j => raw8442step0 (permutation380 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8442step0 permutation380 permutation15
    _ = injectiveMoment H node3371 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1504 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1504 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw1504 = injectiveMoment H raw1504step0 := by
      have heq : raw1504step0 = raw1504.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1504).symm
    injectiveMoment H raw1504step0 = injectiveMoment H raw1504step1 := by
      have heq : raw1504step1 = (fun i j => raw1504step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1504step0 permutation30 permutation24
    _ = injectiveMoment H node896 := by rfl

theorem canonical1508 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1508 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw1508 = injectiveMoment H raw1508step0 := by
      have heq : raw1508step0 = (fun i j => raw1508 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1508 permutation10 permutation9
    _ = injectiveMoment H node454 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1590 = injectiveMoment H node1599 := by
  rfl

theorem canonical1591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1591 = injectiveMoment H node1600 := by
  rfl

theorem canonical1595 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1595 = injectiveMoment H node1576 := by
  calc
    injectiveMoment H raw1595 = injectiveMoment H raw1595step0 := by
      have heq : raw1595step0 = (fun i j => raw1595 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1595 permutation40 permutation11
    _ = injectiveMoment H node1576 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1631 = injectiveMoment H node1610 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1632 = injectiveMoment H node459 := by
  rfl

theorem canonical1642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1642 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw1642 = injectiveMoment H raw1642step0 := by
      have heq : raw1642step0 = raw1642.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1642).symm
    injectiveMoment H raw1642step0 = injectiveMoment H raw1642step1 := by
      have heq : raw1642step1 = (fun i j => raw1642step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1642step0 permutation30 permutation24
    _ = injectiveMoment H node769 := by rfl

theorem canonical1646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1646 = injectiveMoment H node447 := by
  calc
    injectiveMoment H raw1646 = injectiveMoment H raw1646step0 := by
      have heq : raw1646step0 = raw1646.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1646).symm
    injectiveMoment H raw1646step0 = injectiveMoment H raw1646step1 := by
      have heq : raw1646step1 = (fun i j => raw1646step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1646step0 permutation29 permutation20
    _ = injectiveMoment H node447 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1712 = injectiveMoment H node468 := by
  rfl

theorem canonical1713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1713 = injectiveMoment H node469 := by
  rfl

theorem canonical1714 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1714 = injectiveMoment H node1166 := by
  calc
    injectiveMoment H raw1714 = injectiveMoment H raw1714step0 := by
      have heq : raw1714step0 = raw1714.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1714).symm
    injectiveMoment H raw1714step0 = injectiveMoment H raw1714step1 := by
      have heq : raw1714step1 = (fun i j => raw1714step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1714step0 permutation32 permutation30
    _ = injectiveMoment H node1166 := by rfl

theorem canonical1716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1716 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw1716 = injectiveMoment H raw1716step0 := by
      have heq : raw1716step0 = (fun i j => raw1716 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1716 permutation9 permutation11
    _ = injectiveMoment H node454 := by rfl

theorem canonical1717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1717 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw1717 = injectiveMoment H raw1717step0 := by
      have heq : raw1717step0 = raw1717.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1717).symm
    injectiveMoment H raw1717step0 = injectiveMoment H raw1717step1 := by
      have heq : raw1717step1 = (fun i j => raw1717step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1717step0 permutation32 permutation30
    _ = injectiveMoment H node896 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1739 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1739 = injectiveMoment H node468 := by
  calc
    injectiveMoment H raw1739 = injectiveMoment H raw1739step0 := by
      have heq : raw1739step0 = (fun i j => raw1739 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1739 permutation12 permutation9
    _ = injectiveMoment H node468 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1918 = injectiveMoment H node1688 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3082 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw3082 = injectiveMoment H raw3082step0 := by
      have heq : raw3082step0 = raw3082.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3082).symm
    injectiveMoment H raw3082step0 = injectiveMoment H raw3082step1 := by
      have heq : raw3082step1 = (fun i j => raw3082step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3082step0 permutation30 permutation24
    _ = injectiveMoment H node939 := by rfl

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

theorem canonical4171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4171 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw4171 = injectiveMoment H raw4171step0 := by
      have heq : raw4171step0 = raw4171.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4171).symm
    injectiveMoment H raw4171step0 = injectiveMoment H raw4171step1 := by
      have heq : raw4171step1 = (fun i j => raw4171step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4171step0 permutation13 permutation3
    _ = injectiveMoment H node177 := by rfl

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

theorem canonical5636 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5636 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw5636 = injectiveMoment H raw5636step0 := by
      have heq : raw5636step0 = raw5636.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5636).symm
    injectiveMoment H raw5636step0 = injectiveMoment H raw5636step1 := by
      have heq : raw5636step1 = -raw5636step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5636step0).symm
    injectiveMoment H raw5636step1 = injectiveMoment H raw5636step2 := by
      have heq : raw5636step2 = (fun i j => raw5636step1 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5636step1 permutation15 permutation6
    _ = injectiveMoment H node206 := by rfl

theorem canonical5637 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5637 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw5637 = injectiveMoment H raw5637step0 := by
      have heq : raw5637step0 = raw5637.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5637).symm
    injectiveMoment H raw5637step0 = injectiveMoment H raw5637step1 := by
      have heq : raw5637step1 = (fun i j => raw5637step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5637step0 permutation28 permutation6
    _ = injectiveMoment H node145 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5810 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5810 = injectiveMoment H node161 := by
  calc
    injectiveMoment H raw5810 = injectiveMoment H raw5810step0 := by
      have heq : raw5810step0 = raw5810.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5810).symm
    injectiveMoment H raw5810step0 = injectiveMoment H raw5810step1 := by
      have heq : raw5810step1 = (fun i j => raw5810step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5810step0 permutation16 permutation4
    _ = injectiveMoment H node161 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6289 = injectiveMoment H node975 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2486 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2486 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw2486 = injectiveMoment H raw2486step0 := by
      have heq : raw2486step0 = raw2486.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2486).symm
    injectiveMoment H raw2486step0 = injectiveMoment H raw2486step1 := by
      have heq : raw2486step1 = (fun i j => raw2486step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2486step0 permutation30 permutation32
    _ = injectiveMoment H node1005 := by rfl

theorem canonical2488 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2488 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw2488 = injectiveMoment H raw2488step0 := by
      have heq : raw2488step0 = raw2488.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2488).symm
    injectiveMoment H raw2488step0 = injectiveMoment H raw2488step1 := by
      have heq : raw2488step1 = (fun i j => raw2488step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2488step0 permutation22 permutation5
    _ = injectiveMoment H node224 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2524 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw2524 = injectiveMoment H raw2524step0 := by
      have heq : raw2524step0 = raw2524.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2524).symm
    injectiveMoment H raw2524step0 = injectiveMoment H raw2524step1 := by
      have heq : raw2524step1 = (fun i j => raw2524step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2524step0 permutation10 permutation3
    _ = injectiveMoment H node134 := by rfl

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

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
  rfl

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

theorem canonical6889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6889 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw6889 = injectiveMoment H raw6889step0 := by
      have heq : raw6889step0 = raw6889.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6889).symm
    injectiveMoment H raw6889step0 = injectiveMoment H raw6889step1 := by
      have heq : raw6889step1 = -raw6889step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6889step0).symm
    injectiveMoment H raw6889step1 = injectiveMoment H raw6889step2 := by
      have heq : raw6889step2 = (fun i j => raw6889step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6889step1 permutation26 permutation3
    _ = injectiveMoment H node225 := by rfl

theorem canonical6895 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6895 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6895 = injectiveMoment H raw6895step0 := by
      have heq : raw6895step0 = raw6895.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6895).symm
    injectiveMoment H raw6895step0 = injectiveMoment H raw6895step1 := by
      have heq : raw6895step1 = -raw6895step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6895step0).symm
    injectiveMoment H raw6895step1 = injectiveMoment H raw6895step2 := by
      have heq : raw6895step2 = (fun i j => raw6895step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6895step1 permutation26 permutation3
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

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

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

theorem canonical1439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1439 = injectiveMoment H node32 := by
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

theorem sound134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node134 = Sparse.eval value134 (momentVector H) := by
  have hc : momentVector H 81 = injectiveMoment H node134 := rfl
  simp [value134, Sparse.eval, hc]

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

theorem sound161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node161 = Sparse.eval value161 (momentVector H) := by
  have hc : momentVector H 490 = injectiveMoment H node161 := rfl
  simp [value161, Sparse.eval, hc]

theorem sound164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node164 = Sparse.eval value164 (momentVector H) := by
  have hc : momentVector H 492 = injectiveMoment H node164 := rfl
  simp [value164, Sparse.eval, hc]

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

theorem sound177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node177 = Sparse.eval value177 (momentVector H) := by
  have heq : pivotMatrix177 = (fun u v => node177 (pivotPermutation177 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node177 = injectiveMoment H pivotMatrix177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix177 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix177 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (0 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (1 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node177 + (injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value177, value36, value37, value41, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4950 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw4950 = injectiveMoment H raw4950step0 := by
      have heq : raw4950step0 = raw4950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4950).symm
    injectiveMoment H raw4950step0 = injectiveMoment H raw4950step1 := by
      have hz : ∀ i, raw4950step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw4950step1 = (fun i j => raw4950step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4950step0 permutation5 hz
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node198 = Sparse.eval value198 (momentVector H) := by
  have hc : momentVector H 54 = injectiveMoment H node198 := rfl
  simp [value198, Sparse.eval, hc]

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

theorem sound212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node212 = Sparse.eval value212 (momentVector H) := by
  have hc : momentVector H 55 = injectiveMoment H node212 := rfl
  simp [value212, Sparse.eval, hc]

theorem sound224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node224 = Sparse.eval value224 (momentVector H) := by
  have hc : momentVector H 25 = injectiveMoment H node224 := rfl
  simp [value224, Sparse.eval, hc]

theorem sound225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node225 = Sparse.eval value225 (momentVector H) := by
  have hc : momentVector H 228 = injectiveMoment H node225 := rfl
  simp [value225, Sparse.eval, hc]

theorem sound227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node227 = Sparse.eval value227 (momentVector H) := by
  have heq : pivotMatrix227 = (fun u v => node227 (pivotPermutation227 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node227 = injectiveMoment H pivotMatrix227 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix227 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix227 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (1 : Fin 3) = raw4950 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4950 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (2 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node227 + (injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value227, value11, value62, Sparse.eval] at hc ⊢
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

theorem sound276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node276 = Sparse.eval value276 (momentVector H) := by
  have hc : momentVector H 31 = injectiveMoment H node276 := rfl
  simp [value276, Sparse.eval, hc]

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

theorem sound769 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node769 = Sparse.eval value769 (momentVector H) := by
  have heq : pivotMatrix769 = (fun u v => node769 (pivotPermutation769 u) v) := by apply Matrix.ext; unfold pivotMatrix769 node769 pivotPermutation769; decide +kernel
  have hmoment : injectiveMoment H node769 = injectiveMoment H pivotMatrix769 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix769 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix769 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix769 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix769 (0 : Fin 3) = raw5725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix769 raw5725; decide +kernel
    rw [heq]
    exact (canonical5725 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix769 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix769 (1 : Fin 3) = raw5637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix769 raw5637; decide +kernel
    rw [heq]
    exact (canonical5637 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix769 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix769 (2 : Fin 3) = raw5636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix769 raw5636; decide +kernel
    rw [heq]
    exact (canonical5636 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node769 + (injectiveMoment H (mergeFirst pivotMatrix769 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix769 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix769 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value769, value145, value185, value206, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical6591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6591 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw6591 = injectiveMoment H raw6591step0 := by
      have heq : raw6591step0 = raw6591.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6591).symm
    _ = injectiveMoment H node276 := by rfl

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

theorem canonical7522 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7522 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw7522 = injectiveMoment H raw7522step0 := by
      have heq : raw7522step0 = raw7522.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7522).symm
    injectiveMoment H raw7522step0 = injectiveMoment H raw7522step1 := by
      have heq : raw7522step1 = -raw7522step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7522step0).symm
    injectiveMoment H raw7522step1 = injectiveMoment H raw7522step2 := by
      have heq : raw7522step2 = (fun i j => raw7522step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7522step1 permutation23 permutation4
    _ = injectiveMoment H node212 := by rfl

theorem canonical7537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7537 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw7537 = injectiveMoment H raw7537step0 := by
      have heq : raw7537step0 = raw7537.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7537).symm
    injectiveMoment H raw7537step0 = injectiveMoment H raw7537step1 := by
      have heq : raw7537step1 = (fun i j => raw7537step0 (permutation20 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7537step0 permutation20 permutation7
    _ = injectiveMoment H node203 := by rfl

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

theorem sound896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node896 = Sparse.eval value896 (momentVector H) := by
  have heq : pivotMatrix896 = (fun u v => node896.transpose (pivotPermutation896 u) v) := by apply Matrix.ext; unfold pivotMatrix896 node896 pivotPermutation896; decide +kernel
  have hmoment : injectiveMoment H node896 = injectiveMoment H pivotMatrix896 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix896 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix896 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix896 (0 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix896 (0 : Fin 3) = raw2524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix896 raw2524; decide +kernel
    rw [heq]
    exact (canonical2524 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix896 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix896 (1 : Fin 3) = raw6889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix896 raw6889; decide +kernel
    rw [heq]
    exact (canonical6889 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix896 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix896 (2 : Fin 3) = raw6895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix896 raw6895; decide +kernel
    rw [heq]
    exact (canonical6895 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node896 + (injectiveMoment H (mergeFirst pivotMatrix896 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix896 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix896 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value896, value134, value225, value229, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical6706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6706 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw6706 = injectiveMoment H raw6706step0 := by
      have heq : raw6706step0 = raw6706.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6706).symm
    injectiveMoment H raw6706step0 = injectiveMoment H raw6706step1 := by
      have heq : raw6706step1 = (fun i j => raw6706step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6706step0 permutation22 permutation5
    _ = injectiveMoment H node227 := by rfl

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

theorem canonical8224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8224 = injectiveMoment H node164 := by
  calc
    injectiveMoment H raw8224 = injectiveMoment H raw8224step0 := by
      have heq : raw8224step0 = raw8224.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8224).symm
    injectiveMoment H raw8224step0 = injectiveMoment H raw8224step1 := by
      have heq : raw8224step1 = (fun i j => raw8224step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8224step0 permutation19 permutation4
    _ = injectiveMoment H node164 := by rfl

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

theorem canonical8230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8230 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw8230 = injectiveMoment H raw8230step0 := by
      have heq : raw8230step0 = raw8230.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8230).symm
    injectiveMoment H raw8230step0 = injectiveMoment H raw8230step1 := by
      have heq : raw8230step1 = (fun i j => raw8230step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8230step0 permutation19 permutation4
    _ = injectiveMoment H node170 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound18
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1166 = Sparse.eval value1166 (momentVector H) := by
  have heq : pivotMatrix1166 = (fun u v => node1166.transpose (pivotPermutation1166 u) v) := by apply Matrix.ext; unfold pivotMatrix1166 node1166 pivotPermutation1166; decide +kernel
  have hmoment : injectiveMoment H node1166 = injectiveMoment H pivotMatrix1166 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1166 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1166 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1166 (0 : Fin 3)) =
      Sparse.eval value161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1166 (0 : Fin 3) = raw5810 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1166 raw5810; decide +kernel
    rw [heq]
    exact (canonical5810 hH).trans (sound161 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1166 (1 : Fin 3)) =
      Sparse.eval value164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1166 (1 : Fin 3) = raw8224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1166 raw8224; decide +kernel
    rw [heq]
    exact (canonical8224 hH).trans (sound164 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1166 (2 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1166 (2 : Fin 3) = raw8230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1166 raw8230; decide +kernel
    rw [heq]
    exact (canonical8230 hH).trans (sound170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1166 + (injectiveMoment H (mergeFirst pivotMatrix1166 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1166 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1166 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1166, value161, value164, value170, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound15
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound975 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node975 = Sparse.eval value975 (momentVector H) := by
  have heq : pivotMatrix975 = (fun u v => node975.transpose (pivotPermutation975 u) v) := by apply Matrix.ext; unfold pivotMatrix975 node975 pivotPermutation975; decide +kernel
  have hmoment : injectiveMoment H node975 = injectiveMoment H pivotMatrix975 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix975 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix975 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix975 (0 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix975 (0 : Fin 3) = raw4171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix975 raw4171; decide +kernel
    rw [heq]
    exact (canonical4171 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix975 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix975 (1 : Fin 3) = raw7522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix975 raw7522; decide +kernel
    rw [heq]
    exact (canonical7522 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix975 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix975 (2 : Fin 3) = raw7537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix975 raw7537; decide +kernel
    rw [heq]
    exact (canonical7537 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node975 + (injectiveMoment H (mergeFirst pivotMatrix975 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix975 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix975 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value975, value177, value203, value212, Sparse.eval] at hc ⊢
  linarith

theorem sound1005 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1005 = Sparse.eval value1005 (momentVector H) := by
  have heq : pivotMatrix1005 = (fun u v => node1005.transpose (pivotPermutation1005 u) v) := by apply Matrix.ext; unfold pivotMatrix1005 node1005 pivotPermutation1005; decide +kernel
  have hmoment : injectiveMoment H node1005 = injectiveMoment H pivotMatrix1005 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1005 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1005 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1005 (0 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1005 (0 : Fin 3) = raw2488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1005 raw2488; decide +kernel
    rw [heq]
    exact (canonical2488 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1005 (1 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1005 (1 : Fin 3) = raw6591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1005 raw6591; decide +kernel
    rw [heq]
    exact (canonical6591 hH).trans (sound276 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1005 (2 : Fin 3)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1005 (2 : Fin 3) = raw6706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1005 raw6706; decide +kernel
    rw [heq]
    exact (canonical6706 hH).trans (sound227 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1005 + (injectiveMoment H (mergeFirst pivotMatrix1005 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1005 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1005 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1005, value224, value227, value276, Sparse.eval] at hc ⊢
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

theorem sound447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node447 = Sparse.eval value447 (momentVector H) := by
  have hc : momentVector H 311 = injectiveMoment H node447 := rfl
  simp [value447, Sparse.eval, hc]

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

theorem sound454 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node454 = Sparse.eval value454 (momentVector H) := by
  have hc : momentVector H 85 = injectiveMoment H node454 := rfl
  simp [value454, Sparse.eval, hc]

theorem sound459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node459 = Sparse.eval value459 (momentVector H) := by
  have hc : momentVector H 321 = injectiveMoment H node459 := rfl
  simp [value459, Sparse.eval, hc]

theorem sound468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node468 = Sparse.eval value468 (momentVector H) := by
  have hc : momentVector H 329 = injectiveMoment H node468 := rfl
  simp [value468, Sparse.eval, hc]

theorem sound469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node469 = Sparse.eval value469 (momentVector H) := by
  have hc : momentVector H 330 = injectiveMoment H node469 := rfl
  simp [value469, Sparse.eval, hc]

theorem sound476 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node476 = Sparse.eval value476 (momentVector H) := by
  have hc : momentVector H 39 = injectiveMoment H node476 := rfl
  simp [value476, Sparse.eval, hc]

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

theorem canonical2100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2100 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw2100 = injectiveMoment H raw2100step0 := by
      have heq : raw2100step0 = raw2100.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2100).symm
    injectiveMoment H raw2100step0 = injectiveMoment H raw2100step1 := by
      have heq : raw2100step1 = (fun i j => raw2100step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2100step0 permutation30 permutation32
    _ = injectiveMoment H node476 := by rfl

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

theorem canonical2106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2106 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw2106 = injectiveMoment H raw2106step0 := by
      have heq : raw2106step0 = raw2106.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2106).symm
    injectiveMoment H raw2106step0 = injectiveMoment H raw2106step1 := by
      have heq : raw2106step1 = (fun i j => raw2106step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2106step0 permutation32 permutation30
    _ = injectiveMoment H node939 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound24
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1576 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1576 = Sparse.eval value1576 (momentVector H) := by
  have heq : pivotMatrix1576 = (fun u v => node1576 (pivotPermutation1576 u) v) := by apply Matrix.ext; unfold pivotMatrix1576 node1576 pivotPermutation1576; decide +kernel
  have hmoment : injectiveMoment H node1576 = injectiveMoment H pivotMatrix1576 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1576 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1576 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1576 (0 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1576 (0 : Fin 4) = raw3082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1576 raw3082; decide +kernel
    rw [heq]
    exact (canonical3082 hH).trans (sound939 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1576 (1 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1576 (1 : Fin 4) = raw1642 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1576 raw1642; decide +kernel
    rw [heq]
    exact (canonical1642 hH).trans (sound769 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1576 (2 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1576 (2 : Fin 4) = raw1508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1576 raw1508; decide +kernel
    rw [heq]
    exact (canonical1508 hH).trans (sound454 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1576 (3 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1576 (3 : Fin 4) = raw1504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1576 raw1504; decide +kernel
    rw [heq]
    exact (canonical1504 hH).trans (sound896 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1576 + (injectiveMoment H (mergeFirst pivotMatrix1576 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1576 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1576 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1576 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1576, value454, value769, value896, value939, Sparse.eval] at hc ⊢
  linarith

theorem sound1599 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1599 = Sparse.eval value1599 (momentVector H) := by
  have heq : pivotMatrix1599 = (fun u v => node1599 (pivotPermutation1599 u) v) := by apply Matrix.ext; unfold pivotMatrix1599 node1599 pivotPermutation1599; decide +kernel
  have hmoment : injectiveMoment H node1599 = injectiveMoment H pivotMatrix1599 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1599 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1599 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1599 (0 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1599 (0 : Fin 4) = raw2100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1599 raw2100; decide +kernel
    rw [heq]
    exact (canonical2100 hH).trans (sound476 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1599 (1 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1599 (1 : Fin 4) = raw1716 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1599 raw1716; decide +kernel
    rw [heq]
    exact (canonical1716 hH).trans (sound454 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1599 (2 : Fin 4)) =
      Sparse.eval value469 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1599 (2 : Fin 4) = raw1713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1599 raw1713; decide +kernel
    rw [heq]
    exact (canonical1713 hH).trans (sound469 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1599 (3 : Fin 4)) =
      Sparse.eval value468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1599 (3 : Fin 4) = raw1712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1599 raw1712; decide +kernel
    rw [heq]
    exact (canonical1712 hH).trans (sound468 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1599 + (injectiveMoment H (mergeFirst pivotMatrix1599 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1599 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1599 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1599 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1599, value454, value468, value469, value476, Sparse.eval] at hc ⊢
  linarith

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

theorem sound1600 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1600 = Sparse.eval value1600 (momentVector H) := by
  have heq : pivotMatrix1600 = (fun u v => node1600 (pivotPermutation1600 u) v) := by apply Matrix.ext; unfold pivotMatrix1600 node1600 pivotPermutation1600; decide +kernel
  have hmoment : injectiveMoment H node1600 = injectiveMoment H pivotMatrix1600 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1600 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1600 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1600 (0 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1600 (0 : Fin 4) = raw2101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1600 raw2101; decide +kernel
    rw [heq]
    exact (canonical2101 hH).trans (sound1190 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1600 (1 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1600 (1 : Fin 4) = raw1717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1600 raw1717; decide +kernel
    rw [heq]
    exact (canonical1717 hH).trans (sound896 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1600 (2 : Fin 4)) =
      Sparse.eval value1166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1600 (2 : Fin 4) = raw1714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1600 raw1714; decide +kernel
    rw [heq]
    exact (canonical1714 hH).trans (sound1166 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1600 (3 : Fin 4)) =
      Sparse.eval value469 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1600 (3 : Fin 4) = raw1713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1600 raw1713; decide +kernel
    rw [heq]
    exact (canonical1713 hH).trans (sound469 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1600 + (injectiveMoment H (mergeFirst pivotMatrix1600 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1600 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1600 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1600 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1600, value1166, value1190, value469, value896, Sparse.eval] at hc ⊢
  linarith

theorem sound1610 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1610 = Sparse.eval value1610 (momentVector H) := by
  have heq : pivotMatrix1610 = (fun u v => node1610 (pivotPermutation1610 u) v) := by apply Matrix.ext; unfold pivotMatrix1610 node1610 pivotPermutation1610; decide +kernel
  have hmoment : injectiveMoment H node1610 = injectiveMoment H pivotMatrix1610 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1610 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1610 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1610 (0 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1610 (0 : Fin 4) = raw6289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1610 raw6289; decide +kernel
    rw [heq]
    exact (canonical6289 hH).trans (sound975 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1610 (1 : Fin 4)) =
      Sparse.eval value468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1610 (1 : Fin 4) = raw1739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1610 raw1739; decide +kernel
    rw [heq]
    exact (canonical1739 hH).trans (sound468 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1610 (2 : Fin 4)) =
      Sparse.eval value447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1610 (2 : Fin 4) = raw1646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1610 raw1646; decide +kernel
    rw [heq]
    exact (canonical1646 hH).trans (sound447 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1610 (3 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1610 (3 : Fin 4) = raw1632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1610 raw1632; decide +kernel
    rw [heq]
    exact (canonical1632 hH).trans (sound459 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1610 + (injectiveMoment H (mergeFirst pivotMatrix1610 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1610 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1610 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1610 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1610, value447, value459, value468, value975, Sparse.eval] at hc ⊢
  linarith

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

theorem sound1688 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1688 = Sparse.eval value1688 (momentVector H) := by
  have heq : pivotMatrix1688 = (fun u v => node1688 (pivotPermutation1688 u) v) := by apply Matrix.ext; unfold pivotMatrix1688 node1688 pivotPermutation1688; decide +kernel
  have hmoment : injectiveMoment H node1688 = injectiveMoment H pivotMatrix1688 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1688 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1688 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1688 (0 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1688 (0 : Fin 4) = raw2486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1688 raw2486; decide +kernel
    rw [heq]
    exact (canonical2486 hH).trans (sound1005 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1688 (1 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1688 (1 : Fin 4) = raw2106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1688 raw2106; decide +kernel
    rw [heq]
    exact (canonical2106 hH).trans (sound939 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1688 (2 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1688 (2 : Fin 4) = raw2101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1688 raw2101; decide +kernel
    rw [heq]
    exact (canonical2101 hH).trans (sound1190 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1688 (3 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1688 (3 : Fin 4) = raw2100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1688 raw2100; decide +kernel
    rw [heq]
    exact (canonical2100 hH).trans (sound476 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1688 + (injectiveMoment H (mergeFirst pivotMatrix1688 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1688 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1688 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1688 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1688, value1005, value1190, value476, value939, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound45
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2932 = Sparse.eval value2932 (momentVector H) := by
  have heq : pivotMatrix2932 = (fun u v => node2932 (pivotPermutation2932 u) v) := by apply Matrix.ext; unfold pivotMatrix2932 node2932 pivotPermutation2932; decide +kernel
  have hmoment : injectiveMoment H node2932 = injectiveMoment H pivotMatrix2932 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2932 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2932 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2932 (0 : Fin 5)) =
      Sparse.eval value1688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (0 : Fin 5) = raw1918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1918; decide +kernel
    rw [heq]
    exact (canonical1918 hH).trans (sound1688 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2932 (1 : Fin 5)) =
      Sparse.eval value1610 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (1 : Fin 5) = raw1631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1631; decide +kernel
    rw [heq]
    exact (canonical1631 hH).trans (sound1610 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2932 (2 : Fin 5)) =
      Sparse.eval value1576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (2 : Fin 5) = raw1595 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1595; decide +kernel
    rw [heq]
    exact (canonical1595 hH).trans (sound1576 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2932 (3 : Fin 5)) =
      Sparse.eval value1600 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (3 : Fin 5) = raw1591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1591; decide +kernel
    rw [heq]
    exact (canonical1591 hH).trans (sound1600 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2932 (4 : Fin 5)) =
      Sparse.eval value1599 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (4 : Fin 5) = raw1590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1590; decide +kernel
    rw [heq]
    exact (canonical1590 hH).trans (sound1599 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2932 + (injectiveMoment H (mergeFirst pivotMatrix2932 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2932 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2932 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2932 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2932 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2932, value1576, value1599, value1600, value1610, value1688, Sparse.eval] at hc ⊢
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

theorem boundarySound381 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow381 (momentVector H) = 0 := by
  have hshape : boundaryMatrix381 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix381 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix381 (0 : Fin 6)) =
      Sparse.eval value2902 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (0 : Fin 6) = raw8074 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8074 hH).trans (sound2902_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix381 (1 : Fin 6)) =
      Sparse.eval value2916 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (1 : Fin 6) = raw8380 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8380 hH).trans (sound2916_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix381 (2 : Fin 6)) =
      Sparse.eval value2916 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (2 : Fin 6) = raw8425 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8425 hH).trans (sound2916_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix381 (3 : Fin 6)) =
      Sparse.eval value2932 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (3 : Fin 6) = raw8435 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8435 hH).trans (sound2932 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix381 (4 : Fin 6)) =
      Sparse.eval value2906 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (4 : Fin 6) = raw8440 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8440 hH).trans (sound2906_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix381 (5 : Fin 6)) =
      Sparse.eval value3371 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix381 (5 : Fin 6) = raw8442 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8442 hH).trans (sound3371_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix381 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix381 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow381, value2902, value2906, value2916, value2932, value3371, Sparse.eval, Integer.Sparse.eval] at hc ⊢
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

theorem rowCheck209 : Integer.Sparse.reindex coordinateMap (PairData.rows 209) =
    PairSemantics.boundaryRow381 := by decide +kernel

theorem rowSound209_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 209) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck209]
  exact PairSemantics.boundarySound381 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e_oai
