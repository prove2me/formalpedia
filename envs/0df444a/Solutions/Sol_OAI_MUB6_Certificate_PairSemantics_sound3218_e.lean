-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3218_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T07:43:24.331687+00:00
-- url     : https://prove2.me/submissions/a35ff695-9555-442e-a433-72b4c35be00a

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E071
import Definitions.Def_OAIQ106E084
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2324_e

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

end MUB6

end

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

theorem canonical335 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw335 = injectiveMoment H node38 := by
  calc
    injectiveMoment H raw335 = injectiveMoment H raw335step0 := by
      have heq : raw335step0 = raw335.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw335).symm
    injectiveMoment H raw335step0 = injectiveMoment H raw335step1 := by
      have heq : raw335step1 = (fun i j => raw335step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw335step0 permutation6 permutation7
    _ = injectiveMoment H node38 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3517 = injectiveMoment H node1300 := by
  calc
    injectiveMoment H raw3517 = injectiveMoment H raw3517step0 := by
      have heq : raw3517step0 = raw3517.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3517).symm
    injectiveMoment H raw3517step0 = injectiveMoment H raw3517step1 := by
      have heq : raw3517step1 = (fun i j => raw3517step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3517step0 permutation18 permutation21
    _ = injectiveMoment H node1300 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3611 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3611 = injectiveMoment H node461 := by
  calc
    injectiveMoment H raw3611 = injectiveMoment H raw3611step0 := by
      have heq : raw3611step0 = raw3611.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3611).symm
    injectiveMoment H raw3611step0 = injectiveMoment H raw3611step1 := by
      have heq : raw3611step1 = -raw3611step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3611step0).symm
    injectiveMoment H raw3611step1 = injectiveMoment H raw3611step2 := by
      have heq : raw3611step2 = (fun i j => raw3611step1 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3611step1 permutation32 permutation11
    _ = injectiveMoment H node461 := by rfl

theorem canonical3615 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3615 = injectiveMoment H node1313 := by
  calc
    injectiveMoment H raw3615 = injectiveMoment H raw3615step0 := by
      have heq : raw3615step0 = raw3615.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3615).symm
    injectiveMoment H raw3615step0 = injectiveMoment H raw3615step1 := by
      have heq : raw3615step1 = (fun i j => raw3615step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3615step0 permutation18 permutation21
    _ = injectiveMoment H node1313 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4015 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4015 = injectiveMoment H node28 := by
  calc
    injectiveMoment H raw4015 = injectiveMoment H raw4015step0 := by
      have heq : raw4015step0 = -raw4015 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4015).symm
    injectiveMoment H raw4015step0 = injectiveMoment H raw4015step1 := by
      have heq : raw4015step1 = (fun i j => raw4015step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4015step0 permutation8 permutation3
    _ = injectiveMoment H node28 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical4199 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4199 = injectiveMoment H node147 := by
  calc
    injectiveMoment H raw4199 = injectiveMoment H raw4199step0 := by
      have heq : raw4199step0 = raw4199.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4199).symm
    injectiveMoment H raw4199step0 = injectiveMoment H raw4199step1 := by
      have heq : raw4199step1 = -raw4199step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4199step0).symm
    injectiveMoment H raw4199step1 = injectiveMoment H raw4199step2 := by
      have heq : raw4199step2 = (fun i j => raw4199step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4199step1 permutation26 permutation4
    _ = injectiveMoment H node147 := by rfl

theorem canonical4214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4214 = injectiveMoment H node2144 := by
  rfl

theorem canonical4215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4215 = injectiveMoment H node2682 := by
  calc
    injectiveMoment H raw4215 = injectiveMoment H raw4215step0 := by
      have heq : raw4215step0 = (fun i j => raw4215 (permutation60 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4215 permutation60 permutation15
    _ = injectiveMoment H node2682 := by rfl

theorem canonical4216 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4216 = injectiveMoment H node2011 := by
  calc
    injectiveMoment H raw4216 = injectiveMoment H raw4216step0 := by
      have heq : raw4216step0 = -raw4216 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4216).symm
    injectiveMoment H raw4216step0 = injectiveMoment H raw4216step1 := by
      have heq : raw4216step1 = (fun i j => raw4216step0 (permutation99 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4216step0 permutation99 permutation15
    _ = injectiveMoment H node2011 := by rfl

theorem canonical4217 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4217 = injectiveMoment H node1158 := by
  calc
    injectiveMoment H raw4217 = injectiveMoment H raw4217step0 := by
      have heq : raw4217step0 = raw4217.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4217).symm
    injectiveMoment H raw4217step0 = injectiveMoment H raw4217step1 := by
      have heq : raw4217step1 = -raw4217step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4217step0).symm
    injectiveMoment H raw4217step1 = injectiveMoment H raw4217step2 := by
      have heq : raw4217step2 = (fun i j => raw4217step1 (permutation12 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4217step1 permutation12 permutation25
    _ = injectiveMoment H node1158 := by rfl

theorem canonical4218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4218 = injectiveMoment H node780 := by
  calc
    injectiveMoment H raw4218 = injectiveMoment H raw4218step0 := by
      have heq : raw4218step0 = raw4218.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4218).symm
    injectiveMoment H raw4218step0 = injectiveMoment H raw4218step1 := by
      have heq : raw4218step1 = (fun i j => raw4218step0 (permutation32 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4218step0 permutation32 permutation25
    _ = injectiveMoment H node780 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4224 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4224 = injectiveMoment H node2763 := by
  calc
    injectiveMoment H raw4224 = injectiveMoment H raw4224step0 := by
      have heq : raw4224step0 = -raw4224 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4224).symm
    injectiveMoment H raw4224step0 = injectiveMoment H raw4224step1 := by
      have heq : raw4224step1 = (fun i j => raw4224step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4224step0 permutation100 permutation15
    _ = injectiveMoment H node2763 := by rfl

theorem canonical4225 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4225 = injectiveMoment H node1065 := by
  calc
    injectiveMoment H raw4225 = injectiveMoment H raw4225step0 := by
      have heq : raw4225step0 = -raw4225 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4225).symm
    injectiveMoment H raw4225step0 = injectiveMoment H raw4225step1 := by
      have heq : raw4225step1 = (fun i j => raw4225step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4225step0 permutation29 permutation15
    _ = injectiveMoment H node1065 := by rfl

theorem canonical4241 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4241 = injectiveMoment H node88 := by
  calc
    injectiveMoment H raw4241 = injectiveMoment H raw4241step0 := by
      have heq : raw4241step0 = raw4241.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4241).symm
    injectiveMoment H raw4241step0 = injectiveMoment H raw4241step1 := by
      have heq : raw4241step1 = -raw4241step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4241step0).symm
    injectiveMoment H raw4241step1 = injectiveMoment H raw4241step2 := by
      have heq : raw4241step2 = (fun i j => raw4241step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4241step1 permutation24 permutation3
    _ = injectiveMoment H node88 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5076 = injectiveMoment H node2324 := by
  rfl

theorem canonical5077 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5077 = injectiveMoment H node1064 := by
  calc
    injectiveMoment H raw5077 = injectiveMoment H raw5077step0 := by
      have heq : raw5077step0 = raw5077.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5077).symm
    injectiveMoment H raw5077step0 = injectiveMoment H raw5077step1 := by
      have heq : raw5077step1 = -raw5077step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5077step0).symm
    injectiveMoment H raw5077step1 = injectiveMoment H raw5077step2 := by
      have heq : raw5077step2 = (fun i j => raw5077step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5077step1 permutation12 permutation26
    _ = injectiveMoment H node1064 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw556 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw556 = injectiveMoment H raw556step0 := by
      have heq : raw556step0 = (fun i j => raw556 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw556 permutation7 permutation6
    _ = injectiveMoment H node37 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5507 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5507 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw5507 = injectiveMoment H raw5507step0 := by
      have heq : raw5507step0 = raw5507.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5507).symm
    injectiveMoment H raw5507step0 = injectiveMoment H raw5507step1 := by
      have heq : raw5507step1 = (fun i j => raw5507step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5507step0 permutation8 permutation8
    _ = injectiveMoment H node32 := by rfl

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

theorem canonical5547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5547 = injectiveMoment H node52 := by
  rfl

theorem canonical5550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5550 = injectiveMoment H node53 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5619 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5619 = injectiveMoment H node81 := by
  calc
    injectiveMoment H raw5619 = injectiveMoment H raw5619step0 := by
      have heq : raw5619step0 = raw5619.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5619).symm
    injectiveMoment H raw5619step0 = injectiveMoment H raw5619step1 := by
      have heq : raw5619step1 = (fun i j => raw5619step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5619step0 permutation27 permutation6
    _ = injectiveMoment H node81 := by rfl

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

theorem canonical5634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5634 = injectiveMoment H node190 := by
  calc
    injectiveMoment H raw5634 = injectiveMoment H raw5634step0 := by
      have heq : raw5634step0 = raw5634.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5634).symm
    injectiveMoment H raw5634step0 = injectiveMoment H raw5634step1 := by
      have heq : raw5634step1 = (fun i j => raw5634step0 (permutation26 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5634step0 permutation26 permutation7
    _ = injectiveMoment H node190 := by rfl

theorem canonical5641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5641 = injectiveMoment H node171 := by
  calc
    injectiveMoment H raw5641 = injectiveMoment H raw5641step0 := by
      have heq : raw5641step0 = raw5641.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5641).symm
    injectiveMoment H raw5641step0 = injectiveMoment H raw5641step1 := by
      have heq : raw5641step1 = (fun i j => raw5641step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5641step0 permutation22 permutation7
    _ = injectiveMoment H node171 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical190
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6094 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw6094 = injectiveMoment H raw6094step0 := by
      have heq : raw6094step0 = raw6094.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6094).symm
    injectiveMoment H raw6094step0 = injectiveMoment H raw6094step1 := by
      have heq : raw6094step1 = (fun i j => raw6094step0 (permutation31 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6094step0 permutation31 permutation8
    _ = injectiveMoment H node248 := by rfl

theorem canonical6111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6111 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw6111 = injectiveMoment H raw6111step0 := by
      have heq : raw6111step0 = raw6111.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6111).symm
    injectiveMoment H raw6111step0 = injectiveMoment H raw6111step1 := by
      have heq : raw6111step1 = (fun i j => raw6111step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6111step0 permutation30 permutation8
    _ = injectiveMoment H node254 := by rfl

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

theorem canonical6298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6298 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw6298 = injectiveMoment H raw6298step0 := by
      have heq : raw6298step0 = raw6298.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6298).symm
    injectiveMoment H raw6298step0 = injectiveMoment H raw6298step1 := by
      have heq : raw6298step1 = (fun i j => raw6298step0 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6298step0 permutation25 permutation7
    _ = injectiveMoment H node188 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6338 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6338 = injectiveMoment H raw6338step0 := by
      have heq : raw6338step0 = raw6338.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6338).symm
    injectiveMoment H raw6338step0 = injectiveMoment H raw6338step1 := by
      have heq : raw6338step1 = (fun i j => raw6338step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6338step0 permutation21 permutation7
    _ = injectiveMoment H node173 := by rfl

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

theorem canonical6517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6517 = injectiveMoment H node1065 := by
  rfl

theorem canonical6519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6519 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw6519 = injectiveMoment H raw6519step0 := by
      have heq : raw6519step0 = raw6519.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6519).symm
    injectiveMoment H raw6519step0 = injectiveMoment H raw6519step1 := by
      have heq : raw6519step1 = -raw6519step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6519step0).symm
    injectiveMoment H raw6519step1 = injectiveMoment H raw6519step2 := by
      have heq : raw6519step2 = (fun i j => raw6519step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6519step1 permutation31 permutation4
    _ = injectiveMoment H node188 := by rfl

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

theorem canonical6564 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6564 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw6564 = injectiveMoment H raw6564step0 := by
      have heq : raw6564step0 = raw6564.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6564).symm
    injectiveMoment H raw6564step0 = injectiveMoment H raw6564step1 := by
      have heq : raw6564step1 = -raw6564step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6564step0).symm
    injectiveMoment H raw6564step1 = injectiveMoment H raw6564step2 := by
      have heq : raw6564step2 = (fun i j => raw6564step1 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6564step1 permutation32 permutation4
    _ = injectiveMoment H node187 := by rfl

theorem canonical6567 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6567 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6567 = injectiveMoment H raw6567step0 := by
      have heq : raw6567step0 = raw6567.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6567).symm
    injectiveMoment H raw6567step0 = injectiveMoment H raw6567step1 := by
      have heq : raw6567step1 = -raw6567step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6567step0).symm
    injectiveMoment H raw6567step1 = injectiveMoment H raw6567step2 := by
      have heq : raw6567step2 = (fun i j => raw6567step1 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6567step1 permutation32 permutation4
    _ = injectiveMoment H node185 := by rfl

theorem canonical6568 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6568 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw6568 = injectiveMoment H raw6568step0 := by
      have heq : raw6568step0 = raw6568.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6568).symm
    injectiveMoment H raw6568step0 = injectiveMoment H raw6568step1 := by
      have heq : raw6568step1 = -raw6568step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6568step0).symm
    injectiveMoment H raw6568step1 = injectiveMoment H raw6568step2 := by
      have heq : raw6568step2 = (fun i j => raw6568step1 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6568step1 permutation32 permutation4
    _ = injectiveMoment H node155 := by rfl

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

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6989 = injectiveMoment H node780 := by
  calc
    injectiveMoment H raw6989 = injectiveMoment H raw6989step0 := by
      have heq : raw6989step0 = raw6989.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6989).symm
    injectiveMoment H raw6989step0 = injectiveMoment H raw6989step1 := by
      have heq : raw6989step1 = (fun i j => raw6989step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6989step0 permutation31 permutation26
    _ = injectiveMoment H node780 := by rfl

theorem canonical6990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6990 = injectiveMoment H node781 := by
  calc
    injectiveMoment H raw6990 = injectiveMoment H raw6990step0 := by
      have heq : raw6990step0 = raw6990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6990).symm
    injectiveMoment H raw6990step0 = injectiveMoment H raw6990step1 := by
      have heq : raw6990step1 = (fun i j => raw6990step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6990step0 permutation32 permutation32
    _ = injectiveMoment H node781 := by rfl

theorem canonical7002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7002 = injectiveMoment H node919 := by
  calc
    injectiveMoment H raw7002 = injectiveMoment H raw7002step0 := by
      have heq : raw7002step0 = raw7002.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7002).symm
    injectiveMoment H raw7002step0 = injectiveMoment H raw7002step1 := by
      have heq : raw7002step1 = (fun i j => raw7002step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7002step0 permutation32 permutation32
    _ = injectiveMoment H node919 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7022 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7022 = injectiveMoment H raw7022step0 := by
      have hz : ∀ i, raw7022 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7022step0 = (fun i j => raw7022 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7022 permutation15 hz
    _ = injectiveMoment H node53 := by rfl

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

theorem canonical7124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7124 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7124 = injectiveMoment H raw7124step0 := by
      have heq : raw7124step0 = raw7124.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7124).symm
    injectiveMoment H raw7124step0 = injectiveMoment H raw7124step1 := by
      have heq : raw7124step1 = (fun i j => raw7124step0 (permutation17 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7124step0 permutation17 permutation7
    _ = injectiveMoment H node201 := by rfl

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

theorem canonical7408 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7408 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7408 = injectiveMoment H raw7408step0 := by
      have heq : raw7408step0 = -raw7408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7408).symm
    injectiveMoment H raw7408step0 = injectiveMoment H raw7408step1 := by
      have heq : raw7408step1 = (fun i j => raw7408step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7408step0 permutation8 permutation3
    _ = injectiveMoment H node53 := by rfl

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

theorem canonical7541 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7541 = injectiveMoment H node154 := by
  calc
    injectiveMoment H raw7541 = injectiveMoment H raw7541step0 := by
      have heq : raw7541step0 = raw7541.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7541).symm
    injectiveMoment H raw7541step0 = injectiveMoment H raw7541step1 := by
      have heq : raw7541step1 = -raw7541step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7541step0).symm
    injectiveMoment H raw7541step1 = injectiveMoment H raw7541step2 := by
      have heq : raw7541step2 = (fun i j => raw7541step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7541step1 permutation23 permutation4
    _ = injectiveMoment H node154 := by rfl

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

theorem canonical7593 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7593 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw7593 = injectiveMoment H raw7593step0 := by
      have heq : raw7593step0 = raw7593.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7593).symm
    injectiveMoment H raw7593step0 = injectiveMoment H raw7593step1 := by
      have heq : raw7593step1 = -raw7593step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7593step0).symm
    injectiveMoment H raw7593step1 = injectiveMoment H raw7593step2 := by
      have heq : raw7593step2 = (fun i j => raw7593step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7593step1 permutation23 permutation4
    _ = injectiveMoment H node155 := by rfl

theorem canonical7604 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7604 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw7604 = injectiveMoment H raw7604step0 := by
      have heq : raw7604step0 = raw7604.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7604).symm
    injectiveMoment H raw7604step0 = injectiveMoment H raw7604step1 := by
      have heq : raw7604step1 = -raw7604step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7604step0).symm
    injectiveMoment H raw7604step1 = injectiveMoment H raw7604step2 := by
      have heq : raw7604step2 = (fun i j => raw7604step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7604step1 permutation23 permutation3
    _ = injectiveMoment H node187 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7618 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7618 = injectiveMoment H node87 := by
  calc
    injectiveMoment H raw7618 = injectiveMoment H raw7618step0 := by
      have heq : raw7618step0 = raw7618.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7618).symm
    injectiveMoment H raw7618step0 = injectiveMoment H raw7618step1 := by
      have heq : raw7618step1 = -raw7618step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7618step0).symm
    injectiveMoment H raw7618step1 = injectiveMoment H raw7618step2 := by
      have heq : raw7618step2 = (fun i j => raw7618step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7618step1 permutation23 permutation3
    _ = injectiveMoment H node87 := by rfl

theorem canonical7620 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7620 = injectiveMoment H node86 := by
  calc
    injectiveMoment H raw7620 = injectiveMoment H raw7620step0 := by
      have heq : raw7620step0 = raw7620.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7620).symm
    injectiveMoment H raw7620step0 = injectiveMoment H raw7620step1 := by
      have heq : raw7620step1 = -raw7620step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7620step0).symm
    injectiveMoment H raw7620step1 = injectiveMoment H raw7620step2 := by
      have heq : raw7620step2 = (fun i j => raw7620step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7620step1 permutation23 permutation3
    _ = injectiveMoment H node86 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical242
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7774 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7774 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw7774 = injectiveMoment H raw7774step0 := by
      have heq : raw7774step0 = raw7774.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7774).symm
    injectiveMoment H raw7774step0 = injectiveMoment H raw7774step1 := by
      have heq : raw7774step1 = (fun i j => raw7774step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7774step0 permutation32 permutation32
    _ = injectiveMoment H node977 := by rfl

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

theorem canonical7996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7996 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7996 = injectiveMoment H raw7996step0 := by
      have heq : raw7996step0 = (fun i j => raw7996 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7996 permutation5 permutation4
    _ = injectiveMoment H node58 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8047 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw8047 = injectiveMoment H raw8047step0 := by
      have hz : ∀ i, raw8047 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8047step0 = (fun i j => raw8047 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8047 permutation9 hz
    _ = injectiveMoment H node37 := by rfl

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

theorem canonical8097 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8097 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw8097 = injectiveMoment H raw8097step0 := by
      have heq : raw8097step0 = -raw8097 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8097).symm
    injectiveMoment H raw8097step0 = injectiveMoment H raw8097step1 := by
      have hz : ∀ i, raw8097step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8097step1 = (fun i j => raw8097step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8097step0 permutation9 hz
    injectiveMoment H raw8097step1 = injectiveMoment H raw8097step2 := by
      have heq : raw8097step2 = (fun i j => raw8097step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8097step1 permutation8 permutation4
    _ = injectiveMoment H node37 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical260
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8337 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw8337 = injectiveMoment H raw8337step0 := by
      have hz : ∀ i, raw8337 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8337step0 = (fun i j => raw8337 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8337 permutation9 hz
    _ = injectiveMoment H node63 := by rfl

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

theorem canonical8370 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8370 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw8370 = injectiveMoment H raw8370step0 := by
      have heq : raw8370step0 = raw8370.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8370).symm
    injectiveMoment H raw8370step0 = injectiveMoment H raw8370step1 := by
      have heq : raw8370step1 = (fun i j => raw8370step0 (permutation18 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8370step0 permutation18 permutation27
    _ = injectiveMoment H node1063 := by rfl

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

theorem canonical8499 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8499 = injectiveMoment H node1062 := by
  calc
    injectiveMoment H raw8499 = injectiveMoment H raw8499step0 := by
      have heq : raw8499step0 = raw8499.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8499).symm
    injectiveMoment H raw8499step0 = injectiveMoment H raw8499step1 := by
      have heq : raw8499step1 = (fun i j => raw8499step0 (permutation18 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8499step0 permutation18 permutation27
    _ = injectiveMoment H node1062 := by rfl

theorem canonical8501 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8501 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw8501 = injectiveMoment H raw8501step0 := by
      have heq : raw8501step0 = -raw8501 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8501).symm
    injectiveMoment H raw8501step0 = injectiveMoment H raw8501step1 := by
      have hz : ∀ i, raw8501step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8501step1 = (fun i j => raw8501step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8501step0 permutation9 hz
    injectiveMoment H raw8501step1 = injectiveMoment H raw8501step2 := by
      have heq : raw8501step2 = (fun i j => raw8501step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8501step1 permutation8 permutation4
    _ = injectiveMoment H node58 := by rfl

theorem canonical8502 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8502 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw8502 = injectiveMoment H raw8502step0 := by
      have heq : raw8502step0 = -raw8502 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8502).symm
    injectiveMoment H raw8502step0 = injectiveMoment H raw8502step1 := by
      have hz : ∀ i, raw8502step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8502step1 = (fun i j => raw8502step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8502step0 permutation9 hz
    injectiveMoment H raw8502step1 = injectiveMoment H raw8502step2 := by
      have heq : raw8502step2 = (fun i j => raw8502step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8502step1 permutation23 permutation4
    _ = injectiveMoment H node188 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical283
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9066 = injectiveMoment H node195 := by
  calc
    injectiveMoment H raw9066 = injectiveMoment H raw9066step0 := by
      have heq : raw9066step0 = raw9066.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9066).symm
    injectiveMoment H raw9066step0 = injectiveMoment H raw9066step1 := by
      have heq : raw9066step1 = (fun i j => raw9066step0 (permutation17 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9066step0 permutation17 permutation7
    _ = injectiveMoment H node195 := by rfl

theorem canonical9080 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9080 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw9080 = injectiveMoment H raw9080step0 := by
      have heq : raw9080step0 = -raw9080 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9080).symm
    injectiveMoment H raw9080step0 = injectiveMoment H raw9080step1 := by
      have hz : ∀ i, raw9080step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9080step1 = (fun i j => raw9080step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9080step0 permutation9 hz
    injectiveMoment H raw9080step1 = injectiveMoment H raw9080step2 := by
      have heq : raw9080step2 = (fun i j => raw9080step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9080step1 permutation5 permutation3
    _ = injectiveMoment H node32 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9985 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9985 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw9985 = injectiveMoment H raw9985step0 := by
      have heq : raw9985step0 = raw9985.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9985).symm
    injectiveMoment H raw9985step0 = injectiveMoment H raw9985step1 := by
      have heq : raw9985step1 = -raw9985step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9985step0).symm
    injectiveMoment H raw9985step1 = injectiveMoment H raw9985step2 := by
      have heq : raw9985step2 = (fun i j => raw9985step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9985step1 permutation21 permutation3
    _ = injectiveMoment H node170 := by rfl

theorem canonical9989 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9989 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw9989 = injectiveMoment H raw9989step0 := by
      have heq : raw9989step0 = raw9989.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9989).symm
    injectiveMoment H raw9989step0 = injectiveMoment H raw9989step1 := by
      have heq : raw9989step1 = -raw9989step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9989step0).symm
    injectiveMoment H raw9989step1 = injectiveMoment H raw9989step2 := by
      have heq : raw9989step2 = (fun i j => raw9989step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9989step1 permutation21 permutation3
    _ = injectiveMoment H node163 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2096 = injectiveMoment H node1158 := by
  calc
    injectiveMoment H raw2096 = injectiveMoment H raw2096step0 := by
      have heq : raw2096step0 = raw2096.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2096).symm
    injectiveMoment H raw2096step0 = injectiveMoment H raw2096step1 := by
      have heq : raw2096step1 = (fun i j => raw2096step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2096step0 permutation18 permutation21
    _ = injectiveMoment H node1158 := by rfl

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

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
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

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical312 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw312 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw312 = injectiveMoment H raw312step0 := by
      have heq : raw312step0 = raw312.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw312).symm
    injectiveMoment H raw312step0 = injectiveMoment H raw312step1 := by
      have heq : raw312step1 = (fun i j => raw312step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw312step0 permutation7 permutation6
    _ = injectiveMoment H node32 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound81 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node81 = Sparse.eval value81 (momentVector H) := by
  have heq : pivotMatrix81 = (fun u v => node81 (pivotPermutation81 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node81 = injectiveMoment H pivotMatrix81 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix81 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix81 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix81 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix81 (0 : Fin 3) = raw556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical556 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix81 (1 : Fin 3)) =
      Sparse.eval value18 (momentVector H) := by
    have heq : mergeFirst pivotMatrix81 (1 : Fin 3) = raw320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical320 hH).trans (sound18 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix81 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix81 (2 : Fin 3) = raw312 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical312 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node81 + (injectiveMoment H (mergeFirst pivotMatrix81 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix81 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix81 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value81, value18, value32, value37, Sparse.eval] at hc ⊢
  linarith

theorem sound86 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node86 = Sparse.eval value86 (momentVector H) := by
  have hc : momentVector H 260 = injectiveMoment H node86 := rfl
  simp [value86, Sparse.eval, hc]

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

theorem sound88 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node88 = Sparse.eval value88 (momentVector H) := by
  have heq : pivotMatrix88 = (fun u v => node88 (pivotPermutation88 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node88 = injectiveMoment H pivotMatrix88 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix88 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix88 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix88 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix88 (0 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix88 (1 : Fin 3)) =
      Sparse.eval value38 (momentVector H) := by
    have heq : mergeFirst pivotMatrix88 (1 : Fin 3) = raw335 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical335 hH).trans (sound38 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix88 (2 : Fin 3)) =
      Sparse.eval value18 (momentVector H) := by
    have heq : mergeFirst pivotMatrix88 (2 : Fin 3) = raw320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical320 hH).trans (sound18 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node88 + (injectiveMoment H (mergeFirst pivotMatrix88 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix88 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix88 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value88, value18, value37, value38, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node147 = Sparse.eval value147 (momentVector H) := by
  have heq : pivotMatrix147 = (fun u v => node147 (pivotPermutation147 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node147 = injectiveMoment H pivotMatrix147 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix147 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix147 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix147 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix147 (0 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix147 (1 : Fin 3)) =
      Sparse.eval value33 (momentVector H) := by
    have heq : mergeFirst pivotMatrix147 (1 : Fin 3) = raw1442 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1442 hH).trans (sound33 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix147 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix147 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node147 + (injectiveMoment H (mergeFirst pivotMatrix147 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix147 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix147 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value147, value32, value33, value37, Sparse.eval] at hc ⊢
  linarith

theorem sound154 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node154 = Sparse.eval value154 (momentVector H) := by
  have hc : momentVector H 309 = injectiveMoment H node154 := rfl
  simp [value154, Sparse.eval, hc]

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

theorem sound163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node163 = Sparse.eval value163 (momentVector H) := by
  have hc : momentVector H 125 = injectiveMoment H node163 := rfl
  simp [value163, Sparse.eval, hc]

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

theorem sound171 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node171 = Sparse.eval value171 (momentVector H) := by
  have heq : pivotMatrix171 = (fun u v => node171 (pivotPermutation171 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node171 = injectiveMoment H pivotMatrix171 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix171 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix171 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix171 (0 : Fin 3)) =
      Sparse.eval value33 (momentVector H) := by
    have heq : mergeFirst pivotMatrix171 (0 : Fin 3) = raw1442 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1442 hH).trans (sound33 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix171 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix171 (1 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix171 (2 : Fin 3)) =
      Sparse.eval value38 (momentVector H) := by
    have heq : mergeFirst pivotMatrix171 (2 : Fin 3) = raw2853 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2853 hH).trans (sound38 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node171 + (injectiveMoment H (mergeFirst pivotMatrix171 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix171 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix171 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value171, value33, value37, value38, Sparse.eval] at hc ⊢
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
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound195 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node195 = Sparse.eval value195 (momentVector H) := by
  have heq : pivotMatrix195 = (fun u v => node195 (pivotPermutation195 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node195 = injectiveMoment H pivotMatrix195 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix195 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix195 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix195 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix195 (0 : Fin 3) = raw7408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7408 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix195 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix195 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix195 (2 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix195 (2 : Fin 3) = raw4015 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4015 hH).trans (sound28 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node195 + (injectiveMoment H (mergeFirst pivotMatrix195 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix195 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix195 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value195, value28, value32, value53, Sparse.eval] at hc ⊢
  linarith

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

theorem sound248 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node248 = Sparse.eval value248 (momentVector H) := by
  have heq : pivotMatrix248 = (fun u v => node248 (pivotPermutation248 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node248 = injectiveMoment H pivotMatrix248 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix248 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix248 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix248 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix248 (0 : Fin 3) = raw7996 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7996 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix248 (1 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix248 (1 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix248 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix248 (2 : Fin 3) = raw5507 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5507 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node248 + (injectiveMoment H (mergeFirst pivotMatrix248 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix248 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix248 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value248, value32, value53, value58, Sparse.eval] at hc ⊢
  linarith

theorem sound254 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node254 = Sparse.eval value254 (momentVector H) := by
  have heq : pivotMatrix254 = (fun u v => node254 (pivotPermutation254 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node254 = injectiveMoment H pivotMatrix254 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix254 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix254 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix254 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix254 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix254 (1 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix254 (1 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix254 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix254 (2 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node254 + (injectiveMoment H (mergeFirst pivotMatrix254 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix254 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix254 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value254, value52, value53, value57, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound12
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound780 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node780 = Sparse.eval value780 (momentVector H) := by
  have heq : pivotMatrix780 = (fun u v => node780 (pivotPermutation780 u) v) := by apply Matrix.ext; unfold pivotMatrix780 node780 pivotPermutation780; decide +kernel
  have hmoment : injectiveMoment H node780 = injectiveMoment H pivotMatrix780 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix780 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix780 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix780 (0 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix780 (0 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix780 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix780 (1 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix780 (1 : Fin 3) = raw5634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix780 raw5634; decide +kernel
    rw [heq]
    exact (canonical5634 hH).trans (sound190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix780 (2 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix780 (2 : Fin 3) = raw5619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix780 raw5619; decide +kernel
    rw [heq]
    exact (canonical5619 hH).trans (sound81 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node780 + (injectiveMoment H (mergeFirst pivotMatrix780 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix780 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix780 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value780, value188, value190, value81, Sparse.eval] at hc ⊢
  linarith

theorem sound781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node781 = Sparse.eval value781 (momentVector H) := by
  have heq : pivotMatrix781 = (fun u v => node781 (pivotPermutation781 u) v) := by apply Matrix.ext; unfold pivotMatrix781 node781 pivotPermutation781; decide +kernel
  have hmoment : injectiveMoment H node781 = injectiveMoment H pivotMatrix781 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix781 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix781 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix781 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix781 (0 : Fin 3) = raw8047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix781 raw8047; decide +kernel
    rw [heq]
    exact (canonical8047 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix781 (1 : Fin 3)) =
      Sparse.eval value171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix781 (1 : Fin 3) = raw5641 := by apply Matrix.ext; unfold mergeFirst pivotMatrix781 raw5641; decide +kernel
    rw [heq]
    exact (canonical5641 hH).trans (sound171 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix781 (2 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix781 (2 : Fin 3) = raw5619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix781 raw5619; decide +kernel
    rw [heq]
    exact (canonical5619 hH).trans (sound81 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node781 + (injectiveMoment H (mergeFirst pivotMatrix781 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix781 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix781 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value781, value171, value37, value81, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound14
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound919 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node919 = Sparse.eval value919 (momentVector H) := by
  have heq : pivotMatrix919 = (fun u v => node919 (pivotPermutation919 u) v) := by apply Matrix.ext; unfold pivotMatrix919 node919 pivotPermutation919; decide +kernel
  have hmoment : injectiveMoment H node919 = injectiveMoment H pivotMatrix919 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix919 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix919 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix919 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix919 (0 : Fin 3) = raw7022 := by apply Matrix.ext; unfold mergeFirst pivotMatrix919 raw7022; decide +kernel
    rw [heq]
    exact (canonical7022 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix919 (1 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix919 (1 : Fin 3) = raw6111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix919 raw6111; decide +kernel
    rw [heq]
    exact (canonical6111 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix919 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix919 (2 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix919 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node919 + (injectiveMoment H (mergeFirst pivotMatrix919 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix919 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix919 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value919, value248, value254, value53, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound15
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node977 = Sparse.eval value977 (momentVector H) := by
  have heq : pivotMatrix977 = (fun u v => node977 (pivotPermutation977 u) v) := by apply Matrix.ext; unfold pivotMatrix977 node977 pivotPermutation977; decide +kernel
  have hmoment : injectiveMoment H node977 = injectiveMoment H pivotMatrix977 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix977 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix977 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix977 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix977 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (1 : Fin 3) = raw6338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw6338; decide +kernel
    rw [heq]
    exact (canonical6338 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix977 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (2 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node977 + (injectiveMoment H (mergeFirst pivotMatrix977 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix977 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix977 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value977, value173, value188, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound16
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1062 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1062 = Sparse.eval value1062 (momentVector H) := by
  have heq : pivotMatrix1062 = (fun u v => node1062 (pivotPermutation1062 u) v) := by apply Matrix.ext; unfold pivotMatrix1062 node1062 pivotPermutation1062; decide +kernel
  have hmoment : injectiveMoment H node1062 = injectiveMoment H pivotMatrix1062 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1062 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1062 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1062 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1062 (0 : Fin 3) = raw8501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1062 raw8501; decide +kernel
    rw [heq]
    exact (canonical8501 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1062 (1 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1062 (1 : Fin 3) = raw6568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1062 raw6568; decide +kernel
    rw [heq]
    exact (canonical6568 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1062 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1062 (2 : Fin 3) = raw6519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1062 raw6519; decide +kernel
    rw [heq]
    exact (canonical6519 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1062 + (injectiveMoment H (mergeFirst pivotMatrix1062 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1062 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1062 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1062, value155, value188, value58, Sparse.eval] at hc ⊢
  linarith

theorem sound1063 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1063 = Sparse.eval value1063 (momentVector H) := by
  have heq : pivotMatrix1063 = (fun u v => node1063 (pivotPermutation1063 u) v) := by apply Matrix.ext; unfold pivotMatrix1063 node1063 pivotPermutation1063; decide +kernel
  have hmoment : injectiveMoment H node1063 = injectiveMoment H pivotMatrix1063 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1063 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1063 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1063 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1063 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1063 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1063 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1063 (1 : Fin 3) = raw6567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1063 raw6567; decide +kernel
    rw [heq]
    exact (canonical6567 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1063 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1063 (2 : Fin 3) = raw6519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1063 raw6519; decide +kernel
    rw [heq]
    exact (canonical6519 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1063 + (injectiveMoment H (mergeFirst pivotMatrix1063 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1063 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1063 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1063, value185, value188, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound1064 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1064 = Sparse.eval value1064 (momentVector H) := by
  have heq : pivotMatrix1064 = (fun u v => node1064.transpose (pivotPermutation1064 u) v) := by apply Matrix.ext; unfold pivotMatrix1064 node1064 pivotPermutation1064; decide +kernel
  have hmoment : injectiveMoment H node1064 = injectiveMoment H pivotMatrix1064 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1064 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1064 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1064 (0 : Fin 3)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1064 (0 : Fin 3) = raw4199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1064 raw4199; decide +kernel
    rw [heq]
    exact (canonical4199 hH).trans (sound147 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1064 (1 : Fin 3)) =
      Sparse.eval value154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1064 (1 : Fin 3) = raw7541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1064 raw7541; decide +kernel
    rw [heq]
    exact (canonical7541 hH).trans (sound154 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1064 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1064 (2 : Fin 3) = raw7593 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1064 raw7593; decide +kernel
    rw [heq]
    exact (canonical7593 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1064 + (injectiveMoment H (mergeFirst pivotMatrix1064 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1064 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1064 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1064, value147, value154, value155, Sparse.eval] at hc ⊢
  linarith

theorem sound1065 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1065 = Sparse.eval value1065 (momentVector H) := by
  have heq : pivotMatrix1065 = (fun u v => node1065 (pivotPermutation1065 u) v) := by apply Matrix.ext; unfold pivotMatrix1065 node1065 pivotPermutation1065; decide +kernel
  have hmoment : injectiveMoment H node1065 = injectiveMoment H pivotMatrix1065 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1065 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1065 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1065 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1065 (0 : Fin 3) = raw8097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1065 raw8097; decide +kernel
    rw [heq]
    exact (canonical8097 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1065 (1 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1065 (1 : Fin 3) = raw6564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1065 raw6564; decide +kernel
    rw [heq]
    exact (canonical6564 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1065 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1065 (2 : Fin 3) = raw6519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1065 raw6519; decide +kernel
    rw [heq]
    exact (canonical6519 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1065 + (injectiveMoment H (mergeFirst pivotMatrix1065 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1065 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1065 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1065, value187, value188, value37, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound18
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1158 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1158 = Sparse.eval value1158 (momentVector H) := by
  have heq : pivotMatrix1158 = (fun u v => node1158.transpose (pivotPermutation1158 u) v) := by apply Matrix.ext; unfold pivotMatrix1158 node1158 pivotPermutation1158; decide +kernel
  have hmoment : injectiveMoment H node1158 = injectiveMoment H pivotMatrix1158 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1158 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1158 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1158 (0 : Fin 3)) =
      Sparse.eval value88 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1158 (0 : Fin 3) = raw4241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1158 raw4241; decide +kernel
    rw [heq]
    exact (canonical4241 hH).trans (sound88 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1158 (1 : Fin 3)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1158 (1 : Fin 3) = raw7618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1158 raw7618; decide +kernel
    rw [heq]
    exact (canonical7618 hH).trans (sound87 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1158 (2 : Fin 3)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1158 (2 : Fin 3) = raw7620 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1158 raw7620; decide +kernel
    rw [heq]
    exact (canonical7620 hH).trans (sound86 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1158 + (injectiveMoment H (mergeFirst pivotMatrix1158 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1158 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1158 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1158, value86, value87, value88, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound20
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1300 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1300 = Sparse.eval value1300 (momentVector H) := by
  have heq : pivotMatrix1300 = (fun u v => node1300 (pivotPermutation1300 u) v) := by apply Matrix.ext; unfold pivotMatrix1300 node1300 pivotPermutation1300; decide +kernel
  have hmoment : injectiveMoment H node1300 = injectiveMoment H pivotMatrix1300 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1300 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1300 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1300 (0 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1300 (0 : Fin 3) = raw7124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1300 raw7124; decide +kernel
    rw [heq]
    exact (canonical7124 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1300 (1 : Fin 3)) =
      Sparse.eval value195 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1300 (1 : Fin 3) = raw9066 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1300 raw9066; decide +kernel
    rw [heq]
    exact (canonical9066 hH).trans (sound195 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1300 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1300 (2 : Fin 3) = raw9080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1300 raw9080; decide +kernel
    rw [heq]
    exact (canonical9080 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1300 + (injectiveMoment H (mergeFirst pivotMatrix1300 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1300 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1300 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1300, value195, value201, value32, Sparse.eval] at hc ⊢
  linarith

theorem sound1313 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1313 = Sparse.eval value1313 (momentVector H) := by
  have heq : pivotMatrix1313 = (fun u v => node1313.transpose (pivotPermutation1313 u) v) := by apply Matrix.ext; unfold pivotMatrix1313 node1313 pivotPermutation1313; decide +kernel
  have hmoment : injectiveMoment H node1313 = injectiveMoment H pivotMatrix1313 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1313 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1313 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1313 (0 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1313 (0 : Fin 3) = raw7604 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1313 raw7604; decide +kernel
    rw [heq]
    exact (canonical7604 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1313 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1313 (1 : Fin 3) = raw9985 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1313 raw9985; decide +kernel
    rw [heq]
    exact (canonical9985 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1313 (2 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1313 (2 : Fin 3) = raw9989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1313 raw9989; decide +kernel
    rw [heq]
    exact (canonical9989 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1313 + (injectiveMoment H (mergeFirst pivotMatrix1313 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1313 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1313 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1313, value163, value170, value187, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound7
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound461 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node461 = Sparse.eval value461 (momentVector H) := by
  have hc : momentVector H 323 = injectiveMoment H node461 := rfl
  simp [value461, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound31
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2011 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2011 = Sparse.eval value2011 (momentVector H) := by
  have heq : pivotMatrix2011 = (fun u v => node2011 (pivotPermutation2011 u) v) := by apply Matrix.ext; unfold pivotMatrix2011 node2011 pivotPermutation2011; decide +kernel
  have hmoment : injectiveMoment H node2011 = injectiveMoment H pivotMatrix2011 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2011 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2011 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2011 (0 : Fin 4)) =
      Sparse.eval value1158 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2011 (0 : Fin 4) = raw2096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2011 raw2096; decide +kernel
    rw [heq]
    exact (canonical2096 hH).trans (sound1158 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2011 (1 : Fin 4)) =
      Sparse.eval value1300 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2011 (1 : Fin 4) = raw3517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2011 raw3517; decide +kernel
    rw [heq]
    exact (canonical3517 hH).trans (sound1300 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2011 (2 : Fin 4)) =
      Sparse.eval value461 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2011 (2 : Fin 4) = raw3611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2011 raw3611; decide +kernel
    rw [heq]
    exact (canonical3611 hH).trans (sound461 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2011 (3 : Fin 4)) =
      Sparse.eval value1313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2011 (3 : Fin 4) = raw3615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2011 raw3615; decide +kernel
    rw [heq]
    exact (canonical3615 hH).trans (sound1313 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2011 + (injectiveMoment H (mergeFirst pivotMatrix2011 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2011 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2011 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2011 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2011, value1158, value1300, value1313, value461, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound33
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2144 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2144 = Sparse.eval value2144 (momentVector H) := by
  have heq : pivotMatrix2144 = (fun u v => node2144 (pivotPermutation2144 u) v) := by apply Matrix.ext; unfold pivotMatrix2144 node2144 pivotPermutation2144; decide +kernel
  have hmoment : injectiveMoment H node2144 = injectiveMoment H pivotMatrix2144 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2144 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2144 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2144 (0 : Fin 4)) =
      Sparse.eval value1064 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2144 (0 : Fin 4) = raw5077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2144 raw5077; decide +kernel
    rw [heq]
    exact (canonical5077 hH).trans (sound1064 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2144 (1 : Fin 4)) =
      Sparse.eval value1065 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2144 (1 : Fin 4) = raw4225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2144 raw4225; decide +kernel
    rw [heq]
    exact (canonical4225 hH).trans (sound1065 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2144 (2 : Fin 4)) =
      Sparse.eval value780 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2144 (2 : Fin 4) = raw4218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2144 raw4218; decide +kernel
    rw [heq]
    exact (canonical4218 hH).trans (sound780 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2144 (3 : Fin 4)) =
      Sparse.eval value1158 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2144 (3 : Fin 4) = raw4217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2144 raw4217; decide +kernel
    rw [heq]
    exact (canonical4217 hH).trans (sound1158 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2144 + (injectiveMoment H (mergeFirst pivotMatrix2144 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2144 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2144 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2144 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2144, value1064, value1065, value1158, value780, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound41
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2682 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2682 = Sparse.eval value2682 (momentVector H) := by
  have heq : pivotMatrix2682 = (fun u v => node2682 (pivotPermutation2682 u) v) := by apply Matrix.ext; unfold pivotMatrix2682 node2682 pivotPermutation2682; decide +kernel
  have hmoment : injectiveMoment H node2682 = injectiveMoment H pivotMatrix2682 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2682 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2682 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2682 (0 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2682 (0 : Fin 4) = raw7774 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2682 raw7774; decide +kernel
    rw [heq]
    exact (canonical7774 hH).trans (sound977 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2682 (1 : Fin 4)) =
      Sparse.eval value919 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2682 (1 : Fin 4) = raw7002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2682 raw7002; decide +kernel
    rw [heq]
    exact (canonical7002 hH).trans (sound919 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2682 (2 : Fin 4)) =
      Sparse.eval value781 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2682 (2 : Fin 4) = raw6990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2682 raw6990; decide +kernel
    rw [heq]
    exact (canonical6990 hH).trans (sound781 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2682 (3 : Fin 4)) =
      Sparse.eval value780 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2682 (3 : Fin 4) = raw6989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2682 raw6989; decide +kernel
    rw [heq]
    exact (canonical6989 hH).trans (sound780 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2682 + (injectiveMoment H (mergeFirst pivotMatrix2682 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2682 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2682 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2682 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2682, value780, value781, value919, value977, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound43
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2763 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2763 = Sparse.eval value2763 (momentVector H) := by
  have heq : pivotMatrix2763 = (fun u v => node2763 (pivotPermutation2763 u) v) := by apply Matrix.ext; unfold pivotMatrix2763 node2763 pivotPermutation2763; decide +kernel
  have hmoment : injectiveMoment H node2763 = injectiveMoment H pivotMatrix2763 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2763 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2763 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2763 (0 : Fin 4)) =
      Sparse.eval value1065 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2763 (0 : Fin 4) = raw6517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2763 raw6517; decide +kernel
    rw [heq]
    exact (canonical6517 hH).trans (sound1065 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2763 (1 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2763 (1 : Fin 4) = raw8370 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2763 raw8370; decide +kernel
    rw [heq]
    exact (canonical8370 hH).trans (sound1063 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2763 (2 : Fin 4)) =
      Sparse.eval value1062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2763 (2 : Fin 4) = raw8499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2763 raw8499; decide +kernel
    rw [heq]
    exact (canonical8499 hH).trans (sound1062 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2763 (3 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2763 (3 : Fin 4) = raw8502 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2763 raw8502; decide +kernel
    rw [heq]
    exact (canonical8502 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2763 + (injectiveMoment H (mergeFirst pivotMatrix2763 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2763 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2763 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2763 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2763, value1062, value1063, value1065, value188, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound50
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3218_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3218 = Sparse.eval value3218 (momentVector H) := by
  have heq : pivotMatrix3218 = (fun u v => node3218 (pivotPermutation3218 u) v) := by apply Matrix.ext; unfold pivotMatrix3218 node3218 pivotPermutation3218; decide +kernel
  have hmoment : injectiveMoment H node3218 = injectiveMoment H pivotMatrix3218 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3218 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3218 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3218 (0 : Fin 5)) =
      Sparse.eval value2324 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3218 (0 : Fin 5) = raw5076 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3218 raw5076; decide +kernel
    rw [heq]
    exact (canonical5076 hH).trans (sound2324_e hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3218 (1 : Fin 5)) =
      Sparse.eval value2763 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3218 (1 : Fin 5) = raw4224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3218 raw4224; decide +kernel
    rw [heq]
    exact (canonical4224 hH).trans (sound2763 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3218 (2 : Fin 5)) =
      Sparse.eval value2011 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3218 (2 : Fin 5) = raw4216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3218 raw4216; decide +kernel
    rw [heq]
    exact (canonical4216 hH).trans (sound2011 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3218 (3 : Fin 5)) =
      Sparse.eval value2682 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3218 (3 : Fin 5) = raw4215 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3218 raw4215; decide +kernel
    rw [heq]
    exact (canonical4215 hH).trans (sound2682 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3218 (4 : Fin 5)) =
      Sparse.eval value2144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3218 (4 : Fin 5) = raw4214 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3218 raw4214; decide +kernel
    rw [heq]
    exact (canonical4214 hH).trans (sound2144 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3218 + (injectiveMoment H (mergeFirst pivotMatrix3218 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3218 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3218 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3218 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3218 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3218, value2011, value2144, value2324, value2682, value2763, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3218_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3218_e_oai
