-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3118_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T06:15:57.188655+00:00
-- url     : https://prove2.me/submissions/ece228d5-8ca4-4574-b99e-b1b575ff4339

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound1631_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical51 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw51 = injectiveMoment H node7 := by
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

theorem canonical341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw341 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw341 = injectiveMoment H raw341step0 := by
      have heq : raw341step0 = raw341.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw341).symm
    _ = injectiveMoment H node85 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3200 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3200 = injectiveMoment H node1052 := by
  calc
    injectiveMoment H raw3200 = injectiveMoment H raw3200step0 := by
      have heq : raw3200step0 = raw3200.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3200).symm
    injectiveMoment H raw3200step0 = injectiveMoment H raw3200step1 := by
      have heq : raw3200step1 = -raw3200step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3200step0).symm
    injectiveMoment H raw3200step1 = injectiveMoment H raw3200step2 := by
      have heq : raw3200step2 = (fun i j => raw3200step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3200step1 permutation16 permutation17
    _ = injectiveMoment H node1052 := by rfl

theorem canonical3204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3204 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw3204 = injectiveMoment H raw3204step0 := by
      have heq : raw3204step0 = raw3204.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3204).symm
    injectiveMoment H raw3204step0 = injectiveMoment H raw3204step1 := by
      have heq : raw3204step1 = -raw3204step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3204step0).symm
    injectiveMoment H raw3204step1 = injectiveMoment H raw3204step2 := by
      have heq : raw3204step2 = (fun i j => raw3204step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3204step1 permutation16 permutation17
    _ = injectiveMoment H node1056 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3288 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3288 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw3288 = injectiveMoment H raw3288step0 := by
      have heq : raw3288step0 = raw3288.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3288).symm
    _ = injectiveMoment H node151 := by rfl

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

theorem canonical356 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw356 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw356 = injectiveMoment H raw356step0 := by
      have heq : raw356step0 = raw356.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw356).symm
    injectiveMoment H raw356step0 = injectiveMoment H raw356step1 := by
      have heq : raw356step1 = (fun i j => raw356step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw356step0 permutation10 permutation3
    _ = injectiveMoment H node85 := by rfl

theorem canonical357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw357 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw357 = injectiveMoment H raw357step0 := by
      have heq : raw357step0 = raw357.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw357).symm
    injectiveMoment H raw357step0 = injectiveMoment H raw357step1 := by
      have heq : raw357step1 = (fun i j => raw357step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw357step0 permutation10 permutation3
    _ = injectiveMoment H node84 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3646 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw3646 = injectiveMoment H raw3646step0 := by
      have heq : raw3646step0 = raw3646.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3646).symm
    injectiveMoment H raw3646step0 = injectiveMoment H raw3646step1 := by
      have heq : raw3646step1 = (fun i j => raw3646step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3646step0 permutation10 permutation3
    _ = injectiveMoment H node153 := by rfl

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

theorem canonical3651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3651 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw3651 = injectiveMoment H raw3651step0 := by
      have heq : raw3651step0 = raw3651.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3651).symm
    _ = injectiveMoment H node184 := by rfl

theorem canonical3652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3652 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw3652 = injectiveMoment H raw3652step0 := by
      have heq : raw3652step0 = raw3652.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3652).symm
    injectiveMoment H raw3652step0 = injectiveMoment H raw3652step1 := by
      have heq : raw3652step1 = (fun i j => raw3652step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3652step0 permutation10 permutation3
    _ = injectiveMoment H node184 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3843 = injectiveMoment H node211 := by
  calc
    injectiveMoment H raw3843 = injectiveMoment H raw3843step0 := by
      have heq : raw3843step0 = raw3843.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3843).symm
    _ = injectiveMoment H node211 := by rfl

theorem canonical3845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3845 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw3845 = injectiveMoment H raw3845step0 := by
      have heq : raw3845step0 = raw3845.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3845).symm
    _ = injectiveMoment H node212 := by rfl

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

theorem canonical4165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4165 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw4165 = injectiveMoment H raw4165step0 := by
      have heq : raw4165step0 = raw4165.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4165).symm
    injectiveMoment H raw4165step0 = injectiveMoment H raw4165step1 := by
      have heq : raw4165step1 = (fun i j => raw4165step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4165step0 permutation10 permutation3
    _ = injectiveMoment H node151 := by rfl

theorem canonical4167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4167 = injectiveMoment H node140 := by
  calc
    injectiveMoment H raw4167 = injectiveMoment H raw4167step0 := by
      have heq : raw4167step0 = raw4167.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4167).symm
    injectiveMoment H raw4167step0 = injectiveMoment H raw4167step1 := by
      have heq : raw4167step1 = (fun i j => raw4167step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4167step0 permutation13 permutation3
    _ = injectiveMoment H node140 := by rfl

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

theorem canonical4173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4173 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw4173 = injectiveMoment H raw4173step0 := by
      have heq : raw4173step0 = raw4173.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4173).symm
    injectiveMoment H raw4173step0 = injectiveMoment H raw4173step1 := by
      have heq : raw4173step1 = (fun i j => raw4173step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4173step0 permutation13 permutation3
    _ = injectiveMoment H node162 := by rfl

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

theorem canonical4194 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4194 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw4194 = injectiveMoment H raw4194step0 := by
      have heq : raw4194step0 = raw4194.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4194).symm
    injectiveMoment H raw4194step0 = injectiveMoment H raw4194step1 := by
      have heq : raw4194step1 = -raw4194step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4194step0).symm
    injectiveMoment H raw4194step1 = injectiveMoment H raw4194step2 := by
      have heq : raw4194step2 = (fun i j => raw4194step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4194step1 permutation24 permutation4
    _ = injectiveMoment H node151 := by rfl

theorem canonical4195 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4195 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw4195 = injectiveMoment H raw4195step0 := by
      have heq : raw4195step0 = raw4195.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4195).symm
    injectiveMoment H raw4195step0 = injectiveMoment H raw4195step1 := by
      have heq : raw4195step1 = -raw4195step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4195step0).symm
    injectiveMoment H raw4195step1 = injectiveMoment H raw4195step2 := by
      have heq : raw4195step2 = (fun i j => raw4195step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4195step1 permutation26 permutation4
    _ = injectiveMoment H node177 := by rfl

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

theorem canonical4242 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4242 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw4242 = injectiveMoment H raw4242step0 := by
      have heq : raw4242step0 = raw4242.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4242).symm
    injectiveMoment H raw4242step0 = injectiveMoment H raw4242step1 := by
      have heq : raw4242step1 = -raw4242step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4242step0).symm
    injectiveMoment H raw4242step1 = injectiveMoment H raw4242step2 := by
      have heq : raw4242step2 = (fun i j => raw4242step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4242step1 permutation24 permutation3
    _ = injectiveMoment H node85 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4268 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4268 = injectiveMoment H node776 := by
  calc
    injectiveMoment H raw4268 = injectiveMoment H raw4268step0 := by
      have heq : raw4268step0 = raw4268.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4268).symm
    injectiveMoment H raw4268step0 = injectiveMoment H raw4268step1 := by
      have heq : raw4268step1 = (fun i j => raw4268step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4268step0 permutation28 permutation24
    _ = injectiveMoment H node776 := by rfl

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

theorem canonical5453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5453 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw5453 = injectiveMoment H raw5453step0 := by
      have heq : raw5453step0 = raw5453.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5453).symm
    injectiveMoment H raw5453step0 = injectiveMoment H raw5453step1 := by
      have heq : raw5453step1 = (fun i j => raw5453step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5453step0 permutation13 permutation1
    _ = injectiveMoment H node45 := by rfl

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

theorem canonical5555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5555 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw5555 = injectiveMoment H raw5555step0 := by
      have heq : raw5555step0 = (fun i j => raw5555 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5555 permutation4 permutation3
    _ = injectiveMoment H node52 := by rfl

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

theorem canonical5615 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5615 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw5615 = injectiveMoment H raw5615step0 := by
      have heq : raw5615step0 = raw5615.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5615).symm
    injectiveMoment H raw5615step0 = injectiveMoment H raw5615step1 := by
      have heq : raw5615step1 = (fun i j => raw5615step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5615step0 permutation27 permutation6
    _ = injectiveMoment H node146 := by rfl

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

theorem canonical5639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5639 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw5639 = injectiveMoment H raw5639step0 := by
      have heq : raw5639step0 = raw5639.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5639).symm
    injectiveMoment H raw5639step0 = injectiveMoment H raw5639step1 := by
      have heq : raw5639step1 = (fun i j => raw5639step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5639step0 permutation28 permutation8
    _ = injectiveMoment H node145 := by rfl

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

theorem canonical6091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6091 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw6091 = injectiveMoment H raw6091step0 := by
      have heq : raw6091step0 = raw6091.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6091).symm
    injectiveMoment H raw6091step0 = injectiveMoment H raw6091step1 := by
      have heq : raw6091step1 = (fun i j => raw6091step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6091step0 permutation27 permutation6
    _ = injectiveMoment H node145 := by rfl

theorem canonical6110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6110 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw6110 = injectiveMoment H raw6110step0 := by
      have heq : raw6110step0 = raw6110.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6110).symm
    injectiveMoment H raw6110step0 = injectiveMoment H raw6110step1 := by
      have heq : raw6110step1 = (fun i j => raw6110step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6110step0 permutation27 permutation6
    _ = injectiveMoment H node150 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7021 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw7021 = injectiveMoment H raw7021step0 := by
      have hz : ∀ i, raw7021 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7021step0 = (fun i j => raw7021 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7021 permutation15 hz
    _ = injectiveMoment H node52 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical226
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7250 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7250 = injectiveMoment H node256 := by
  calc
    injectiveMoment H raw7250 = injectiveMoment H raw7250step0 := by
      have heq : raw7250step0 = raw7250.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7250).symm
    _ = injectiveMoment H node256 := by rfl

theorem canonical7254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7254 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw7254 = injectiveMoment H raw7254step0 := by
      have heq : raw7254step0 = raw7254.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7254).symm
    _ = injectiveMoment H node274 := by rfl

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

theorem canonical7457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7457 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw7457 = injectiveMoment H raw7457step0 := by
      have heq : raw7457step0 = -raw7457 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7457).symm
    injectiveMoment H raw7457step0 = injectiveMoment H raw7457step1 := by
      have heq : raw7457step1 = (fun i j => raw7457step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7457step0 permutation8 permutation4
    _ = injectiveMoment H node62 := by rfl

theorem canonical7468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7468 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw7468 = injectiveMoment H raw7468step0 := by
      have heq : raw7468step0 = raw7468.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7468).symm
    injectiveMoment H raw7468step0 = injectiveMoment H raw7468step1 := by
      have heq : raw7468step1 = (fun i j => raw7468step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7468step0 permutation10 permutation3
    _ = injectiveMoment H node274 := by rfl

theorem canonical7476 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7476 = injectiveMoment H node257 := by
  calc
    injectiveMoment H raw7476 = injectiveMoment H raw7476step0 := by
      have heq : raw7476step0 = raw7476.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7476).symm
    injectiveMoment H raw7476step0 = injectiveMoment H raw7476step1 := by
      have heq : raw7476step1 = -raw7476step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7476step0).symm
    injectiveMoment H raw7476step1 = injectiveMoment H raw7476step2 := by
      have heq : raw7476step2 = (fun i j => raw7476step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7476step1 permutation24 permutation4
    _ = injectiveMoment H node257 := by rfl

theorem canonical7477 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7477 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw7477 = injectiveMoment H raw7477step0 := by
      have heq : raw7477step0 = raw7477.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7477).symm
    injectiveMoment H raw7477step0 = injectiveMoment H raw7477step1 := by
      have heq : raw7477step1 = -raw7477step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7477step0).symm
    injectiveMoment H raw7477step1 = injectiveMoment H raw7477step2 := by
      have heq : raw7477step2 = (fun i j => raw7477step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7477step1 permutation24 permutation4
    _ = injectiveMoment H node274 := by rfl

theorem canonical7478 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7478 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw7478 = injectiveMoment H raw7478step0 := by
      have heq : raw7478step0 = raw7478.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7478).symm
    injectiveMoment H raw7478step0 = injectiveMoment H raw7478step1 := by
      have heq : raw7478step1 = (fun i j => raw7478step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7478step0 permutation13 permutation3
    _ = injectiveMoment H node288 := by rfl

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

theorem canonical7509 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7509 = injectiveMoment H node256 := by
  calc
    injectiveMoment H raw7509 = injectiveMoment H raw7509step0 := by
      have heq : raw7509step0 = raw7509.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7509).symm
    injectiveMoment H raw7509step0 = injectiveMoment H raw7509step1 := by
      have heq : raw7509step1 = -raw7509step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7509step0).symm
    injectiveMoment H raw7509step1 = injectiveMoment H raw7509step2 := by
      have heq : raw7509step2 = (fun i j => raw7509step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7509step1 permutation24 permutation4
    _ = injectiveMoment H node256 := by rfl

theorem canonical7510 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7510 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7510 = injectiveMoment H raw7510step0 := by
      have heq : raw7510step0 = raw7510.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7510).symm
    injectiveMoment H raw7510step0 = injectiveMoment H raw7510step1 := by
      have heq : raw7510step1 = -raw7510step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7510step0).symm
    injectiveMoment H raw7510step1 = injectiveMoment H raw7510step2 := by
      have heq : raw7510step2 = (fun i j => raw7510step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7510step1 permutation26 permutation4
    _ = injectiveMoment H node272 := by rfl

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

theorem canonical7535 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7535 = injectiveMoment H node152 := by
  calc
    injectiveMoment H raw7535 = injectiveMoment H raw7535step0 := by
      have heq : raw7535step0 = raw7535.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7535).symm
    injectiveMoment H raw7535step0 = injectiveMoment H raw7535step1 := by
      have heq : raw7535step1 = -raw7535step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7535step0).symm
    injectiveMoment H raw7535step1 = injectiveMoment H raw7535step2 := by
      have heq : raw7535step2 = (fun i j => raw7535step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7535step1 permutation23 permutation4
    _ = injectiveMoment H node152 := by rfl

theorem canonical7536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7536 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw7536 = injectiveMoment H raw7536step0 := by
      have heq : raw7536step0 = raw7536.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7536).symm
    injectiveMoment H raw7536step0 = injectiveMoment H raw7536step1 := by
      have heq : raw7536step1 = -raw7536step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7536step0).symm
    injectiveMoment H raw7536step1 = injectiveMoment H raw7536step2 := by
      have heq : raw7536step2 = (fun i j => raw7536step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7536step1 permutation23 permutation4
    _ = injectiveMoment H node184 := by rfl

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

theorem canonical7588 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7588 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw7588 = injectiveMoment H raw7588step0 := by
      have heq : raw7588step0 = raw7588.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7588).symm
    injectiveMoment H raw7588step0 = injectiveMoment H raw7588step1 := by
      have heq : raw7588step1 = -raw7588step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7588step0).symm
    injectiveMoment H raw7588step1 = injectiveMoment H raw7588step2 := by
      have heq : raw7588step2 = (fun i j => raw7588step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7588step1 permutation23 permutation4
    _ = injectiveMoment H node153 := by rfl

theorem canonical7589 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7589 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw7589 = injectiveMoment H raw7589step0 := by
      have heq : raw7589step0 = raw7589.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7589).symm
    injectiveMoment H raw7589step0 = injectiveMoment H raw7589step1 := by
      have heq : raw7589step1 = -raw7589step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7589step0).symm
    injectiveMoment H raw7589step1 = injectiveMoment H raw7589step2 := by
      have heq : raw7589step2 = (fun i j => raw7589step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7589step1 permutation23 permutation4
    _ = injectiveMoment H node185 := by rfl

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

theorem canonical7619 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7619 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7619 = injectiveMoment H raw7619step0 := by
      have heq : raw7619step0 = raw7619.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7619).symm
    injectiveMoment H raw7619step0 = injectiveMoment H raw7619step1 := by
      have heq : raw7619step1 = (fun i j => raw7619step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7619step0 permutation19 permutation5
    _ = injectiveMoment H node201 := by rfl

theorem canonical7621 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7621 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw7621 = injectiveMoment H raw7621step0 := by
      have heq : raw7621step0 = raw7621.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7621).symm
    injectiveMoment H raw7621step0 = injectiveMoment H raw7621step1 := by
      have heq : raw7621step1 = -raw7621step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7621step0).symm
    injectiveMoment H raw7621step1 = injectiveMoment H raw7621step2 := by
      have heq : raw7621step2 = (fun i j => raw7621step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7621step1 permutation23 permutation3
    _ = injectiveMoment H node84 := by rfl

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

theorem canonical7987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7987 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw7987 = injectiveMoment H raw7987step0 := by
      have hz : ∀ i, raw7987 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw7987step0 = (fun i j => raw7987 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7987 permutation3 hz
    _ = injectiveMoment H node9 := by rfl

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

theorem canonical8021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8021 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw8021 = injectiveMoment H raw8021step0 := by
      have hz : ∀ i, raw8021 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8021step0 = (fun i j => raw8021 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8021 permutation9 hz
    _ = injectiveMoment H node31 := by rfl

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

theorem canonical842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw842 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw842 = injectiveMoment H raw842step0 := by
      have heq : raw842step0 = raw842.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw842).symm
    injectiveMoment H raw842step0 = injectiveMoment H raw842step1 := by
      have heq : raw842step1 = (fun i j => raw842step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw842step0 permutation13 permutation1
    _ = injectiveMoment H node25 := by rfl

theorem canonical843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw843 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw843 = injectiveMoment H raw843step0 := by
      have heq : raw843step0 = raw843.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw843).symm
    injectiveMoment H raw843step0 = injectiveMoment H raw843step1 := by
      have heq : raw843step1 = (fun i j => raw843step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw843step0 permutation13 permutation1
    _ = injectiveMoment H node23 := by rfl

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

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical955 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw955 = injectiveMoment H node27 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1065 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1065 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw1065 = injectiveMoment H raw1065step0 := by
      have heq : raw1065step0 = raw1065.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1065).symm
    injectiveMoment H raw1065step0 = injectiveMoment H raw1065step1 := by
      have heq : raw1065step1 = (fun i j => raw1065step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1065step0 permutation28 permutation24
    _ = injectiveMoment H node914 := by rfl

theorem canonical1067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1067 = injectiveMoment H node772 := by
  calc
    injectiveMoment H raw1067 = injectiveMoment H raw1067step0 := by
      have heq : raw1067step0 = raw1067.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1067).symm
    injectiveMoment H raw1067step0 = injectiveMoment H raw1067step1 := by
      have heq : raw1067step1 = (fun i j => raw1067step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1067step0 permutation27 permutation18
    _ = injectiveMoment H node772 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1092 = injectiveMoment H node773 := by
  calc
    injectiveMoment H raw1092 = injectiveMoment H raw1092step0 := by
      have heq : raw1092step0 = raw1092.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1092).symm
    injectiveMoment H raw1092step0 = injectiveMoment H raw1092step1 := by
      have heq : raw1092step1 = (fun i j => raw1092step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1092step0 permutation28 permutation24
    _ = injectiveMoment H node773 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1216 = injectiveMoment H node973 := by
  calc
    injectiveMoment H raw1216 = injectiveMoment H raw1216step0 := by
      have heq : raw1216step0 = raw1216.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1216).symm
    injectiveMoment H raw1216step0 = injectiveMoment H raw1216step1 := by
      have heq : raw1216step1 = (fun i j => raw1216step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1216step0 permutation28 permutation24
    _ = injectiveMoment H node973 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical1449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1449 = injectiveMoment H node35 := by
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

theorem canonical181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw181 = injectiveMoment H node15 := by
  calc
    injectiveMoment H raw181 = injectiveMoment H raw181step0 := by
      have heq : raw181step0 = raw181.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw181).symm
    injectiveMoment H raw181step0 = injectiveMoment H raw181step1 := by
      have heq : raw181step1 = (fun i j => raw181step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw181step0 permutation13 permutation1
    _ = injectiveMoment H node15 := by rfl

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

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2950 = injectiveMoment H node1920 := by
  rfl

theorem canonical2951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2951 = injectiveMoment H node1921 := by
  rfl

theorem canonical2953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2953 = injectiveMoment H node1459 := by
  calc
    injectiveMoment H raw2953 = injectiveMoment H raw2953step0 := by
      have heq : raw2953step0 = (fun i j => raw2953 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2953 permutation41 permutation11
    _ = injectiveMoment H node1459 := by rfl

theorem canonical2975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2975 = injectiveMoment H node1930 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2979 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw2979 = injectiveMoment H raw2979step0 := by
      have heq : raw2979step0 = raw2979.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2979).symm
    injectiveMoment H raw2979step0 = injectiveMoment H raw2979step1 := by
      have heq : raw2979step1 = (fun i j => raw2979step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2979step0 permutation28 permutation24
    _ = injectiveMoment H node775 := by rfl

theorem canonical2983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2983 = injectiveMoment H node459 := by
  calc
    injectiveMoment H raw2983 = injectiveMoment H raw2983step0 := by
      have heq : raw2983step0 = raw2983.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2983).symm
    injectiveMoment H raw2983step0 = injectiveMoment H raw2983step1 := by
      have heq : raw2983step1 = (fun i j => raw2983step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2983step0 permutation27 permutation18
    _ = injectiveMoment H node459 := by rfl

theorem canonical2996 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2996 = injectiveMoment H node1051 := by
  calc
    injectiveMoment H raw2996 = injectiveMoment H raw2996step0 := by
      have heq : raw2996step0 = raw2996.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2996).symm
    injectiveMoment H raw2996step0 = injectiveMoment H raw2996step1 := by
      have heq : raw2996step1 = -raw2996step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2996step0).symm
    injectiveMoment H raw2996step1 = injectiveMoment H raw2996step2 := by
      have heq : raw2996step2 = (fun i j => raw2996step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2996step1 permutation16 permutation17
    _ = injectiveMoment H node1051 := by rfl

theorem canonical2998 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2998 = injectiveMoment H node1055 := by
  calc
    injectiveMoment H raw2998 = injectiveMoment H raw2998step0 := by
      have heq : raw2998step0 = raw2998.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2998).symm
    injectiveMoment H raw2998step0 = injectiveMoment H raw2998step1 := by
      have heq : raw2998step1 = -raw2998step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2998step0).symm
    injectiveMoment H raw2998step1 = injectiveMoment H raw2998step2 := by
      have heq : raw2998step2 = (fun i j => raw2998step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2998step1 permutation16 permutation17
    _ = injectiveMoment H node1055 := by rfl

theorem canonical3001 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3001 = injectiveMoment H node1159 := by
  calc
    injectiveMoment H raw3001 = injectiveMoment H raw3001step0 := by
      have heq : raw3001step0 = raw3001.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3001).symm
    injectiveMoment H raw3001step0 = injectiveMoment H raw3001step1 := by
      have heq : raw3001step1 = -raw3001step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3001step0).symm
    injectiveMoment H raw3001step1 = injectiveMoment H raw3001step2 := by
      have heq : raw3001step2 = (fun i j => raw3001step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3001step1 permutation16 permutation18
    _ = injectiveMoment H node1159 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3008 = injectiveMoment H node912 := by
  calc
    injectiveMoment H raw3008 = injectiveMoment H raw3008step0 := by
      have heq : raw3008step0 = raw3008.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3008).symm
    injectiveMoment H raw3008step0 = injectiveMoment H raw3008step1 := by
      have heq : raw3008step1 = (fun i j => raw3008step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3008step0 permutation28 permutation18
    _ = injectiveMoment H node912 := by rfl

theorem canonical3009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3009 = injectiveMoment H node772 := by
  calc
    injectiveMoment H raw3009 = injectiveMoment H raw3009step0 := by
      have heq : raw3009step0 = raw3009.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3009).symm
    injectiveMoment H raw3009step0 = injectiveMoment H raw3009step1 := by
      have heq : raw3009step1 = (fun i j => raw3009step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3009step0 permutation28 permutation18
    _ = injectiveMoment H node772 := by rfl

theorem canonical3019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3019 = injectiveMoment H node772 := by
  calc
    injectiveMoment H raw3019 = injectiveMoment H raw3019step0 := by
      have heq : raw3019step0 = raw3019.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3019).symm
    injectiveMoment H raw3019step0 = injectiveMoment H raw3019step1 := by
      have heq : raw3019step1 = (fun i j => raw3019step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3019step0 permutation28 permutation24
    _ = injectiveMoment H node772 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3123 = injectiveMoment H node1631 := by
  calc
    injectiveMoment H raw3123 = injectiveMoment H raw3123step0 := by
      have heq : raw3123step0 = (fun i j => raw3123 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3123 permutation41 permutation11
    _ = injectiveMoment H node1631 := by rfl

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

theorem sound7 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node7 = Sparse.eval value7 (momentVector H) := by
  have hc : momentVector H 9 = injectiveMoment H node7 := rfl
  simp [value7, Sparse.eval, hc]

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

theorem sound15 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node15 = Sparse.eval value15 (momentVector H) := by
  have heq : pivotMatrix15 = (fun u v => node15 (pivotPermutation15 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node15 = injectiveMoment H pivotMatrix15 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix15 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix15 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix15 (0 : Fin 3)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix15 (0 : Fin 3) = raw51 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical51 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix15 (1 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix15 (1 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix15 (2 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix15 (2 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node15 + (injectiveMoment H (mergeFirst pivotMatrix15 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix15 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix15 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value15, value7, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound23 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node23 = Sparse.eval value23 (momentVector H) := by
  have hc : momentVector H 68 = injectiveMoment H node23 := rfl
  simp [value23, Sparse.eval, hc]

theorem sound25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node25 = Sparse.eval value25 (momentVector H) := by
  have heq : pivotMatrix25 = (fun u v => node25 (pivotPermutation25 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node25 = injectiveMoment H pivotMatrix25 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix25 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix25 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (0 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (1 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (2 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node25 + (injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value25, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound27 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node27 = Sparse.eval value27 (momentVector H) := by
  have hc : momentVector H 69 = injectiveMoment H node27 := rfl
  simp [value27, Sparse.eval, hc]

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound45 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node45 = Sparse.eval value45 (momentVector H) := by
  have hc : momentVector H 27 = injectiveMoment H node45 := rfl
  simp [value45, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound84 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node84 = Sparse.eval value84 (momentVector H) := by
  have hc : momentVector H 259 = injectiveMoment H node84 := rfl
  simp [value84, Sparse.eval, hc]

theorem sound85 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node85 = Sparse.eval value85 (momentVector H) := by
  have hc : momentVector H 59 = injectiveMoment H node85 := rfl
  simp [value85, Sparse.eval, hc]

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

theorem sound140 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node140 = Sparse.eval value140 (momentVector H) := by
  have heq : pivotMatrix140 = (fun u v => node140 (pivotPermutation140 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node140 = injectiveMoment H pivotMatrix140 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix140 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix140 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix140 (0 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix140 (0 : Fin 3) = raw955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical955 hH).trans (sound27 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix140 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix140 (1 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix140 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix140 (2 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node140 + (injectiveMoment H (mergeFirst pivotMatrix140 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix140 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix140 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value140, value27, value31, value52, Sparse.eval] at hc ⊢
  linarith

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

theorem sound146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node146 = Sparse.eval value146 (momentVector H) := by
  have heq : pivotMatrix146 = (fun u v => node146 (pivotPermutation146 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node146 = injectiveMoment H pivotMatrix146 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix146 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix146 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix146 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix146 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix146 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix146 (1 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix146 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix146 (2 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node146 + (injectiveMoment H (mergeFirst pivotMatrix146 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix146 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix146 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value146, value31, value32, value36, Sparse.eval] at hc ⊢
  linarith

theorem sound150 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node150 = Sparse.eval value150 (momentVector H) := by
  have heq : pivotMatrix150 = (fun u v => node150 (pivotPermutation150 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node150 = injectiveMoment H pivotMatrix150 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix150 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix150 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (0 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (1 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (2 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node150 + (injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value150, value35, value52, value56, Sparse.eval] at hc ⊢
  linarith

theorem sound151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node151 = Sparse.eval value151 (momentVector H) := by
  have hc : momentVector H 10 = injectiveMoment H node151 := rfl
  simp [value151, Sparse.eval, hc]

theorem sound152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node152 = Sparse.eval value152 (momentVector H) := by
  have hc : momentVector H 308 = injectiveMoment H node152 := rfl
  simp [value152, Sparse.eval, hc]

theorem sound153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node153 = Sparse.eval value153 (momentVector H) := by
  have heq : pivotMatrix153 = (fun u v => node153 (pivotPermutation153 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node153 = injectiveMoment H pivotMatrix153 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix153 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix153 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix153 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (0 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix153 (1 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (1 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix153 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (2 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node153 + (injectiveMoment H (mergeFirst pivotMatrix153 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix153 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix153 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value153, value31, value35, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node162 = Sparse.eval value162 (momentVector H) := by
  have hc : momentVector H 124 = injectiveMoment H node162 := rfl
  simp [value162, Sparse.eval, hc]

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

theorem sound184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node184 = Sparse.eval value184 (momentVector H) := by
  have hc : momentVector H 51 = injectiveMoment H node184 := rfl
  simp [value184, Sparse.eval, hc]

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
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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

theorem sound211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node211 = Sparse.eval value211 (momentVector H) := by
  have hc : momentVector H 727 = injectiveMoment H node211 := rfl
  simp [value211, Sparse.eval, hc]

theorem sound212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node212 = Sparse.eval value212 (momentVector H) := by
  have hc : momentVector H 55 = injectiveMoment H node212 := rfl
  simp [value212, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound256 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node256 = Sparse.eval value256 (momentVector H) := by
  have heq : pivotMatrix256 = (fun u v => node256 (pivotPermutation256 u) v) := by apply Matrix.ext; unfold pivotMatrix256 node256 pivotPermutation256; decide +kernel
  have hmoment : injectiveMoment H node256 = injectiveMoment H pivotMatrix256 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix256 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix256 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix256 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix256 (0 : Fin 3) = raw7987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix256 raw7987; decide +kernel
    rw [heq]
    exact (canonical7987 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix256 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix256 (1 : Fin 3) = raw5555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix256 raw5555; decide +kernel
    rw [heq]
    exact (canonical5555 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix256 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix256 (2 : Fin 3) = raw5547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix256 raw5547; decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node256 + (injectiveMoment H (mergeFirst pivotMatrix256 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix256 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix256 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value256, value52, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound257 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node257 = Sparse.eval value257 (momentVector H) := by
  have heq : pivotMatrix257 = (fun u v => node257.transpose (pivotPermutation257 u) v) := by apply Matrix.ext; unfold pivotMatrix257 node257 pivotPermutation257; decide +kernel
  have hmoment : injectiveMoment H node257 = injectiveMoment H pivotMatrix257 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix257 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix257 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix257 (0 : Fin 2)) =
      Sparse.eval value15 (momentVector H) := by
    have heq : mergeFirst pivotMatrix257 (0 : Fin 2) = raw181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix257 raw181; decide +kernel
    rw [heq]
    exact (canonical181 hH).trans (sound15 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix257 (1 : Fin 2)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix257 (1 : Fin 2) = raw843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix257 raw843; decide +kernel
    rw [heq]
    exact (canonical843 hH).trans (sound23 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node257 + (injectiveMoment H (mergeFirst pivotMatrix257 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix257 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value257, value15, value23, Sparse.eval] at hc ⊢
  linarith

theorem sound272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node272 = Sparse.eval value272 (momentVector H) := by
  have heq : pivotMatrix272 = (fun u v => node272 (pivotPermutation272 u) v) := by apply Matrix.ext; unfold pivotMatrix272 node272 pivotPermutation272; decide +kernel
  have hmoment : injectiveMoment H node272 = injectiveMoment H pivotMatrix272 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix272 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix272 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix272 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (0 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix272 (1 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (1 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix272 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (2 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node272 + (injectiveMoment H (mergeFirst pivotMatrix272 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix272 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix272 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value272, value57, value58, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound274 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node274 = Sparse.eval value274 (momentVector H) := by
  have heq : pivotMatrix274 = (fun u v => node274.transpose (pivotPermutation274 u) v) := by apply Matrix.ext; unfold pivotMatrix274 node274 pivotPermutation274; decide +kernel
  have hmoment : injectiveMoment H node274 = injectiveMoment H pivotMatrix274 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix274 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix274 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix274 (0 : Fin 2)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix274 (0 : Fin 2) = raw842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix274 raw842; decide +kernel
    rw [heq]
    exact (canonical842 hH).trans (sound25 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix274 (1 : Fin 2)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix274 (1 : Fin 2) = raw5453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix274 raw5453; decide +kernel
    rw [heq]
    exact (canonical5453 hH).trans (sound45 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node274 + (injectiveMoment H (mergeFirst pivotMatrix274 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix274 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value274, value25, value45, Sparse.eval] at hc ⊢
  linarith

theorem sound288 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node288 = Sparse.eval value288 (momentVector H) := by
  have heq : pivotMatrix288 = (fun u v => node288 (pivotPermutation288 u) v) := by apply Matrix.ext; unfold pivotMatrix288 node288 pivotPermutation288; decide +kernel
  have hmoment : injectiveMoment H node288 = injectiveMoment H pivotMatrix288 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix288 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix288 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix288 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix288 (0 : Fin 3) = raw7457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix288 raw7457; decide +kernel
    rw [heq]
    exact (canonical7457 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix288 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix288 (1 : Fin 3) = raw6870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix288 raw6870; decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix288 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix288 (2 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix288 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node288 + (injectiveMoment H (mergeFirst pivotMatrix288 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix288 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix288 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value288, value62, value63, Sparse.eval] at hc ⊢
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

theorem sound772 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node772 = Sparse.eval value772 (momentVector H) := by
  have heq : pivotMatrix772 = (fun u v => node772.transpose (pivotPermutation772 u) v) := by apply Matrix.ext; unfold pivotMatrix772 node772 pivotPermutation772; decide +kernel
  have hmoment : injectiveMoment H node772 = injectiveMoment H pivotMatrix772 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix772 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix772 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix772 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix772 (0 : Fin 3) = raw341 := by apply Matrix.ext; unfold mergeFirst pivotMatrix772 raw341; decide +kernel
    rw [heq]
    exact (canonical341 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix772 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix772 (1 : Fin 3) = raw3646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix772 raw3646; decide +kernel
    rw [heq]
    exact (canonical3646 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix772 (2 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix772 (2 : Fin 3) = raw3652 := by apply Matrix.ext; unfold mergeFirst pivotMatrix772 raw3652; decide +kernel
    rw [heq]
    exact (canonical3652 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node772 + (injectiveMoment H (mergeFirst pivotMatrix772 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix772 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix772 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value772, value153, value184, value85, Sparse.eval] at hc ⊢
  linarith

theorem sound773 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node773 = Sparse.eval value773 (momentVector H) := by
  have heq : pivotMatrix773 = (fun u v => node773.transpose (pivotPermutation773 u) v) := by apply Matrix.ext; unfold pivotMatrix773 node773 pivotPermutation773; decide +kernel
  have hmoment : injectiveMoment H node773 = injectiveMoment H pivotMatrix773 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix773 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix773 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix773 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix773 (0 : Fin 3) = raw356 := by apply Matrix.ext; unfold mergeFirst pivotMatrix773 raw356; decide +kernel
    rw [heq]
    exact (canonical356 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix773 (1 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix773 (1 : Fin 3) = raw4165 := by apply Matrix.ext; unfold mergeFirst pivotMatrix773 raw4165; decide +kernel
    rw [heq]
    exact (canonical4165 hH).trans (sound151 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix773 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix773 (2 : Fin 3) = raw4171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix773 raw4171; decide +kernel
    rw [heq]
    exact (canonical4171 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node773 + (injectiveMoment H (mergeFirst pivotMatrix773 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix773 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix773 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value773, value151, value177, value85, Sparse.eval] at hc ⊢
  linarith

theorem sound775 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node775 = Sparse.eval value775 (momentVector H) := by
  have heq : pivotMatrix775 = (fun u v => node775 (pivotPermutation775 u) v) := by apply Matrix.ext; unfold pivotMatrix775 node775 pivotPermutation775; decide +kernel
  have hmoment : injectiveMoment H node775 = injectiveMoment H pivotMatrix775 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix775 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix775 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix775 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix775 (0 : Fin 3) = raw8021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix775 raw8021; decide +kernel
    rw [heq]
    exact (canonical8021 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix775 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix775 (1 : Fin 3) = raw5639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix775 raw5639; decide +kernel
    rw [heq]
    exact (canonical5639 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix775 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix775 (2 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix775 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node775 + (injectiveMoment H (mergeFirst pivotMatrix775 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix775 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix775 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value775, value145, value146, value31, Sparse.eval] at hc ⊢
  linarith

theorem sound776 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node776 = Sparse.eval value776 (momentVector H) := by
  have heq : pivotMatrix776 = (fun u v => node776.transpose (pivotPermutation776 u) v) := by apply Matrix.ext; unfold pivotMatrix776 node776 pivotPermutation776; decide +kernel
  have hmoment : injectiveMoment H node776 = injectiveMoment H pivotMatrix776 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix776 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix776 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix776 (0 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix776 (0 : Fin 3) = raw357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix776 raw357; decide +kernel
    rw [heq]
    exact (canonical357 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix776 (1 : Fin 3)) =
      Sparse.eval value140 (momentVector H) := by
    have heq : mergeFirst pivotMatrix776 (1 : Fin 3) = raw4167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix776 raw4167; decide +kernel
    rw [heq]
    exact (canonical4167 hH).trans (sound140 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix776 (2 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix776 (2 : Fin 3) = raw4173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix776 raw4173; decide +kernel
    rw [heq]
    exact (canonical4173 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node776 + (injectiveMoment H (mergeFirst pivotMatrix776 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix776 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix776 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value776, value140, value162, value84, Sparse.eval] at hc ⊢
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

theorem sound912 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node912 = Sparse.eval value912 (momentVector H) := by
  have heq : pivotMatrix912 = (fun u v => node912.transpose (pivotPermutation912 u) v) := by apply Matrix.ext; unfold pivotMatrix912 node912 pivotPermutation912; decide +kernel
  have hmoment : injectiveMoment H node912 = injectiveMoment H pivotMatrix912 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix912 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix912 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix912 (0 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix912 (0 : Fin 3) = raw3288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix912 raw3288; decide +kernel
    rw [heq]
    exact (canonical3288 hH).trans (sound151 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix912 (1 : Fin 3)) =
      Sparse.eval value256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix912 (1 : Fin 3) = raw7250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix912 raw7250; decide +kernel
    rw [heq]
    exact (canonical7250 hH).trans (sound256 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix912 (2 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix912 (2 : Fin 3) = raw7254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix912 raw7254; decide +kernel
    rw [heq]
    exact (canonical7254 hH).trans (sound274 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node912 + (injectiveMoment H (mergeFirst pivotMatrix912 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix912 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix912 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value912, value151, value256, value274, Sparse.eval] at hc ⊢
  linarith

theorem sound914 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node914 = Sparse.eval value914 (momentVector H) := by
  have heq : pivotMatrix914 = (fun u v => node914 (pivotPermutation914 u) v) := by apply Matrix.ext; unfold pivotMatrix914 node914 pivotPermutation914; decide +kernel
  have hmoment : injectiveMoment H node914 = injectiveMoment H pivotMatrix914 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix914 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix914 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix914 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix914 (0 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix914 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix914 (1 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix914 (1 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix914 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix914 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix914 (2 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix914 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node914 + (injectiveMoment H (mergeFirst pivotMatrix914 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix914 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix914 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value914, value145, value150, value52, Sparse.eval] at hc ⊢
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

theorem sound973 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node973 = Sparse.eval value973 (momentVector H) := by
  have heq : pivotMatrix973 = (fun u v => node973.transpose (pivotPermutation973 u) v) := by apply Matrix.ext; unfold pivotMatrix973 node973 pivotPermutation973; decide +kernel
  have hmoment : injectiveMoment H node973 = injectiveMoment H pivotMatrix973 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix973 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix973 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix973 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix973 (0 : Fin 3) = raw3651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix973 raw3651; decide +kernel
    rw [heq]
    exact (canonical3651 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix973 (1 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix973 (1 : Fin 3) = raw7468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix973 raw7468; decide +kernel
    rw [heq]
    exact (canonical7468 hH).trans (sound274 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix973 (2 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix973 (2 : Fin 3) = raw7478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix973 raw7478; decide +kernel
    rw [heq]
    exact (canonical7478 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node973 + (injectiveMoment H (mergeFirst pivotMatrix973 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix973 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix973 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value973, value184, value274, value288, Sparse.eval] at hc ⊢
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

theorem sound1051 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1051 = Sparse.eval value1051 (momentVector H) := by
  have heq : pivotMatrix1051 = (fun u v => node1051.transpose (pivotPermutation1051 u) v) := by apply Matrix.ext; unfold pivotMatrix1051 node1051 pivotPermutation1051; decide +kernel
  have hmoment : injectiveMoment H node1051 = injectiveMoment H pivotMatrix1051 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1051 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1051 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1051 (0 : Fin 3)) =
      Sparse.eval value211 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1051 (0 : Fin 3) = raw3843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1051 raw3843; decide +kernel
    rw [heq]
    exact (canonical3843 hH).trans (sound211 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1051 (1 : Fin 3)) =
      Sparse.eval value257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1051 (1 : Fin 3) = raw7476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1051 raw7476; decide +kernel
    rw [heq]
    exact (canonical7476 hH).trans (sound257 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1051 (2 : Fin 3)) =
      Sparse.eval value256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1051 (2 : Fin 3) = raw7509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1051 raw7509; decide +kernel
    rw [heq]
    exact (canonical7509 hH).trans (sound256 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1051 + (injectiveMoment H (mergeFirst pivotMatrix1051 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1051 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1051 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1051, value211, value256, value257, Sparse.eval] at hc ⊢
  linarith

theorem sound1052 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1052 = Sparse.eval value1052 (momentVector H) := by
  have heq : pivotMatrix1052 = (fun u v => node1052.transpose (pivotPermutation1052 u) v) := by apply Matrix.ext; unfold pivotMatrix1052 node1052 pivotPermutation1052; decide +kernel
  have hmoment : injectiveMoment H node1052 = injectiveMoment H pivotMatrix1052 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1052 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1052 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1052 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1052 (0 : Fin 3) = raw3845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1052 raw3845; decide +kernel
    rw [heq]
    exact (canonical3845 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1052 (1 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1052 (1 : Fin 3) = raw7477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1052 raw7477; decide +kernel
    rw [heq]
    exact (canonical7477 hH).trans (sound274 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1052 (2 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1052 (2 : Fin 3) = raw7510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1052 raw7510; decide +kernel
    rw [heq]
    exact (canonical7510 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1052 + (injectiveMoment H (mergeFirst pivotMatrix1052 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1052 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1052 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1052, value212, value272, value274, Sparse.eval] at hc ⊢
  linarith

theorem sound1055 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1055 = Sparse.eval value1055 (momentVector H) := by
  have heq : pivotMatrix1055 = (fun u v => node1055.transpose (pivotPermutation1055 u) v) := by apply Matrix.ext; unfold pivotMatrix1055 node1055 pivotPermutation1055; decide +kernel
  have hmoment : injectiveMoment H node1055 = injectiveMoment H pivotMatrix1055 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1055 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1055 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1055 (0 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1055 (0 : Fin 3) = raw4194 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1055 raw4194; decide +kernel
    rw [heq]
    exact (canonical4194 hH).trans (sound151 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1055 (1 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1055 (1 : Fin 3) = raw7535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1055 raw7535; decide +kernel
    rw [heq]
    exact (canonical7535 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1055 (2 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1055 (2 : Fin 3) = raw7588 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1055 raw7588; decide +kernel
    rw [heq]
    exact (canonical7588 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1055 + (injectiveMoment H (mergeFirst pivotMatrix1055 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1055 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1055 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1055, value151, value152, value153, Sparse.eval] at hc ⊢
  linarith

theorem sound1056 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1056 = Sparse.eval value1056 (momentVector H) := by
  have heq : pivotMatrix1056 = (fun u v => node1056.transpose (pivotPermutation1056 u) v) := by apply Matrix.ext; unfold pivotMatrix1056 node1056 pivotPermutation1056; decide +kernel
  have hmoment : injectiveMoment H node1056 = injectiveMoment H pivotMatrix1056 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1056 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1056 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1056 (0 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1056 (0 : Fin 3) = raw4195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1056 raw4195; decide +kernel
    rw [heq]
    exact (canonical4195 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1056 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1056 (1 : Fin 3) = raw7536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1056 raw7536; decide +kernel
    rw [heq]
    exact (canonical7536 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1056 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1056 (2 : Fin 3) = raw7589 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1056 raw7589; decide +kernel
    rw [heq]
    exact (canonical7589 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1056 + (injectiveMoment H (mergeFirst pivotMatrix1056 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1056 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1056 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1056, value177, value184, value185, Sparse.eval] at hc ⊢
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

theorem sound1159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1159 = Sparse.eval value1159 (momentVector H) := by
  have heq : pivotMatrix1159 = (fun u v => node1159.transpose (pivotPermutation1159 u) v) := by apply Matrix.ext; unfold pivotMatrix1159 node1159 pivotPermutation1159; decide +kernel
  have hmoment : injectiveMoment H node1159 = injectiveMoment H pivotMatrix1159 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1159 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1159 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1159 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1159 (0 : Fin 3) = raw4242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1159 raw4242; decide +kernel
    rw [heq]
    exact (canonical4242 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1159 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1159 (1 : Fin 3) = raw7619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1159 raw7619; decide +kernel
    rw [heq]
    exact (canonical7619 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1159 (2 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1159 (2 : Fin 3) = raw7621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1159 raw7621; decide +kernel
    rw [heq]
    exact (canonical7621 hH).trans (sound84 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1159 + (injectiveMoment H (mergeFirst pivotMatrix1159 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1159 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1159 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1159, value201, value84, value85, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound22
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1459 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1459 = Sparse.eval value1459 (momentVector H) := by
  have heq : pivotMatrix1459 = (fun u v => node1459 (pivotPermutation1459 u) v) := by apply Matrix.ext; unfold pivotMatrix1459 node1459 pivotPermutation1459; decide +kernel
  have hmoment : injectiveMoment H node1459 = injectiveMoment H pivotMatrix1459 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1459 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1459 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1459 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1459 (0 : Fin 4) = raw1216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1459 raw1216; decide +kernel
    rw [heq]
    exact (canonical1216 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1459 (1 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1459 (1 : Fin 4) = raw1092 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1459 raw1092; decide +kernel
    rw [heq]
    exact (canonical1092 hH).trans (sound773 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1459 (2 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1459 (2 : Fin 4) = raw1067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1459 raw1067; decide +kernel
    rw [heq]
    exact (canonical1067 hH).trans (sound772 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1459 (3 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1459 (3 : Fin 4) = raw1065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1459 raw1065; decide +kernel
    rw [heq]
    exact (canonical1065 hH).trans (sound914 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1459 + (injectiveMoment H (mergeFirst pivotMatrix1459 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1459 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1459 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1459 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1459, value772, value773, value914, value973, Sparse.eval] at hc ⊢
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

theorem sound459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node459 = Sparse.eval value459 (momentVector H) := by
  have hc : momentVector H 321 = injectiveMoment H node459 := rfl
  simp [value459, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound30
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1920 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1920 = Sparse.eval value1920 (momentVector H) := by
  have heq : pivotMatrix1920 = (fun u v => node1920 (pivotPermutation1920 u) v) := by apply Matrix.ext; unfold pivotMatrix1920 node1920 pivotPermutation1920; decide +kernel
  have hmoment : injectiveMoment H node1920 = injectiveMoment H pivotMatrix1920 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1920 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1920 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1920 (0 : Fin 4)) =
      Sparse.eval value1052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1920 (0 : Fin 4) = raw3200 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1920 raw3200; decide +kernel
    rw [heq]
    exact (canonical3200 hH).trans (sound1052 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1920 (1 : Fin 4)) =
      Sparse.eval value912 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1920 (1 : Fin 4) = raw3008 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1920 raw3008; decide +kernel
    rw [heq]
    exact (canonical3008 hH).trans (sound912 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1920 (2 : Fin 4)) =
      Sparse.eval value1055 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1920 (2 : Fin 4) = raw2998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1920 raw2998; decide +kernel
    rw [heq]
    exact (canonical2998 hH).trans (sound1055 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1920 (3 : Fin 4)) =
      Sparse.eval value1051 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1920 (3 : Fin 4) = raw2996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1920 raw2996; decide +kernel
    rw [heq]
    exact (canonical2996 hH).trans (sound1051 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1920 + (injectiveMoment H (mergeFirst pivotMatrix1920 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1920 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1920 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1920 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1920, value1051, value1052, value1055, value912, Sparse.eval] at hc ⊢
  linarith

theorem sound1921 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1921 = Sparse.eval value1921 (momentVector H) := by
  have heq : pivotMatrix1921 = (fun u v => node1921 (pivotPermutation1921 u) v) := by apply Matrix.ext; unfold pivotMatrix1921 node1921 pivotPermutation1921; decide +kernel
  have hmoment : injectiveMoment H node1921 = injectiveMoment H pivotMatrix1921 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1921 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1921 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1921 (0 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1921 (0 : Fin 4) = raw3204 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1921 raw3204; decide +kernel
    rw [heq]
    exact (canonical3204 hH).trans (sound1056 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1921 (1 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1921 (1 : Fin 4) = raw3009 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1921 raw3009; decide +kernel
    rw [heq]
    exact (canonical3009 hH).trans (sound772 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1921 (2 : Fin 4)) =
      Sparse.eval value1159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1921 (2 : Fin 4) = raw3001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1921 raw3001; decide +kernel
    rw [heq]
    exact (canonical3001 hH).trans (sound1159 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1921 (3 : Fin 4)) =
      Sparse.eval value1055 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1921 (3 : Fin 4) = raw2998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1921 raw2998; decide +kernel
    rw [heq]
    exact (canonical2998 hH).trans (sound1055 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1921 + (injectiveMoment H (mergeFirst pivotMatrix1921 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1921 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1921 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1921 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1921, value1055, value1056, value1159, value772, Sparse.eval] at hc ⊢
  linarith

theorem sound1930 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1930 = Sparse.eval value1930 (momentVector H) := by
  have heq : pivotMatrix1930 = (fun u v => node1930 (pivotPermutation1930 u) v) := by apply Matrix.ext; unfold pivotMatrix1930 node1930 pivotPermutation1930; decide +kernel
  have hmoment : injectiveMoment H node1930 = injectiveMoment H pivotMatrix1930 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1930 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1930 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1930 (0 : Fin 4)) =
      Sparse.eval value776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1930 (0 : Fin 4) = raw4268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1930 raw4268; decide +kernel
    rw [heq]
    exact (canonical4268 hH).trans (sound776 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1930 (1 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1930 (1 : Fin 4) = raw3019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1930 raw3019; decide +kernel
    rw [heq]
    exact (canonical3019 hH).trans (sound772 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1930 (2 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1930 (2 : Fin 4) = raw2983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1930 raw2983; decide +kernel
    rw [heq]
    exact (canonical2983 hH).trans (sound459 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1930 (3 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1930 (3 : Fin 4) = raw2979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1930 raw2979; decide +kernel
    rw [heq]
    exact (canonical2979 hH).trans (sound775 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1930 + (injectiveMoment H (mergeFirst pivotMatrix1930 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1930 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1930 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1930 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1930, value459, value772, value775, value776, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound48
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3118_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3118 = Sparse.eval value3118 (momentVector H) := by
  have heq : pivotMatrix3118 = (fun u v => node3118 (pivotPermutation3118 u) v) := by apply Matrix.ext; unfold pivotMatrix3118 node3118 pivotPermutation3118; decide +kernel
  have hmoment : injectiveMoment H node3118 = injectiveMoment H pivotMatrix3118 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3118 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3118 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3118 (0 : Fin 5)) =
      Sparse.eval value1631 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3118 (0 : Fin 5) = raw3123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3118 raw3123; decide +kernel
    rw [heq]
    exact (canonical3123 hH).trans (sound1631_e hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3118 (1 : Fin 5)) =
      Sparse.eval value1930 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3118 (1 : Fin 5) = raw2975 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3118 raw2975; decide +kernel
    rw [heq]
    exact (canonical2975 hH).trans (sound1930 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3118 (2 : Fin 5)) =
      Sparse.eval value1459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3118 (2 : Fin 5) = raw2953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3118 raw2953; decide +kernel
    rw [heq]
    exact (canonical2953 hH).trans (sound1459 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3118 (3 : Fin 5)) =
      Sparse.eval value1921 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3118 (3 : Fin 5) = raw2951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3118 raw2951; decide +kernel
    rw [heq]
    exact (canonical2951 hH).trans (sound1921 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3118 (4 : Fin 5)) =
      Sparse.eval value1920 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3118 (4 : Fin 5) = raw2950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3118 raw2950; decide +kernel
    rw [heq]
    exact (canonical2950 hH).trans (sound1920 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3118 + (injectiveMoment H (mergeFirst pivotMatrix3118 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3118 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3118 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3118 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3118 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3118, value1459, value1631, value1920, value1921, value1930, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3118_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3118_e_oai
