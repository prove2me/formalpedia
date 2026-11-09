-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3119_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T06:09:33.120207+00:00
-- url     : https://prove2.me/submissions/dba2bfe6-ba7d-4654-b40c-037c25f167ab

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

theorem canonical341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw341 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw341 = injectiveMoment H raw341step0 := by
      have heq : raw341step0 = raw341.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw341).symm
    _ = injectiveMoment H node85 := by rfl

theorem canonical346 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw346 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw346 = injectiveMoment H raw346step0 := by
      have heq : raw346step0 = raw346.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw346).symm
    injectiveMoment H raw346step0 = injectiveMoment H raw346step1 := by
      have heq : raw346step1 = -raw346step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw346step0).symm
    injectiveMoment H raw346step1 = injectiveMoment H raw346step2 := by
      have heq : raw346step2 = (fun i j => raw346step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw346step1 permutation19 permutation5
    _ = injectiveMoment H node198 := by rfl

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

theorem canonical3208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3208 = injectiveMoment H node1269 := by
  calc
    injectiveMoment H raw3208 = injectiveMoment H raw3208step0 := by
      have heq : raw3208step0 = raw3208.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3208).symm
    injectiveMoment H raw3208step0 = injectiveMoment H raw3208step1 := by
      have heq : raw3208step1 = (fun i j => raw3208step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3208step0 permutation25 permutation19
    _ = injectiveMoment H node1269 := by rfl

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

theorem canonical3847 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3847 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw3847 = injectiveMoment H raw3847step0 := by
      have heq : raw3847step0 = raw3847.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3847).symm
    injectiveMoment H raw3847step0 = injectiveMoment H raw3847step1 := by
      have heq : raw3847step1 = -raw3847step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3847step0).symm
    injectiveMoment H raw3847step1 = injectiveMoment H raw3847step2 := by
      have heq : raw3847step2 = (fun i j => raw3847step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3847step1 permutation19 permutation5
    _ = injectiveMoment H node203 := by rfl

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

theorem canonical4151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4151 = injectiveMoment H node33 := by
  calc
    injectiveMoment H raw4151 = injectiveMoment H raw4151step0 := by
      have heq : raw4151step0 = -raw4151 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4151).symm
    injectiveMoment H raw4151step0 = injectiveMoment H raw4151step1 := by
      have heq : raw4151step1 = (fun i j => raw4151step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4151step0 permutation8 permutation4
    _ = injectiveMoment H node33 := by rfl

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

theorem canonical4162 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4162 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4162 = injectiveMoment H raw4162step0 := by
      have heq : raw4162step0 = raw4162.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4162).symm
    injectiveMoment H raw4162step0 = injectiveMoment H raw4162step1 := by
      have heq : raw4162step1 = -raw4162step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4162step0).symm
    injectiveMoment H raw4162step1 = injectiveMoment H raw4162step2 := by
      have heq : raw4162step2 = (fun i j => raw4162step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4162step1 permutation8 permutation4
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

theorem canonical4270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4270 = injectiveMoment H node394 := by
  calc
    injectiveMoment H raw4270 = injectiveMoment H raw4270step0 := by
      have heq : raw4270step0 = raw4270.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4270).symm
    injectiveMoment H raw4270step0 = injectiveMoment H raw4270step1 := by
      have heq : raw4270step1 = (fun i j => raw4270step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4270step0 permutation27 permutation18
    _ = injectiveMoment H node394 := by rfl

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

theorem canonical5547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5547 = injectiveMoment H node52 := by
  rfl

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

theorem canonical5631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5631 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw5631 = injectiveMoment H raw5631step0 := by
      have heq : raw5631step0 = raw5631.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5631).symm
    injectiveMoment H raw5631step0 = injectiveMoment H raw5631step1 := by
      have heq : raw5631step1 = (fun i j => raw5631step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5631step0 permutation28 permutation6
    _ = injectiveMoment H node150 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5695 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw5695 = injectiveMoment H raw5695step0 := by
      have heq : raw5695step0 = raw5695.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5695).symm
    injectiveMoment H raw5695step0 = injectiveMoment H raw5695step1 := by
      have heq : raw5695step1 = (fun i j => raw5695step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5695step0 permutation27 permutation6
    _ = injectiveMoment H node177 := by rfl

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

theorem canonical5718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5718 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw5718 = injectiveMoment H raw5718step0 := by
      have heq : raw5718step0 = raw5718.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5718).symm
    injectiveMoment H raw5718step0 = injectiveMoment H raw5718step1 := by
      have heq : raw5718step1 = (fun i j => raw5718step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5718step0 permutation28 permutation6
    _ = injectiveMoment H node181 := by rfl

theorem canonical5724 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5724 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw5724 = injectiveMoment H raw5724step0 := by
      have heq : raw5724step0 = raw5724.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5724).symm
    injectiveMoment H raw5724step0 = injectiveMoment H raw5724step1 := by
      have heq : raw5724step1 = (fun i j => raw5724step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5724step0 permutation22 permutation5
    _ = injectiveMoment H node204 := by rfl

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

theorem canonical5730 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5730 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw5730 = injectiveMoment H raw5730step0 := by
      have heq : raw5730step0 = raw5730.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5730).symm
    injectiveMoment H raw5730step0 = injectiveMoment H raw5730step1 := by
      have heq : raw5730step1 = (fun i j => raw5730step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5730step0 permutation22 permutation7
    _ = injectiveMoment H node204 := by rfl

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

theorem canonical5809 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5809 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw5809 = injectiveMoment H raw5809step0 := by
      have heq : raw5809step0 = raw5809.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5809).symm
    injectiveMoment H raw5809step0 = injectiveMoment H raw5809step1 := by
      have heq : raw5809step1 = (fun i j => raw5809step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5809step0 permutation12 permutation5
    _ = injectiveMoment H node85 := by rfl

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

theorem canonical6875 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6875 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw6875 = injectiveMoment H raw6875step0 := by
      have heq : raw6875step0 = -raw6875 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6875).symm
    injectiveMoment H raw6875step0 = injectiveMoment H raw6875step1 := by
      have heq : raw6875step1 = (fun i j => raw6875step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6875step0 permutation8 permutation4
    _ = injectiveMoment H node59 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7519 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7519 = injectiveMoment H raw7519step0 := by
      have heq : raw7519step0 = raw7519.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7519).symm
    injectiveMoment H raw7519step0 = injectiveMoment H raw7519step1 := by
      have heq : raw7519step1 = -raw7519step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7519step0).symm
    injectiveMoment H raw7519step1 = injectiveMoment H raw7519step2 := by
      have heq : raw7519step2 = (fun i j => raw7519step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7519step1 permutation24 permutation3
    _ = injectiveMoment H node201 := by rfl

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

theorem canonical7526 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7526 = injectiveMoment H node217 := by
  calc
    injectiveMoment H raw7526 = injectiveMoment H raw7526step0 := by
      have heq : raw7526step0 = raw7526.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7526).symm
    injectiveMoment H raw7526step0 = injectiveMoment H raw7526step1 := by
      have heq : raw7526step1 = -raw7526step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7526step0).symm
    injectiveMoment H raw7526step1 = injectiveMoment H raw7526step2 := by
      have heq : raw7526step2 = (fun i j => raw7526step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7526step1 permutation23 permutation4
    _ = injectiveMoment H node217 := by rfl

theorem canonical7533 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7533 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw7533 = injectiveMoment H raw7533step0 := by
      have heq : raw7533step0 = raw7533.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7533).symm
    injectiveMoment H raw7533step0 = injectiveMoment H raw7533step1 := by
      have heq : raw7533step1 = -raw7533step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7533step0).symm
    injectiveMoment H raw7533step1 = injectiveMoment H raw7533step2 := by
      have heq : raw7533step2 = (fun i j => raw7533step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7533step1 permutation24 permutation3
    _ = injectiveMoment H node153 := by rfl

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

theorem canonical7542 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7542 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw7542 = injectiveMoment H raw7542step0 := by
      have heq : raw7542step0 = raw7542.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7542).symm
    injectiveMoment H raw7542step0 = injectiveMoment H raw7542step1 := by
      have heq : raw7542step1 = -raw7542step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7542step0).symm
    injectiveMoment H raw7542step1 = injectiveMoment H raw7542step2 := by
      have heq : raw7542step2 = (fun i j => raw7542step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7542step1 permutation23 permutation4
    _ = injectiveMoment H node215 := by rfl

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

theorem canonical8093 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8093 = injectiveMoment H node41 := by
  calc
    injectiveMoment H raw8093 = injectiveMoment H raw8093step0 := by
      have hz : ∀ i, raw8093 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8093step0 = (fun i j => raw8093 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8093 permutation9 hz
    _ = injectiveMoment H node41 := by rfl

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

theorem canonical8223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8223 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw8223 = injectiveMoment H raw8223step0 := by
      have heq : raw8223step0 = raw8223.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8223).symm
    injectiveMoment H raw8223step0 = injectiveMoment H raw8223step1 := by
      have heq : raw8223step1 = (fun i j => raw8223step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8223step0 permutation19 permutation4
    _ = injectiveMoment H node199 := by rfl

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

theorem canonical8228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8228 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw8228 = injectiveMoment H raw8228step0 := by
      have heq : raw8228step0 = raw8228.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8228).symm
    injectiveMoment H raw8228step0 = injectiveMoment H raw8228step1 := by
      have heq : raw8228step1 = (fun i j => raw8228step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8228step0 permutation19 permutation4
    _ = injectiveMoment H node204 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9953 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw9953 = injectiveMoment H raw9953step0 := by
      have heq : raw9953step0 = raw9953.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9953).symm
    injectiveMoment H raw9953step0 = injectiveMoment H raw9953step1 := by
      have heq : raw9953step1 = (fun i j => raw9953step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9953step0 permutation29 permutation4
    _ = injectiveMoment H node199 := by rfl

theorem canonical9957 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9957 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw9957 = injectiveMoment H raw9957step0 := by
      have heq : raw9957step0 = raw9957.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9957).symm
    injectiveMoment H raw9957step0 = injectiveMoment H raw9957step1 := by
      have heq : raw9957step1 = -raw9957step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9957step0).symm
    injectiveMoment H raw9957step1 = injectiveMoment H raw9957step2 := by
      have heq : raw9957step2 = (fun i j => raw9957step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9957step1 permutation23 permutation3
    _ = injectiveMoment H node198 := by rfl

theorem canonical9960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9960 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw9960 = injectiveMoment H raw9960step0 := by
      have heq : raw9960step0 = raw9960.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9960).symm
    injectiveMoment H raw9960step0 = injectiveMoment H raw9960step1 := by
      have heq : raw9960step1 = -raw9960step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9960step0).symm
    injectiveMoment H raw9960step1 = injectiveMoment H raw9960step2 := by
      have heq : raw9960step2 = (fun i j => raw9960step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9960step1 permutation21 permutation4
    _ = injectiveMoment H node193 := by rfl

theorem canonical9964 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9964 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw9964 = injectiveMoment H raw9964step0 := by
      have heq : raw9964step0 = raw9964.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9964).symm
    injectiveMoment H raw9964step0 = injectiveMoment H raw9964step1 := by
      have heq : raw9964step1 = -raw9964step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9964step0).symm
    injectiveMoment H raw9964step1 = injectiveMoment H raw9964step2 := by
      have heq : raw9964step2 = (fun i j => raw9964step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9964step1 permutation21 permutation3
    _ = injectiveMoment H node151 := by rfl

theorem canonical9968 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9968 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw9968 = injectiveMoment H raw9968step0 := by
      have heq : raw9968step0 = raw9968.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9968).symm
    injectiveMoment H raw9968step0 = injectiveMoment H raw9968step1 := by
      have heq : raw9968step1 = -raw9968step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9968step0).symm
    injectiveMoment H raw9968step1 = injectiveMoment H raw9968step2 := by
      have heq : raw9968step2 = (fun i j => raw9968step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9968step1 permutation21 permutation4
    _ = injectiveMoment H node198 := by rfl

theorem canonical9972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9972 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw9972 = injectiveMoment H raw9972step0 := by
      have heq : raw9972step0 = raw9972.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9972).symm
    injectiveMoment H raw9972step0 = injectiveMoment H raw9972step1 := by
      have heq : raw9972step1 = (fun i j => raw9972step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9972step0 permutation27 permutation3
    _ = injectiveMoment H node199 := by rfl

theorem canonical9976 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9976 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw9976 = injectiveMoment H raw9976step0 := by
      have heq : raw9976step0 = raw9976.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9976).symm
    injectiveMoment H raw9976step0 = injectiveMoment H raw9976step1 := by
      have heq : raw9976step1 = -raw9976step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9976step0).symm
    injectiveMoment H raw9976step1 = injectiveMoment H raw9976step2 := by
      have heq : raw9976step2 = (fun i j => raw9976step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9976step1 permutation21 permutation3
    _ = injectiveMoment H node146 := by rfl

theorem canonical9980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9980 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw9980 = injectiveMoment H raw9980step0 := by
      have heq : raw9980step0 = raw9980.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9980).symm
    injectiveMoment H raw9980step0 = injectiveMoment H raw9980step1 := by
      have heq : raw9980step1 = (fun i j => raw9980step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9980step0 permutation27 permutation3
    _ = injectiveMoment H node204 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1139 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw1139 = injectiveMoment H raw1139step0 := by
      have heq : raw1139step0 = raw1139.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1139).symm
    injectiveMoment H raw1139step0 = injectiveMoment H raw1139step1 := by
      have heq : raw1139step1 = (fun i j => raw1139step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1139step0 permutation28 permutation18
    _ = injectiveMoment H node771 := by rfl

theorem canonical1141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1141 = injectiveMoment H node1164 := by
  calc
    injectiveMoment H raw1141 = injectiveMoment H raw1141step0 := by
      have heq : raw1141step0 = raw1141.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1141).symm
    injectiveMoment H raw1141step0 = injectiveMoment H raw1141step1 := by
      have heq : raw1141step1 = (fun i j => raw1141step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1141step0 permutation31 permutation20
    _ = injectiveMoment H node1164 := by rfl

theorem canonical1150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1150 = injectiveMoment H node397 := by
  calc
    injectiveMoment H raw1150 = injectiveMoment H raw1150step0 := by
      have heq : raw1150step0 = raw1150.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1150).symm
    injectiveMoment H raw1150step0 = injectiveMoment H raw1150step1 := by
      have heq : raw1150step1 = (fun i j => raw1150step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1150step0 permutation28 permutation18
    _ = injectiveMoment H node397 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1259 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1259 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw1259 = injectiveMoment H raw1259step0 := by
      have heq : raw1259step0 = raw1259.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1259).symm
    injectiveMoment H raw1259step0 = injectiveMoment H raw1259step1 := by
      have heq : raw1259step1 = (fun i j => raw1259step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1259step0 permutation28 permutation18
    _ = injectiveMoment H node804 := by rfl

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

theorem canonical1916 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1916 = injectiveMoment H node802 := by
  calc
    injectiveMoment H raw1916 = injectiveMoment H raw1916step0 := by
      have heq : raw1916step0 = (fun i j => raw1916 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1916 permutation10 permutation15
    _ = injectiveMoment H node802 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2053 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2053 = injectiveMoment H node806 := by
  calc
    injectiveMoment H raw2053 = injectiveMoment H raw2053step0 := by
      have heq : raw2053step0 = (fun i j => raw2053 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2053 permutation12 permutation15
    _ = injectiveMoment H node806 := by rfl

theorem canonical2063 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2063 = injectiveMoment H node805 := by
  calc
    injectiveMoment H raw2063 = injectiveMoment H raw2063step0 := by
      have heq : raw2063step0 = raw2063.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2063).symm
    injectiveMoment H raw2063step0 = injectiveMoment H raw2063step1 := by
      have heq : raw2063step1 = (fun i j => raw2063step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2063step0 permutation28 permutation18
    _ = injectiveMoment H node805 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2951 = injectiveMoment H node1921 := by
  rfl

theorem canonical2952 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2952 = injectiveMoment H node1922 := by
  rfl

theorem canonical2954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2954 = injectiveMoment H node1471 := by
  calc
    injectiveMoment H raw2954 = injectiveMoment H raw2954step0 := by
      have heq : raw2954step0 = (fun i j => raw2954 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2954 permutation39 permutation11
    _ = injectiveMoment H node1471 := by rfl

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

theorem canonical2976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2976 = injectiveMoment H node1931 := by
  rfl

theorem canonical2980 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2980 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw2980 = injectiveMoment H raw2980step0 := by
      have heq : raw2980step0 = -raw2980 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2980).symm
    injectiveMoment H raw2980step0 = injectiveMoment H raw2980step1 := by
      have heq : raw2980step1 = (fun i j => raw2980step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2980step0 permutation23 permutation15
    _ = injectiveMoment H node1257 := by rfl

theorem canonical2985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2985 = injectiveMoment H node395 := by
  calc
    injectiveMoment H raw2985 = injectiveMoment H raw2985step0 := by
      have heq : raw2985step0 = (fun i j => raw2985 (permutation12 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2985 permutation12 permutation21
    _ = injectiveMoment H node395 := by rfl

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

theorem canonical3003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3003 = injectiveMoment H node1229 := by
  calc
    injectiveMoment H raw3003 = injectiveMoment H raw3003step0 := by
      have heq : raw3003step0 = raw3003.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3003).symm
    injectiveMoment H raw3003step0 = injectiveMoment H raw3003step1 := by
      have heq : raw3003step1 = (fun i j => raw3003step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3003step0 permutation25 permutation19
    _ = injectiveMoment H node1229 := by rfl

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

theorem canonical3011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3011 = injectiveMoment H node1180 := by
  calc
    injectiveMoment H raw3011 = injectiveMoment H raw3011step0 := by
      have heq : raw3011step0 = raw3011.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3011).symm
    injectiveMoment H raw3011step0 = injectiveMoment H raw3011step1 := by
      have heq : raw3011step1 = (fun i j => raw3011step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3011step0 permutation31 permutation20
    _ = injectiveMoment H node1180 := by rfl

theorem canonical3021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3021 = injectiveMoment H node397 := by
  calc
    injectiveMoment H raw3021 = injectiveMoment H raw3021step0 := by
      have heq : raw3021step0 = raw3021.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3021).symm
    injectiveMoment H raw3021step0 = injectiveMoment H raw3021step1 := by
      have heq : raw3021step1 = (fun i j => raw3021step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3021step0 permutation27 permutation18
    _ = injectiveMoment H node397 := by rfl

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

theorem canonical3124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3124 = injectiveMoment H node1638 := by
  calc
    injectiveMoment H raw3124 = injectiveMoment H raw3124step0 := by
      have heq : raw3124step0 = (fun i j => raw3124 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3124 permutation39 permutation11
    _ = injectiveMoment H node1638 := by rfl

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

theorem sound193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node193 = Sparse.eval value193 (momentVector H) := by
  have hc : momentVector H 723 = injectiveMoment H node193 := rfl
  simp [value193, Sparse.eval, hc]

theorem sound198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node198 = Sparse.eval value198 (momentVector H) := by
  have hc : momentVector H 54 = injectiveMoment H node198 := rfl
  simp [value198, Sparse.eval, hc]

theorem sound199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node199 = Sparse.eval value199 (momentVector H) := by
  have hc : momentVector H 199 = injectiveMoment H node199 := rfl
  simp [value199, Sparse.eval, hc]

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

theorem sound204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node204 = Sparse.eval value204 (momentVector H) := by
  have heq : pivotMatrix204 = (fun u v => node204 (pivotPermutation204 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node204 = injectiveMoment H pivotMatrix204 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix204 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix204 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix204 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (0 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix204 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix204 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (2 : Fin 3) = raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4147 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node204 + (injectiveMoment H (mergeFirst pivotMatrix204 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix204 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix204 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value204, value37, value41, Sparse.eval] at hc ⊢
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

theorem sound217 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node217 = Sparse.eval value217 (momentVector H) := by
  have heq : pivotMatrix217 = (fun u v => node217 (pivotPermutation217 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node217 = injectiveMoment H pivotMatrix217 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix217 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix217 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix217 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix217 (0 : Fin 3) = raw6875 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6875 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix217 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix217 (1 : Fin 3) = raw4162 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4162 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix217 (2 : Fin 3)) =
      Sparse.eval value33 (momentVector H) := by
    have heq : mergeFirst pivotMatrix217 (2 : Fin 3) = raw4151 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4151 hH).trans (sound33 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node217 + (injectiveMoment H (mergeFirst pivotMatrix217 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix217 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix217 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value217, value32, value33, value59, Sparse.eval] at hc ⊢
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

theorem sound771 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node771 = Sparse.eval value771 (momentVector H) := by
  have heq : pivotMatrix771 = (fun u v => node771 (pivotPermutation771 u) v) := by apply Matrix.ext; unfold pivotMatrix771 node771 pivotPermutation771; decide +kernel
  have hmoment : injectiveMoment H node771 = injectiveMoment H pivotMatrix771 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix771 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix771 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix771 (0 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix771 (0 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix771 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix771 (1 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix771 (1 : Fin 3) = raw5631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix771 raw5631; decide +kernel
    rw [heq]
    exact (canonical5631 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix771 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix771 (2 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix771 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node771 + (injectiveMoment H (mergeFirst pivotMatrix771 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix771 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix771 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value771, value145, value146, value150, Sparse.eval] at hc ⊢
  linarith

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

theorem sound802 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node802 = Sparse.eval value802 (momentVector H) := by
  have heq : pivotMatrix802 = (fun u v => node802 (pivotPermutation802 u) v) := by apply Matrix.ext; unfold pivotMatrix802 node802 pivotPermutation802; decide +kernel
  have hmoment : injectiveMoment H node802 = injectiveMoment H pivotMatrix802 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix802 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix802 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix802 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix802 (0 : Fin 3) = raw5797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix802 raw5797; decide +kernel
    rw [heq]
    exact (canonical5797 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix802 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix802 (1 : Fin 3) = raw5725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix802 raw5725; decide +kernel
    rw [heq]
    exact (canonical5725 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix802 (2 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix802 (2 : Fin 3) = raw5724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix802 raw5724; decide +kernel
    rw [heq]
    exact (canonical5724 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node802 + (injectiveMoment H (mergeFirst pivotMatrix802 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix802 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix802 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value802, value185, value203, value204, Sparse.eval] at hc ⊢
  linarith

theorem sound804 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node804 = Sparse.eval value804 (momentVector H) := by
  have heq : pivotMatrix804 = (fun u v => node804.transpose (pivotPermutation804 u) v) := by apply Matrix.ext; unfold pivotMatrix804 node804 pivotPermutation804; decide +kernel
  have hmoment : injectiveMoment H node804 = injectiveMoment H pivotMatrix804 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix804 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix804 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix804 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix804 (0 : Fin 3) = raw346 := by apply Matrix.ext; unfold mergeFirst pivotMatrix804 raw346; decide +kernel
    rw [heq]
    exact (canonical346 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix804 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix804 (1 : Fin 3) = raw3651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix804 raw3651; decide +kernel
    rw [heq]
    exact (canonical3651 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix804 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix804 (2 : Fin 3) = raw3847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix804 raw3847; decide +kernel
    rw [heq]
    exact (canonical3847 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node804 + (injectiveMoment H (mergeFirst pivotMatrix804 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix804 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix804 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value804, value184, value198, value203, Sparse.eval] at hc ⊢
  linarith

theorem sound805 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node805 = Sparse.eval value805 (momentVector H) := by
  have heq : pivotMatrix805 = (fun u v => node805 (pivotPermutation805 u) v) := by apply Matrix.ext; unfold pivotMatrix805 node805 pivotPermutation805; decide +kernel
  have hmoment : injectiveMoment H node805 = injectiveMoment H pivotMatrix805 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix805 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix805 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix805 (0 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix805 (0 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix805 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix805 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix805 (1 : Fin 3) = raw5718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix805 raw5718; decide +kernel
    rw [heq]
    exact (canonical5718 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix805 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix805 (2 : Fin 3) = raw5695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix805 raw5695; decide +kernel
    rw [heq]
    exact (canonical5695 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node805 + (injectiveMoment H (mergeFirst pivotMatrix805 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix805 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix805 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value805, value176, value177, value181, Sparse.eval] at hc ⊢
  linarith

theorem sound806 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node806 = Sparse.eval value806 (momentVector H) := by
  have heq : pivotMatrix806 = (fun u v => node806 (pivotPermutation806 u) v) := by apply Matrix.ext; unfold pivotMatrix806 node806 pivotPermutation806; decide +kernel
  have hmoment : injectiveMoment H node806 = injectiveMoment H pivotMatrix806 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix806 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix806 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix806 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix806 (0 : Fin 3) = raw8093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix806 raw8093; decide +kernel
    rw [heq]
    exact (canonical8093 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix806 (1 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix806 (1 : Fin 3) = raw5730 := by apply Matrix.ext; unfold mergeFirst pivotMatrix806 raw5730; decide +kernel
    rw [heq]
    exact (canonical5730 hH).trans (sound204 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix806 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix806 (2 : Fin 3) = raw5695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix806 raw5695; decide +kernel
    rw [heq]
    exact (canonical5695 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node806 + (injectiveMoment H (mergeFirst pivotMatrix806 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix806 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix806 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value806, value177, value204, value41, Sparse.eval] at hc ⊢
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

theorem sound1164 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1164 = Sparse.eval value1164 (momentVector H) := by
  have heq : pivotMatrix1164 = (fun u v => node1164.transpose (pivotPermutation1164 u) v) := by apply Matrix.ext; unfold pivotMatrix1164 node1164 pivotPermutation1164; decide +kernel
  have hmoment : injectiveMoment H node1164 = injectiveMoment H pivotMatrix1164 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1164 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1164 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1164 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1164 (0 : Fin 3) = raw5809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1164 raw5809; decide +kernel
    rw [heq]
    exact (canonical5809 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1164 (1 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1164 (1 : Fin 3) = raw8223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1164 raw8223; decide +kernel
    rw [heq]
    exact (canonical8223 hH).trans (sound199 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1164 (2 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1164 (2 : Fin 3) = raw8228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1164 raw8228; decide +kernel
    rw [heq]
    exact (canonical8228 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1164 + (injectiveMoment H (mergeFirst pivotMatrix1164 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1164 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1164 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1164, value199, value204, value85, Sparse.eval] at hc ⊢
  linarith

theorem sound1180 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1180 = Sparse.eval value1180 (momentVector H) := by
  have heq : pivotMatrix1180 = (fun u v => node1180.transpose (pivotPermutation1180 u) v) := by apply Matrix.ext; unfold pivotMatrix1180 node1180 pivotPermutation1180; decide +kernel
  have hmoment : injectiveMoment H node1180 = injectiveMoment H pivotMatrix1180 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1180 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1180 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1180 (0 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1180 (0 : Fin 3) = raw7519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1180 raw7519; decide +kernel
    rw [heq]
    exact (canonical7519 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1180 (1 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1180 (1 : Fin 3) = raw9953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1180 raw9953; decide +kernel
    rw [heq]
    exact (canonical9953 hH).trans (sound199 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1180 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1180 (2 : Fin 3) = raw9957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1180 raw9957; decide +kernel
    rw [heq]
    exact (canonical9957 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1180 + (injectiveMoment H (mergeFirst pivotMatrix1180 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1180 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1180 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1180, value198, value199, value201, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound19
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1229 = Sparse.eval value1229 (momentVector H) := by
  have heq : pivotMatrix1229 = (fun u v => node1229.transpose (pivotPermutation1229 u) v) := by apply Matrix.ext; unfold pivotMatrix1229 node1229 pivotPermutation1229; decide +kernel
  have hmoment : injectiveMoment H node1229 = injectiveMoment H pivotMatrix1229 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1229 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1229 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1229 (0 : Fin 3)) =
      Sparse.eval value217 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1229 (0 : Fin 3) = raw7526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1229 raw7526; decide +kernel
    rw [heq]
    exact (canonical7526 hH).trans (sound217 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1229 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1229 (1 : Fin 3) = raw9960 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1229 raw9960; decide +kernel
    rw [heq]
    exact (canonical9960 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1229 (2 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1229 (2 : Fin 3) = raw9972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1229 raw9972; decide +kernel
    rw [heq]
    exact (canonical9972 hH).trans (sound199 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1229 + (injectiveMoment H (mergeFirst pivotMatrix1229 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1229 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1229 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1229, value193, value199, value217, Sparse.eval] at hc ⊢
  linarith

theorem sound1257 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1257 = Sparse.eval value1257 (momentVector H) := by
  have heq : pivotMatrix1257 = (fun u v => node1257.transpose (pivotPermutation1257 u) v) := by apply Matrix.ext; unfold pivotMatrix1257 node1257 pivotPermutation1257; decide +kernel
  have hmoment : injectiveMoment H node1257 = injectiveMoment H pivotMatrix1257 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1257 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1257 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1257 (0 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1257 (0 : Fin 3) = raw7533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1257 raw7533; decide +kernel
    rw [heq]
    exact (canonical7533 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1257 (1 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1257 (1 : Fin 3) = raw9964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1257 raw9964; decide +kernel
    rw [heq]
    exact (canonical9964 hH).trans (sound151 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1257 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1257 (2 : Fin 3) = raw9976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1257 raw9976; decide +kernel
    rw [heq]
    exact (canonical9976 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1257 + (injectiveMoment H (mergeFirst pivotMatrix1257 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1257 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1257 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1257, value146, value151, value153, Sparse.eval] at hc ⊢
  linarith

theorem sound1269 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1269 = Sparse.eval value1269 (momentVector H) := by
  have heq : pivotMatrix1269 = (fun u v => node1269.transpose (pivotPermutation1269 u) v) := by apply Matrix.ext; unfold pivotMatrix1269 node1269 pivotPermutation1269; decide +kernel
  have hmoment : injectiveMoment H node1269 = injectiveMoment H pivotMatrix1269 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1269 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1269 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1269 (0 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1269 (0 : Fin 3) = raw7542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1269 raw7542; decide +kernel
    rw [heq]
    exact (canonical7542 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1269 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1269 (1 : Fin 3) = raw9968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1269 raw9968; decide +kernel
    rw [heq]
    exact (canonical9968 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1269 (2 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1269 (2 : Fin 3) = raw9980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1269 raw9980; decide +kernel
    rw [heq]
    exact (canonical9980 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1269 + (injectiveMoment H (mergeFirst pivotMatrix1269 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1269 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1269 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1269, value198, value204, value215, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound6
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node394 = Sparse.eval value394 (momentVector H) := by
  have hc : momentVector H 282 = injectiveMoment H node394 := rfl
  simp [value394, Sparse.eval, hc]

theorem sound395 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node395 = Sparse.eval value395 (momentVector H) := by
  have hc : momentVector H 72 = injectiveMoment H node395 := rfl
  simp [value395, Sparse.eval, hc]

theorem sound397 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node397 = Sparse.eval value397 (momentVector H) := by
  have hc : momentVector H 74 = injectiveMoment H node397 := rfl
  simp [value397, Sparse.eval, hc]

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

theorem sound1471 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1471 = Sparse.eval value1471 (momentVector H) := by
  have heq : pivotMatrix1471 = (fun u v => node1471 (pivotPermutation1471 u) v) := by apply Matrix.ext; unfold pivotMatrix1471 node1471 pivotPermutation1471; decide +kernel
  have hmoment : injectiveMoment H node1471 = injectiveMoment H pivotMatrix1471 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1471 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1471 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1471 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1471 (0 : Fin 4) = raw1259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1471 raw1259; decide +kernel
    rw [heq]
    exact (canonical1259 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1471 (1 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1471 (1 : Fin 4) = raw1150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1471 raw1150; decide +kernel
    rw [heq]
    exact (canonical1150 hH).trans (sound397 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1471 (2 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1471 (2 : Fin 4) = raw1141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1471 raw1141; decide +kernel
    rw [heq]
    exact (canonical1141 hH).trans (sound1164 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1471 (3 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1471 (3 : Fin 4) = raw1139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1471 raw1139; decide +kernel
    rw [heq]
    exact (canonical1139 hH).trans (sound771 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1471 + (injectiveMoment H (mergeFirst pivotMatrix1471 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1471 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1471 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1471 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1471, value1164, value397, value771, value804, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound25
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1638 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1638 = Sparse.eval value1638 (momentVector H) := by
  have heq : pivotMatrix1638 = (fun u v => node1638 (pivotPermutation1638 u) v) := by apply Matrix.ext; unfold pivotMatrix1638 node1638 pivotPermutation1638; decide +kernel
  have hmoment : injectiveMoment H node1638 = injectiveMoment H pivotMatrix1638 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1638 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1638 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1638 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1638 (0 : Fin 4) = raw1259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1638 raw1259; decide +kernel
    rw [heq]
    exact (canonical1259 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1638 (1 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1638 (1 : Fin 4) = raw1916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1638 raw1916; decide +kernel
    rw [heq]
    exact (canonical1916 hH).trans (sound802 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1638 (2 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1638 (2 : Fin 4) = raw2053 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1638 raw2053; decide +kernel
    rw [heq]
    exact (canonical2053 hH).trans (sound806 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1638 (3 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1638 (3 : Fin 4) = raw2063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1638 raw2063; decide +kernel
    rw [heq]
    exact (canonical2063 hH).trans (sound805 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1638 + (injectiveMoment H (mergeFirst pivotMatrix1638 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1638 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1638 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1638 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1638, value802, value804, value805, value806, Sparse.eval] at hc ⊢
  linarith

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

theorem sound1922 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1922 = Sparse.eval value1922 (momentVector H) := by
  have heq : pivotMatrix1922 = (fun u v => node1922 (pivotPermutation1922 u) v) := by apply Matrix.ext; unfold pivotMatrix1922 node1922 pivotPermutation1922; decide +kernel
  have hmoment : injectiveMoment H node1922 = injectiveMoment H pivotMatrix1922 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1922 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1922 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1922 (0 : Fin 4)) =
      Sparse.eval value1269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1922 (0 : Fin 4) = raw3208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1922 raw3208; decide +kernel
    rw [heq]
    exact (canonical3208 hH).trans (sound1269 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1922 (1 : Fin 4)) =
      Sparse.eval value1180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1922 (1 : Fin 4) = raw3011 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1922 raw3011; decide +kernel
    rw [heq]
    exact (canonical3011 hH).trans (sound1180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1922 (2 : Fin 4)) =
      Sparse.eval value1229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1922 (2 : Fin 4) = raw3003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1922 raw3003; decide +kernel
    rw [heq]
    exact (canonical3003 hH).trans (sound1229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1922 (3 : Fin 4)) =
      Sparse.eval value1159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1922 (3 : Fin 4) = raw3001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1922 raw3001; decide +kernel
    rw [heq]
    exact (canonical3001 hH).trans (sound1159 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1922 + (injectiveMoment H (mergeFirst pivotMatrix1922 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1922 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1922 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1922 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1922, value1159, value1180, value1229, value1269, Sparse.eval] at hc ⊢
  linarith

theorem sound1931 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1931 = Sparse.eval value1931 (momentVector H) := by
  have heq : pivotMatrix1931 = (fun u v => node1931 (pivotPermutation1931 u) v) := by apply Matrix.ext; unfold pivotMatrix1931 node1931 pivotPermutation1931; decide +kernel
  have hmoment : injectiveMoment H node1931 = injectiveMoment H pivotMatrix1931 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1931 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1931 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1931 (0 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1931 (0 : Fin 4) = raw4270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1931 raw4270; decide +kernel
    rw [heq]
    exact (canonical4270 hH).trans (sound394 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1931 (1 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1931 (1 : Fin 4) = raw3021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1931 raw3021; decide +kernel
    rw [heq]
    exact (canonical3021 hH).trans (sound397 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1931 (2 : Fin 4)) =
      Sparse.eval value395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1931 (2 : Fin 4) = raw2985 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1931 raw2985; decide +kernel
    rw [heq]
    exact (canonical2985 hH).trans (sound395 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1931 (3 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1931 (3 : Fin 4) = raw2980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1931 raw2980; decide +kernel
    rw [heq]
    exact (canonical2980 hH).trans (sound1257 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1931 + (injectiveMoment H (mergeFirst pivotMatrix1931 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1931 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1931 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1931 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1931, value1257, value394, value395, value397, Sparse.eval] at hc ⊢
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

theorem sound3119_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3119 = Sparse.eval value3119 (momentVector H) := by
  have heq : pivotMatrix3119 = (fun u v => node3119 (pivotPermutation3119 u) v) := by apply Matrix.ext; unfold pivotMatrix3119 node3119 pivotPermutation3119; decide +kernel
  have hmoment : injectiveMoment H node3119 = injectiveMoment H pivotMatrix3119 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3119 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3119 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3119 (0 : Fin 5)) =
      Sparse.eval value1638 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3119 (0 : Fin 5) = raw3124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3119 raw3124; decide +kernel
    rw [heq]
    exact (canonical3124 hH).trans (sound1638 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3119 (1 : Fin 5)) =
      Sparse.eval value1931 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3119 (1 : Fin 5) = raw2976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3119 raw2976; decide +kernel
    rw [heq]
    exact (canonical2976 hH).trans (sound1931 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3119 (2 : Fin 5)) =
      Sparse.eval value1471 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3119 (2 : Fin 5) = raw2954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3119 raw2954; decide +kernel
    rw [heq]
    exact (canonical2954 hH).trans (sound1471 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3119 (3 : Fin 5)) =
      Sparse.eval value1922 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3119 (3 : Fin 5) = raw2952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3119 raw2952; decide +kernel
    rw [heq]
    exact (canonical2952 hH).trans (sound1922 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3119 (4 : Fin 5)) =
      Sparse.eval value1921 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3119 (4 : Fin 5) = raw2951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3119 raw2951; decide +kernel
    rw [heq]
    exact (canonical2951 hH).trans (sound1921 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3119 + (injectiveMoment H (mergeFirst pivotMatrix3119 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3119 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3119 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3119 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3119 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3119, value1471, value1638, value1921, value1922, value1931, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3119_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3119_e_oai
