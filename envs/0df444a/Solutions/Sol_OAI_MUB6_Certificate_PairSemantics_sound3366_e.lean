-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3366_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T11:55:48.00517+00:00
-- url     : https://prove2.me/submissions/fbcafd0e-18e0-480c-9406-3aa1ec2ae8ca

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2521_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2547_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2548_e

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

theorem canonical35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw35 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw35 = injectiveMoment H raw35step0 := by
      have heq : raw35step0 = raw35.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw35).symm
    injectiveMoment H raw35step0 = injectiveMoment H raw35step1 := by
      have heq : raw35step1 = (fun i j => raw35step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw35step0 permutation4 permutation1
    _ = injectiveMoment H node7 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3777 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3777 = injectiveMoment H node965 := by
  calc
    injectiveMoment H raw3777 = injectiveMoment H raw3777step0 := by
      have heq : raw3777step0 = -raw3777 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3777).symm
    injectiveMoment H raw3777step0 = injectiveMoment H raw3777step1 := by
      have heq : raw3777step1 = (fun i j => raw3777step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3777step0 permutation29 permutation15
    _ = injectiveMoment H node965 := by rfl

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

theorem canonical4174 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4174 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw4174 = injectiveMoment H raw4174step0 := by
      have heq : raw4174step0 = raw4174.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4174).symm
    injectiveMoment H raw4174step0 = injectiveMoment H raw4174step1 := by
      have heq : raw4174step1 = (fun i j => raw4174step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4174step0 permutation13 permutation3
    _ = injectiveMoment H node170 := by rfl

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

theorem canonical4908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4908 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4908 = injectiveMoment H raw4908step0 := by
      have heq : raw4908step0 = -raw4908 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4908).symm
    injectiveMoment H raw4908step0 = injectiveMoment H raw4908step1 := by
      have heq : raw4908step1 = (fun i j => raw4908step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4908step0 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

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

theorem canonical4963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4963 = injectiveMoment H node42 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5018 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5018 = injectiveMoment H node980 := by
  calc
    injectiveMoment H raw5018 = injectiveMoment H raw5018step0 := by
      have heq : raw5018step0 = raw5018.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5018).symm
    injectiveMoment H raw5018step0 = injectiveMoment H raw5018step1 := by
      have heq : raw5018step1 = -raw5018step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5018step0).symm
    injectiveMoment H raw5018step1 = injectiveMoment H raw5018step2 := by
      have heq : raw5018step2 = (fun i j => raw5018step1 (permutation25 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5018step1 permutation25 permutation16
    _ = injectiveMoment H node980 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5032 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5032 = injectiveMoment H node932 := by
  calc
    injectiveMoment H raw5032 = injectiveMoment H raw5032step0 := by
      have heq : raw5032step0 = raw5032.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5032).symm
    injectiveMoment H raw5032step0 = injectiveMoment H raw5032step1 := by
      have heq : raw5032step1 = -raw5032step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5032step0).symm
    injectiveMoment H raw5032step1 = injectiveMoment H raw5032step2 := by
      have heq : raw5032step2 = (fun i j => raw5032step1 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5032step1 permutation23 permutation16
    _ = injectiveMoment H node932 := by rfl

theorem canonical5033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5033 = injectiveMoment H node800 := by
  calc
    injectiveMoment H raw5033 = injectiveMoment H raw5033step0 := by
      have heq : raw5033step0 = raw5033.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5033).symm
    injectiveMoment H raw5033step0 = injectiveMoment H raw5033step1 := by
      have heq : raw5033step1 = (fun i j => raw5033step0 (permutation29 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5033step0 permutation29 permutation19
    _ = injectiveMoment H node800 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical5712 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5712 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw5712 = injectiveMoment H raw5712step0 := by
      have heq : raw5712step0 = raw5712.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5712).symm
    injectiveMoment H raw5712step0 = injectiveMoment H raw5712step1 := by
      have heq : raw5712step1 = -raw5712step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5712step0).symm
    injectiveMoment H raw5712step1 = injectiveMoment H raw5712step2 := by
      have heq : raw5712step2 = (fun i j => raw5712step1 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5712step1 permutation16 permutation6
    _ = injectiveMoment H node285 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical191
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6112 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw6112 = injectiveMoment H raw6112step0 := by
      have heq : raw6112step0 = raw6112.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6112).symm
    injectiveMoment H raw6112step0 = injectiveMoment H raw6112step1 := by
      have heq : raw6112step1 = -raw6112step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6112step0).symm
    injectiveMoment H raw6112step1 = injectiveMoment H raw6112step2 := by
      have heq : raw6112step2 = (fun i j => raw6112step1 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6112step1 permutation15 permutation6
    _ = injectiveMoment H node228 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical192
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6162 = injectiveMoment H node2521 := by
  rfl

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

theorem canonical6233 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6233 = injectiveMoment H node2319 := by
  calc
    injectiveMoment H raw6233 = injectiveMoment H raw6233step0 := by
      have heq : raw6233step0 = -raw6233 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6233).symm
    injectiveMoment H raw6233step0 = injectiveMoment H raw6233step1 := by
      have heq : raw6233step1 = (fun i j => raw6233step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6233step0 permutation101 permutation15
    _ = injectiveMoment H node2319 := by rfl

theorem canonical6235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6235 = injectiveMoment H node2547 := by
  calc
    injectiveMoment H raw6235 = injectiveMoment H raw6235step0 := by
      have heq : raw6235step0 = (fun i j => raw6235 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6235 permutation35 permutation9
    _ = injectiveMoment H node2547 := by rfl

theorem canonical6237 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6237 = injectiveMoment H node2548 := by
  calc
    injectiveMoment H raw6237 = injectiveMoment H raw6237step0 := by
      have heq : raw6237step0 = (fun i j => raw6237 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6237 permutation34 permutation9
    _ = injectiveMoment H node2548 := by rfl

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

theorem canonical6304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6304 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6304 = injectiveMoment H raw6304step0 := by
      have heq : raw6304step0 = raw6304.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6304).symm
    injectiveMoment H raw6304step0 = injectiveMoment H raw6304step1 := by
      have heq : raw6304step1 = (fun i j => raw6304step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6304step0 permutation21 permutation5
    _ = injectiveMoment H node173 := by rfl

theorem canonical6330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6330 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw6330 = injectiveMoment H raw6330step0 := by
      have heq : raw6330step0 = raw6330.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6330).symm
    injectiveMoment H raw6330step0 = injectiveMoment H raw6330step1 := by
      have heq : raw6330step1 = (fun i j => raw6330step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6330step0 permutation22 permutation5
    _ = injectiveMoment H node170 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical208
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6679 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6679 = injectiveMoment H node982 := by
  calc
    injectiveMoment H raw6679 = injectiveMoment H raw6679step0 := by
      have heq : raw6679step0 = raw6679.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6679).symm
    injectiveMoment H raw6679step0 = injectiveMoment H raw6679step1 := by
      have heq : raw6679step1 = -raw6679step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6679step0).symm
    injectiveMoment H raw6679step1 = injectiveMoment H raw6679step2 := by
      have heq : raw6679step2 = (fun i j => raw6679step1 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6679step1 permutation23 permutation15
    _ = injectiveMoment H node982 := by rfl

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

theorem canonical6892 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6892 = injectiveMoment H node219 := by
  calc
    injectiveMoment H raw6892 = injectiveMoment H raw6892step0 := by
      have heq : raw6892step0 = raw6892.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6892).symm
    injectiveMoment H raw6892step0 = injectiveMoment H raw6892step1 := by
      have heq : raw6892step1 = -raw6892step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6892step0).symm
    injectiveMoment H raw6892step1 = injectiveMoment H raw6892step2 := by
      have heq : raw6892step2 = (fun i j => raw6892step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6892step1 permutation26 permutation3
    _ = injectiveMoment H node219 := by rfl

theorem canonical6903 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6903 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw6903 = injectiveMoment H raw6903step0 := by
      have heq : raw6903step0 = raw6903.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6903).symm
    injectiveMoment H raw6903step0 = injectiveMoment H raw6903step1 := by
      have heq : raw6903step1 = -raw6903step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6903step0).symm
    injectiveMoment H raw6903step1 = injectiveMoment H raw6903step2 := by
      have heq : raw6903step2 = (fun i j => raw6903step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6903step1 permutation25 permutation3
    _ = injectiveMoment H node223 := by rfl

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

theorem canonical6936 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6936 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw6936 = injectiveMoment H raw6936step0 := by
      have heq : raw6936step0 = raw6936.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6936).symm
    injectiveMoment H raw6936step0 = injectiveMoment H raw6936step1 := by
      have heq : raw6936step1 = -raw6936step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6936step0).symm
    injectiveMoment H raw6936step1 = injectiveMoment H raw6936step2 := by
      have heq : raw6936step2 = (fun i j => raw6936step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6936step1 permutation26 permutation3
    _ = injectiveMoment H node187 := by rfl

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

theorem canonical7110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7110 = injectiveMoment H node143 := by
  calc
    injectiveMoment H raw7110 = injectiveMoment H raw7110step0 := by
      have heq : raw7110step0 = raw7110.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7110).symm
    injectiveMoment H raw7110step0 = injectiveMoment H raw7110step1 := by
      have heq : raw7110step1 = (fun i j => raw7110step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7110step0 permutation21 permutation5
    _ = injectiveMoment H node143 := by rfl

theorem canonical7114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7114 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw7114 = injectiveMoment H raw7114step0 := by
      have heq : raw7114step0 = raw7114.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7114).symm
    injectiveMoment H raw7114step0 = injectiveMoment H raw7114step1 := by
      have heq : raw7114step1 = (fun i j => raw7114step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7114step0 permutation22 permutation5
    _ = injectiveMoment H node269 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7231 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw7231 = injectiveMoment H raw7231step0 := by
      have heq : raw7231step0 = raw7231.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7231).symm
    injectiveMoment H raw7231step0 = injectiveMoment H raw7231step1 := by
      have heq : raw7231step1 = (fun i j => raw7231step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7231step0 permutation21 permutation5
    _ = injectiveMoment H node174 := by rfl

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

theorem canonical7525 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7525 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw7525 = injectiveMoment H raw7525step0 := by
      have heq : raw7525step0 = raw7525.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7525).symm
    injectiveMoment H raw7525step0 = injectiveMoment H raw7525step1 := by
      have heq : raw7525step1 = -raw7525step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7525step0).symm
    injectiveMoment H raw7525step1 = injectiveMoment H raw7525step2 := by
      have heq : raw7525step2 = (fun i j => raw7525step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7525step1 permutation24 permutation3
    _ = injectiveMoment H node222 := by rfl

theorem canonical7543 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7543 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw7543 = injectiveMoment H raw7543step0 := by
      have heq : raw7543step0 = raw7543.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7543).symm
    injectiveMoment H raw7543step0 = injectiveMoment H raw7543step1 := by
      have heq : raw7543step1 = -raw7543step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7543step0).symm
    injectiveMoment H raw7543step1 = injectiveMoment H raw7543step2 := by
      have heq : raw7543step2 = (fun i j => raw7543step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7543step1 permutation23 permutation3
    _ = injectiveMoment H node223 := by rfl

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

theorem canonical7587 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7587 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw7587 = injectiveMoment H raw7587step0 := by
      have heq : raw7587step0 = raw7587.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7587).symm
    injectiveMoment H raw7587step0 = injectiveMoment H raw7587step1 := by
      have heq : raw7587step1 = (fun i j => raw7587step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7587step0 permutation27 permutation5
    _ = injectiveMoment H node174 := by rfl

theorem canonical7592 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7592 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw7592 = injectiveMoment H raw7592step0 := by
      have heq : raw7592step0 = raw7592.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7592).symm
    injectiveMoment H raw7592step0 = injectiveMoment H raw7592step1 := by
      have heq : raw7592step1 = -raw7592step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7592step0).symm
    injectiveMoment H raw7592step1 = injectiveMoment H raw7592step2 := by
      have heq : raw7592step2 = (fun i j => raw7592step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7592step1 permutation23 permutation3
    _ = injectiveMoment H node166 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7883 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7883 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7883 = injectiveMoment H raw7883step0 := by
      have heq : raw7883step0 = -raw7883 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7883).symm
    injectiveMoment H raw7883step0 = injectiveMoment H raw7883step1 := by
      have heq : raw7883step1 = (fun i j => raw7883step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7883step0 permutation8 permutation3
    _ = injectiveMoment H node58 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8369 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8369 = injectiveMoment H node1312 := by
  calc
    injectiveMoment H raw8369 = injectiveMoment H raw8369step0 := by
      have heq : raw8369step0 = (fun i j => raw8369 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8369 permutation15 permutation9
    _ = injectiveMoment H node1312 := by rfl

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

theorem canonical8475 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8475 = injectiveMoment H node1218 := by
  calc
    injectiveMoment H raw8475 = injectiveMoment H raw8475step0 := by
      have heq : raw8475step0 = raw8475.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8475).symm
    injectiveMoment H raw8475step0 = injectiveMoment H raw8475step1 := by
      have heq : raw8475step1 = -raw8475step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8475step0).symm
    injectiveMoment H raw8475step1 = injectiveMoment H raw8475step2 := by
      have heq : raw8475step2 = (fun i j => raw8475step1 (permutation21 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8475step1 permutation21 permutation15
    _ = injectiveMoment H node1218 := by rfl

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

theorem canonical8483 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8483 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw8483 = injectiveMoment H raw8483step0 := by
      have hz : ∀ i, raw8483 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8483step0 = (fun i j => raw8483 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8483 permutation9 hz
    injectiveMoment H raw8483step0 = injectiveMoment H raw8483step1 := by
      have heq : raw8483step1 = (fun i j => raw8483step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8483step0 permutation27 permutation5
    _ = injectiveMoment H node174 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw962 = injectiveMoment H node49 := by
  calc
    injectiveMoment H raw962 = injectiveMoment H raw962step0 := by
      have heq : raw962step0 = raw962.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw962).symm
    injectiveMoment H raw962step0 = injectiveMoment H raw962step1 := by
      have heq : raw962step1 = (fun i j => raw962step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw962step0 permutation8 permutation6
    _ = injectiveMoment H node49 := by rfl

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

theorem canonical182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw182 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw182 = injectiveMoment H raw182step0 := by
      have heq : raw182step0 = raw182.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw182).symm
    injectiveMoment H raw182step0 = injectiveMoment H raw182step1 := by
      have heq : raw182step1 = (fun i j => raw182step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw182step0 permutation4 permutation1
    _ = injectiveMoment H node8 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2527 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2527 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw2527 = injectiveMoment H raw2527step0 := by
      have heq : raw2527step0 = raw2527.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2527).symm
    injectiveMoment H raw2527step0 = injectiveMoment H raw2527step1 := by
      have heq : raw2527step1 = -raw2527step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2527step0).symm
    injectiveMoment H raw2527step1 = injectiveMoment H raw2527step2 := by
      have heq : raw2527step2 = (fun i j => raw2527step1 (permutation32 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2527step1 permutation32 permutation5
    _ = injectiveMoment H node89 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2729 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2729 = injectiveMoment H node27 := by
  calc
    injectiveMoment H raw2729 = injectiveMoment H raw2729step0 := by
      have heq : raw2729step0 = -raw2729 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2729).symm
    injectiveMoment H raw2729step0 = injectiveMoment H raw2729step1 := by
      have heq : raw2729step1 = (fun i j => raw2729step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2729step0 permutation8 permutation3
    _ = injectiveMoment H node27 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3113 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3113 = injectiveMoment H node2815 := by
  calc
    injectiveMoment H raw3113 = injectiveMoment H raw3113step0 := by
      have heq : raw3113step0 = -raw3113 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3113).symm
    injectiveMoment H raw3113step0 = injectiveMoment H raw3113step1 := by
      have heq : raw3113step1 = (fun i j => raw3113step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3113step0 permutation100 permutation15
    _ = injectiveMoment H node2815 := by rfl

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

theorem sound27 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node27 = Sparse.eval value27 (momentVector H) := by
  have hc : momentVector H 69 = injectiveMoment H node27 := rfl
  simp [value27, Sparse.eval, hc]

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

theorem sound42 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node42 = Sparse.eval value42 (momentVector H) := by
  have hc : momentVector H 11 = injectiveMoment H node42 := rfl
  simp [value42, Sparse.eval, hc]

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

theorem sound49 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node49 = Sparse.eval value49 (momentVector H) := by
  have heq : pivotMatrix49 = (fun u v => node49.transpose (pivotPermutation49 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node49 = injectiveMoment H pivotMatrix49 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix49 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix49 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix49 (0 : Fin 2)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix49 (0 : Fin 2) = raw35 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical35 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix49 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix49 (1 : Fin 2) = raw182 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical182 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node49 + (injectiveMoment H (mergeFirst pivotMatrix49 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix49 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value49, value7, value8, Sparse.eval] at hc ⊢
  linarith

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

theorem sound89 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node89 = Sparse.eval value89 (momentVector H) := by
  have hc : momentVector H 262 = injectiveMoment H node89 := rfl
  simp [value89, Sparse.eval, hc]

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

theorem sound143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node143 = Sparse.eval value143 (momentVector H) := by
  have heq : pivotMatrix143 = (fun u v => node143 (pivotPermutation143 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node143 = injectiveMoment H pivotMatrix143 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix143 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix143 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix143 (0 : Fin 3)) =
      Sparse.eval value49 (momentVector H) := by
    have heq : mergeFirst pivotMatrix143 (0 : Fin 3) = raw962 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical962 hH).trans (sound49 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix143 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix143 (1 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix143 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix143 (2 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node143 + (injectiveMoment H (mergeFirst pivotMatrix143 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix143 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix143 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value143, value49, value52, value59, Sparse.eval] at hc ⊢
  linarith

theorem sound166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node166 = Sparse.eval value166 (momentVector H) := by
  have heq : pivotMatrix166 = (fun u v => node166 (pivotPermutation166 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node166 = injectiveMoment H pivotMatrix166 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix166 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix166 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix166 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix166 (0 : Fin 3) = raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix166 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix166 (1 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix166 (2 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix166 (2 : Fin 3) = raw2729 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2729 hH).trans (sound27 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node166 + (injectiveMoment H (mergeFirst pivotMatrix166 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix166 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix166 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value166, value27, value40, value52, Sparse.eval] at hc ⊢
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

theorem sound174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node174 = Sparse.eval value174 (momentVector H) := by
  have heq : pivotMatrix174 = (fun u v => node174 (pivotPermutation174 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node174 = injectiveMoment H pivotMatrix174 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix174 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix174 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix174 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (0 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix174 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (1 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix174 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (2 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node174 + (injectiveMoment H (mergeFirst pivotMatrix174 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix174 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix174 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value174, value52, value56, value63, Sparse.eval] at hc ⊢
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

theorem sound219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node219 = Sparse.eval value219 (momentVector H) := by
  have hc : momentVector H 796 = injectiveMoment H node219 := rfl
  simp [value219, Sparse.eval, hc]

theorem sound222 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node222 = Sparse.eval value222 (momentVector H) := by
  have heq : pivotMatrix222 = (fun u v => node222 (pivotPermutation222 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node222 = injectiveMoment H pivotMatrix222 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix222 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix222 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix222 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix222 (0 : Fin 3) = raw7883 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7883 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix222 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix222 (1 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix222 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix222 (2 : Fin 3) = raw4908 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4908 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node222 + (injectiveMoment H (mergeFirst pivotMatrix222 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix222 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix222 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value222, value32, value43, value58, Sparse.eval] at hc ⊢
  linarith

theorem sound223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node223 = Sparse.eval value223 (momentVector H) := by
  have hc : momentVector H 56 = injectiveMoment H node223 := rfl
  simp [value223, Sparse.eval, hc]

theorem sound228 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node228 = Sparse.eval value228 (momentVector H) := by
  have heq : pivotMatrix228 = (fun u v => node228 (pivotPermutation228 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node228 = injectiveMoment H pivotMatrix228 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix228 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix228 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix228 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix228 (0 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix228 (1 : Fin 3)) =
      Sparse.eval value42 (momentVector H) := by
    have heq : mergeFirst pivotMatrix228 (1 : Fin 3) = raw4963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4963 hH).trans (sound42 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix228 (2 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix228 (2 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node228 + (injectiveMoment H (mergeFirst pivotMatrix228 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix228 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix228 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value228, value32, value42, value43, Sparse.eval] at hc ⊢
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
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound269 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node269 = Sparse.eval value269 (momentVector H) := by
  have heq : pivotMatrix269 = (fun u v => node269 (pivotPermutation269 u) v) := by apply Matrix.ext; unfold pivotMatrix269 node269 pivotPermutation269; decide +kernel
  have hmoment : injectiveMoment H node269 = injectiveMoment H pivotMatrix269 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix269 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix269 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix269 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix269 (0 : Fin 3) = raw5550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix269 raw5550; decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix269 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix269 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix269 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix269 (2 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix269 (2 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix269 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node269 + (injectiveMoment H (mergeFirst pivotMatrix269 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix269 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix269 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value269, value53, value57, value58, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound12
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound800 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node800 = Sparse.eval value800 (momentVector H) := by
  have heq : pivotMatrix800 = (fun u v => node800 (pivotPermutation800 u) v) := by apply Matrix.ext; unfold pivotMatrix800 node800 pivotPermutation800; decide +kernel
  have hmoment : injectiveMoment H node800 = injectiveMoment H pivotMatrix800 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix800 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix800 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix800 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix800 (0 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix800 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix800 (1 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix800 (1 : Fin 3) = raw5712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix800 raw5712; decide +kernel
    rw [heq]
    exact (canonical5712 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix800 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix800 (2 : Fin 3) = raw5705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix800 raw5705; decide +kernel
    rw [heq]
    exact (canonical5705 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node800 + (injectiveMoment H (mergeFirst pivotMatrix800 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix800 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix800 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value800, value206, value229, value285, Sparse.eval] at hc ⊢
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

theorem sound932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node932 = Sparse.eval value932 (momentVector H) := by
  have heq : pivotMatrix932 = (fun u v => node932.transpose (pivotPermutation932 u) v) := by apply Matrix.ext; unfold pivotMatrix932 node932 pivotPermutation932; decide +kernel
  have hmoment : injectiveMoment H node932 = injectiveMoment H pivotMatrix932 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix932 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix932 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix932 (0 : Fin 3)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix932 (0 : Fin 3) = raw2527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix932 raw2527; decide +kernel
    rw [heq]
    exact (canonical2527 hH).trans (sound89 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix932 (1 : Fin 3)) =
      Sparse.eval value219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix932 (1 : Fin 3) = raw6892 := by apply Matrix.ext; unfold mergeFirst pivotMatrix932 raw6892; decide +kernel
    rw [heq]
    exact (canonical6892 hH).trans (sound219 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix932 (2 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix932 (2 : Fin 3) = raw6903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix932 raw6903; decide +kernel
    rw [heq]
    exact (canonical6903 hH).trans (sound223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node932 + (injectiveMoment H (mergeFirst pivotMatrix932 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix932 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix932 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value932, value219, value223, value89, Sparse.eval] at hc ⊢
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

theorem sound965 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node965 = Sparse.eval value965 (momentVector H) := by
  have heq : pivotMatrix965 = (fun u v => node965 (pivotPermutation965 u) v) := by apply Matrix.ext; unfold pivotMatrix965 node965 pivotPermutation965; decide +kernel
  have hmoment : injectiveMoment H node965 = injectiveMoment H pivotMatrix965 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix965 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix965 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix965 (0 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix965 (0 : Fin 3) = raw6112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix965 raw6112; decide +kernel
    rw [heq]
    exact (canonical6112 hH).trans (sound228 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix965 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix965 (1 : Fin 3) = raw6330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix965 raw6330; decide +kernel
    rw [heq]
    exact (canonical6330 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix965 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix965 (2 : Fin 3) = raw6331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix965 raw6331; decide +kernel
    rw [heq]
    exact (canonical6331 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node965 + (injectiveMoment H (mergeFirst pivotMatrix965 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix965 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix965 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value965, value170, value228, value229, Sparse.eval] at hc ⊢
  linarith

theorem sound980 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node980 = Sparse.eval value980 (momentVector H) := by
  have heq : pivotMatrix980 = (fun u v => node980.transpose (pivotPermutation980 u) v) := by apply Matrix.ext; unfold pivotMatrix980 node980 pivotPermutation980; decide +kernel
  have hmoment : injectiveMoment H node980 = injectiveMoment H pivotMatrix980 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix980 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix980 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix980 (0 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix980 (0 : Fin 3) = raw4174 := by apply Matrix.ext; unfold mergeFirst pivotMatrix980 raw4174; decide +kernel
    rw [heq]
    exact (canonical4174 hH).trans (sound170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix980 (1 : Fin 3)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix980 (1 : Fin 3) = raw7525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix980 raw7525; decide +kernel
    rw [heq]
    exact (canonical7525 hH).trans (sound222 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix980 (2 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix980 (2 : Fin 3) = raw7543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix980 raw7543; decide +kernel
    rw [heq]
    exact (canonical7543 hH).trans (sound223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node980 + (injectiveMoment H (mergeFirst pivotMatrix980 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix980 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix980 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value980, value170, value222, value223, Sparse.eval] at hc ⊢
  linarith

theorem sound982 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node982 = Sparse.eval value982 (momentVector H) := by
  have heq : pivotMatrix982 = (fun u v => node982 (pivotPermutation982 u) v) := by apply Matrix.ext; unfold pivotMatrix982 node982 pivotPermutation982; decide +kernel
  have hmoment : injectiveMoment H node982 = injectiveMoment H pivotMatrix982 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix982 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix982 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix982 (0 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix982 (0 : Fin 3) = raw7231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix982 raw7231; decide +kernel
    rw [heq]
    exact (canonical7231 hH).trans (sound174 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix982 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix982 (1 : Fin 3) = raw6330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix982 raw6330; decide +kernel
    rw [heq]
    exact (canonical6330 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix982 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix982 (2 : Fin 3) = raw6304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix982 raw6304; decide +kernel
    rw [heq]
    exact (canonical6304 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node982 + (injectiveMoment H (mergeFirst pivotMatrix982 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix982 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix982 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value982, value170, value173, value174, Sparse.eval] at hc ⊢
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

theorem sound1218 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1218 = Sparse.eval value1218 (momentVector H) := by
  have heq : pivotMatrix1218 = (fun u v => node1218 (pivotPermutation1218 u) v) := by apply Matrix.ext; unfold pivotMatrix1218 node1218 pivotPermutation1218; decide +kernel
  have hmoment : injectiveMoment H node1218 = injectiveMoment H pivotMatrix1218 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1218 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1218 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1218 (0 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1218 (0 : Fin 3) = raw7231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1218 raw7231; decide +kernel
    rw [heq]
    exact (canonical7231 hH).trans (sound174 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1218 (1 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1218 (1 : Fin 3) = raw7114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1218 raw7114; decide +kernel
    rw [heq]
    exact (canonical7114 hH).trans (sound269 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1218 (2 : Fin 3)) =
      Sparse.eval value143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1218 (2 : Fin 3) = raw7110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1218 raw7110; decide +kernel
    rw [heq]
    exact (canonical7110 hH).trans (sound143 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1218 + (injectiveMoment H (mergeFirst pivotMatrix1218 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1218 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1218 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1218, value143, value174, value269, Sparse.eval] at hc ⊢
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

theorem sound1312 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1312 = Sparse.eval value1312 (momentVector H) := by
  have heq : pivotMatrix1312 = (fun u v => node1312 (pivotPermutation1312 u) v) := by apply Matrix.ext; unfold pivotMatrix1312 node1312 pivotPermutation1312; decide +kernel
  have hmoment : injectiveMoment H node1312 = injectiveMoment H pivotMatrix1312 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1312 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1312 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1312 (0 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1312 (0 : Fin 3) = raw6936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1312 raw6936; decide +kernel
    rw [heq]
    exact (canonical6936 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1312 (1 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1312 (1 : Fin 3) = raw7587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1312 raw7587; decide +kernel
    rw [heq]
    exact (canonical7587 hH).trans (sound174 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1312 (2 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1312 (2 : Fin 3) = raw7592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1312 raw7592; decide +kernel
    rw [heq]
    exact (canonical7592 hH).trans (sound166 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1312 + (injectiveMoment H (mergeFirst pivotMatrix1312 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1312 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1312 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1312, value166, value174, value187, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound36
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2319 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2319 = Sparse.eval value2319 (momentVector H) := by
  have heq : pivotMatrix2319 = (fun u v => node2319 (pivotPermutation2319 u) v) := by apply Matrix.ext; unfold pivotMatrix2319 node2319 pivotPermutation2319; decide +kernel
  have hmoment : injectiveMoment H node2319 = injectiveMoment H pivotMatrix2319 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2319 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2319 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2319 (0 : Fin 4)) =
      Sparse.eval value965 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2319 (0 : Fin 4) = raw3777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2319 raw3777; decide +kernel
    rw [heq]
    exact (canonical3777 hH).trans (sound965 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2319 (1 : Fin 4)) =
      Sparse.eval value980 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2319 (1 : Fin 4) = raw5018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2319 raw5018; decide +kernel
    rw [heq]
    exact (canonical5018 hH).trans (sound980 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2319 (2 : Fin 4)) =
      Sparse.eval value932 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2319 (2 : Fin 4) = raw5032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2319 raw5032; decide +kernel
    rw [heq]
    exact (canonical5032 hH).trans (sound932 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2319 (3 : Fin 4)) =
      Sparse.eval value800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2319 (3 : Fin 4) = raw5033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2319 raw5033; decide +kernel
    rw [heq]
    exact (canonical5033 hH).trans (sound800 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2319 + (injectiveMoment H (mergeFirst pivotMatrix2319 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2319 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2319 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2319 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2319, value800, value932, value965, value980, Sparse.eval] at hc ⊢
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

theorem sound2815 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2815 = Sparse.eval value2815 (momentVector H) := by
  have heq : pivotMatrix2815 = (fun u v => node2815 (pivotPermutation2815 u) v) := by apply Matrix.ext; unfold pivotMatrix2815 node2815 pivotPermutation2815; decide +kernel
  have hmoment : injectiveMoment H node2815 = injectiveMoment H pivotMatrix2815 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2815 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2815 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2815 (0 : Fin 4)) =
      Sparse.eval value982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2815 (0 : Fin 4) = raw6679 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2815 raw6679; decide +kernel
    rw [heq]
    exact (canonical6679 hH).trans (sound982 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2815 (1 : Fin 4)) =
      Sparse.eval value1312 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2815 (1 : Fin 4) = raw8369 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2815 raw8369; decide +kernel
    rw [heq]
    exact (canonical8369 hH).trans (sound1312 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2815 (2 : Fin 4)) =
      Sparse.eval value1218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2815 (2 : Fin 4) = raw8475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2815 raw8475; decide +kernel
    rw [heq]
    exact (canonical8475 hH).trans (sound1218 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2815 (3 : Fin 4)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2815 (3 : Fin 4) = raw8483 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2815 raw8483; decide +kernel
    rw [heq]
    exact (canonical8483 hH).trans (sound174 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2815 + (injectiveMoment H (mergeFirst pivotMatrix2815 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2815 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2815 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2815 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2815, value1218, value1312, value174, value982, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound52
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3366_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3366 = Sparse.eval value3366 (momentVector H) := by
  have heq : pivotMatrix3366 = (fun u v => node3366 (pivotPermutation3366 u) v) := by apply Matrix.ext; unfold pivotMatrix3366 node3366 pivotPermutation3366; decide +kernel
  have hmoment : injectiveMoment H node3366 = injectiveMoment H pivotMatrix3366 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3366 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3366 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3366 (0 : Fin 5)) =
      Sparse.eval value2815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3366 (0 : Fin 5) = raw3113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3366 raw3113; decide +kernel
    rw [heq]
    exact (canonical3113 hH).trans (sound2815 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3366 (1 : Fin 5)) =
      Sparse.eval value2521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3366 (1 : Fin 5) = raw6162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3366 raw6162; decide +kernel
    rw [heq]
    exact (canonical6162 hH).trans (sound2521_e hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3366 (2 : Fin 5)) =
      Sparse.eval value2319 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3366 (2 : Fin 5) = raw6233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3366 raw6233; decide +kernel
    rw [heq]
    exact (canonical6233 hH).trans (sound2319 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3366 (3 : Fin 5)) =
      Sparse.eval value2547 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3366 (3 : Fin 5) = raw6235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3366 raw6235; decide +kernel
    rw [heq]
    exact (canonical6235 hH).trans (sound2547_e hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3366 (4 : Fin 5)) =
      Sparse.eval value2548 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3366 (4 : Fin 5) = raw6237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3366 raw6237; decide +kernel
    rw [heq]
    exact (canonical6237 hH).trans (sound2548_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3366 + (injectiveMoment H (mergeFirst pivotMatrix3366 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3366 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3366 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3366 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3366 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3366, value2319, value2521, value2547, value2548, value2815, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3366_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3366_e_oai
