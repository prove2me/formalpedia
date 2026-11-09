-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3215_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T07:50:27.299794+00:00
-- url     : https://prove2.me/submissions/11c5e358-663b-4a5e-b20d-f124efda0b49

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

theorem canonical349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw349 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw349 = injectiveMoment H raw349step0 := by
      have heq : raw349step0 = raw349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw349).symm
    injectiveMoment H raw349step0 = injectiveMoment H raw349step1 := by
      have heq : raw349step1 = (fun i j => raw349step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw349step0 permutation19 permutation5
    _ = injectiveMoment H node212 := by rfl

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

theorem canonical3526 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3526 = injectiveMoment H node1840 := by
  calc
    injectiveMoment H raw3526 = injectiveMoment H raw3526step0 := by
      have heq : raw3526step0 = -raw3526 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3526).symm
    injectiveMoment H raw3526step0 = injectiveMoment H raw3526step1 := by
      have heq : raw3526step1 = (fun i j => raw3526step0 (permutation126 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3526step0 permutation126 permutation21
    _ = injectiveMoment H node1840 := by rfl

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

theorem canonical3674 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3674 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw3674 = injectiveMoment H raw3674step0 := by
      have heq : raw3674step0 = raw3674.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3674).symm
    _ = injectiveMoment H node202 := by rfl

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

theorem canonical3778 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3778 = injectiveMoment H node1246 := by
  calc
    injectiveMoment H raw3778 = injectiveMoment H raw3778step0 := by
      have heq : raw3778step0 = -raw3778 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3778).symm
    injectiveMoment H raw3778step0 = injectiveMoment H raw3778step1 := by
      have heq : raw3778step1 = (fun i j => raw3778step0 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3778step0 permutation27 permutation19
    _ = injectiveMoment H node1246 := by rfl

theorem canonical3786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3786 = injectiveMoment H node2086 := by
  rfl

theorem canonical3791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3791 = injectiveMoment H node617 := by
  rfl

theorem canonical3794 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3794 = injectiveMoment H node1204 := by
  calc
    injectiveMoment H raw3794 = injectiveMoment H raw3794step0 := by
      have heq : raw3794step0 = -raw3794 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3794).symm
    injectiveMoment H raw3794step0 = injectiveMoment H raw3794step1 := by
      have heq : raw3794step1 = (fun i j => raw3794step0 (permutation19 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3794step0 permutation19 permutation16
    _ = injectiveMoment H node1204 := by rfl

theorem canonical3795 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3795 = injectiveMoment H node1745 := by
  calc
    injectiveMoment H raw3795 = injectiveMoment H raw3795step0 := by
      have heq : raw3795step0 = (fun i j => raw3795 (permutation123 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3795 permutation123 permutation19
    _ = injectiveMoment H node1745 := by rfl

theorem canonical3797 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3797 = injectiveMoment H node2073 := by
  calc
    injectiveMoment H raw3797 = injectiveMoment H raw3797step0 := by
      have heq : raw3797step0 = (fun i j => raw3797 (permutation123 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3797 permutation123 permutation20
    _ = injectiveMoment H node2073 := by rfl

theorem canonical3798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3798 = injectiveMoment H node1784 := by
  calc
    injectiveMoment H raw3798 = injectiveMoment H raw3798step0 := by
      have heq : raw3798step0 = (fun i j => raw3798 (permutation123 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3798 permutation123 permutation19
    _ = injectiveMoment H node1784 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3836 = injectiveMoment H node620 := by
  calc
    injectiveMoment H raw3836 = injectiveMoment H raw3836step0 := by
      have heq : raw3836step0 = (fun i j => raw3836 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3836 permutation9 permutation10
    _ = injectiveMoment H node620 := by rfl

theorem canonical3839 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3839 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw3839 = injectiveMoment H raw3839step0 := by
      have heq : raw3839step0 = -raw3839 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3839).symm
    injectiveMoment H raw3839step0 = injectiveMoment H raw3839step1 := by
      have heq : raw3839step1 = (fun i j => raw3839step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3839step0 permutation16 permutation17
    _ = injectiveMoment H node1009 := by rfl

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

theorem canonical3844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3844 = injectiveMoment H node1347 := by
  calc
    injectiveMoment H raw3844 = injectiveMoment H raw3844step0 := by
      have heq : raw3844step0 = raw3844.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3844).symm
    injectiveMoment H raw3844step0 = injectiveMoment H raw3844step1 := by
      have heq : raw3844step1 = (fun i j => raw3844step0 (permutation30 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3844step0 permutation30 permutation28
    _ = injectiveMoment H node1347 := by rfl

theorem canonical3858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3858 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw3858 = injectiveMoment H raw3858step0 := by
      have heq : raw3858step0 = raw3858.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3858).symm
    injectiveMoment H raw3858step0 = injectiveMoment H raw3858step1 := by
      have heq : raw3858step1 = (fun i j => raw3858step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3858step0 permutation19 permutation5
    _ = injectiveMoment H node210 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4196 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4196 = injectiveMoment H raw4196step0 := by
      have heq : raw4196step0 = raw4196.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4196).symm
    injectiveMoment H raw4196step0 = injectiveMoment H raw4196step1 := by
      have heq : raw4196step1 = (fun i j => raw4196step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4196step0 permutation13 permutation3
    _ = injectiveMoment H node203 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5039 = injectiveMoment H node1277 := by
  calc
    injectiveMoment H raw5039 = injectiveMoment H raw5039step0 := by
      have heq : raw5039step0 = raw5039.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5039).symm
    injectiveMoment H raw5039step0 = injectiveMoment H raw5039step1 := by
      have heq : raw5039step1 = (fun i j => raw5039step0 (permutation30 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5039step0 permutation30 permutation28
    _ = injectiveMoment H node1277 := by rfl

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

theorem canonical5786 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5786 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw5786 = injectiveMoment H raw5786step0 := by
      have heq : raw5786step0 = raw5786.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5786).symm
    injectiveMoment H raw5786step0 = injectiveMoment H raw5786step1 := by
      have heq : raw5786step1 = -raw5786step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5786step0).symm
    injectiveMoment H raw5786step1 = injectiveMoment H raw5786step2 := by
      have heq : raw5786step2 = (fun i j => raw5786step1 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5786step1 permutation16 permutation6
    _ = injectiveMoment H node284 := by rfl

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

theorem canonical5837 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5837 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw5837 = injectiveMoment H raw5837step0 := by
      have heq : raw5837step0 = raw5837.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5837).symm
    injectiveMoment H raw5837step0 = injectiveMoment H raw5837step1 := by
      have heq : raw5837step1 = (fun i j => raw5837step0 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5837step0 permutation22 permutation6
    _ = injectiveMoment H node210 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5891 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw5891 = injectiveMoment H raw5891step0 := by
      have heq : raw5891step0 = (fun i j => raw5891 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5891 permutation4 permutation5
    _ = injectiveMoment H node36 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical200
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6418 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6418 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw6418 = injectiveMoment H raw6418step0 := by
      have heq : raw6418step0 = raw6418.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6418).symm
    injectiveMoment H raw6418step0 = injectiveMoment H raw6418step1 := by
      have heq : raw6418step1 = -raw6418step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6418step0).symm
    injectiveMoment H raw6418step1 = injectiveMoment H raw6418step2 := by
      have heq : raw6418step2 = (fun i j => raw6418step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6418step1 permutation22 permutation5
    _ = injectiveMoment H node210 := by rfl

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

theorem canonical6562 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6562 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw6562 = injectiveMoment H raw6562step0 := by
      have heq : raw6562step0 = raw6562.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6562).symm
    injectiveMoment H raw6562step0 = injectiveMoment H raw6562step1 := by
      have heq : raw6562step1 = -raw6562step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6562step0).symm
    injectiveMoment H raw6562step1 = injectiveMoment H raw6562step2 := by
      have heq : raw6562step2 = (fun i j => raw6562step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6562step1 permutation31 permutation3
    _ = injectiveMoment H node230 := by rfl

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

theorem canonical6907 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6907 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw6907 = injectiveMoment H raw6907step0 := by
      have heq : raw6907step0 = raw6907.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6907).symm
    injectiveMoment H raw6907step0 = injectiveMoment H raw6907step1 := by
      have heq : raw6907step1 = -raw6907step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6907step0).symm
    injectiveMoment H raw6907step1 = injectiveMoment H raw6907step2 := by
      have heq : raw6907step2 = (fun i j => raw6907step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6907step1 permutation26 permutation3
    _ = injectiveMoment H node210 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7117 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7117 = injectiveMoment H raw7117step0 := by
      have heq : raw7117step0 = raw7117.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7117).symm
    injectiveMoment H raw7117step0 = injectiveMoment H raw7117step1 := by
      have heq : raw7117step1 = (fun i j => raw7117step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7117step0 permutation28 permutation6
    _ = injectiveMoment H node272 := by rfl

theorem canonical7122 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7122 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw7122 = injectiveMoment H raw7122step0 := by
      have heq : raw7122step0 = raw7122.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7122).symm
    injectiveMoment H raw7122step0 = injectiveMoment H raw7122step1 := by
      have heq : raw7122step1 = -raw7122step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7122step0).symm
    injectiveMoment H raw7122step1 = injectiveMoment H raw7122step2 := by
      have heq : raw7122step2 = (fun i j => raw7122step1 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7122step1 permutation16 permutation5
    _ = injectiveMoment H node209 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7218 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw7218 = injectiveMoment H raw7218step0 := by
      have hz : ∀ i, raw7218 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7218step0 = (fun i j => raw7218 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7218 permutation15 hz
    _ = injectiveMoment H node62 := by rfl

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

theorem canonical7241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7241 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7241 = injectiveMoment H raw7241step0 := by
      have heq : raw7241step0 = raw7241.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7241).symm
    injectiveMoment H raw7241step0 = injectiveMoment H raw7241step1 := by
      have heq : raw7241step1 = (fun i j => raw7241step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7241step0 permutation22 permutation5
    _ = injectiveMoment H node284 := by rfl

theorem canonical7242 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7242 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw7242 = injectiveMoment H raw7242step0 := by
      have heq : raw7242step0 = raw7242.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7242).symm
    injectiveMoment H raw7242step0 = injectiveMoment H raw7242step1 := by
      have heq : raw7242step1 = (fun i j => raw7242step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7242step0 permutation28 permutation6
    _ = injectiveMoment H node287 := by rfl

theorem canonical7245 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7245 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw7245 = injectiveMoment H raw7245step0 := by
      have heq : raw7245step0 = raw7245.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7245).symm
    injectiveMoment H raw7245step0 = injectiveMoment H raw7245step1 := by
      have heq : raw7245step1 = -raw7245step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7245step0).symm
    injectiveMoment H raw7245step1 = injectiveMoment H raw7245step2 := by
      have heq : raw7245step2 = (fun i j => raw7245step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7245step1 permutation29 permutation4
    _ = injectiveMoment H node181 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7453 = injectiveMoment H node64 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7538 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7538 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw7538 = injectiveMoment H raw7538step0 := by
      have heq : raw7538step0 = raw7538.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7538).symm
    injectiveMoment H raw7538step0 = injectiveMoment H raw7538step1 := by
      have heq : raw7538step1 = -raw7538step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7538step0).symm
    injectiveMoment H raw7538step1 = injectiveMoment H raw7538step2 := by
      have heq : raw7538step2 = (fun i j => raw7538step1 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7538step1 permutation20 permutation5
    _ = injectiveMoment H node210 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical245
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7841 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw7841 = injectiveMoment H raw7841step0 := by
      have heq : raw7841step0 = raw7841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7841).symm
    injectiveMoment H raw7841step0 = injectiveMoment H raw7841step1 := by
      have heq : raw7841step1 = (fun i j => raw7841step0 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7841step0 permutation24 permutation7
    _ = injectiveMoment H node287 := by rfl

theorem canonical7869 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7869 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw7869 = injectiveMoment H raw7869step0 := by
      have heq : raw7869step0 = raw7869.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7869).symm
    injectiveMoment H raw7869step0 = injectiveMoment H raw7869step1 := by
      have heq : raw7869step1 = (fun i j => raw7869step0 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7869step0 permutation27 permutation5
    _ = injectiveMoment H node227 := by rfl

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

theorem canonical7895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7895 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7895 = injectiveMoment H raw7895step0 := by
      have hz : ∀ i, raw7895 i (permutation7 0) = 0 := by decide +kernel
      have heq : raw7895step0 = (fun i j => raw7895 i (permutation7 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7895 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7914 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7914 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw7914 = injectiveMoment H raw7914step0 := by
      have heq : raw7914step0 = raw7914.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7914).symm
    injectiveMoment H raw7914step0 = injectiveMoment H raw7914step1 := by
      have heq : raw7914step1 = -raw7914step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7914step0).symm
    injectiveMoment H raw7914step1 = injectiveMoment H raw7914step2 := by
      have heq : raw7914step2 = (fun i j => raw7914step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7914step1 permutation24 permutation3
    _ = injectiveMoment H node261 := by rfl

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

theorem canonical7995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7995 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw7995 = injectiveMoment H raw7995step0 := by
      have heq : raw7995step0 = (fun i j => raw7995 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7995 permutation5 permutation4
    _ = injectiveMoment H node63 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8316 = injectiveMoment H node44 := by
  calc
    injectiveMoment H raw8316 = injectiveMoment H raw8316step0 := by
      have heq : raw8316step0 = -raw8316 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8316).symm
    injectiveMoment H raw8316step0 = injectiveMoment H raw8316step1 := by
      have hz : ∀ i, raw8316step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8316step1 = (fun i j => raw8316step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8316step0 permutation9 hz
    injectiveMoment H raw8316step1 = injectiveMoment H raw8316step2 := by
      have heq : raw8316step2 = (fun i j => raw8316step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8316step1 permutation8 permutation3
    _ = injectiveMoment H node44 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical304
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9750 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw9750 = injectiveMoment H raw9750step0 := by
      have heq : raw9750step0 = raw9750.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9750).symm
    injectiveMoment H raw9750step0 = injectiveMoment H raw9750step1 := by
      have heq : raw9750step1 = -raw9750step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9750step0).symm
    injectiveMoment H raw9750step1 = injectiveMoment H raw9750step2 := by
      have heq : raw9750step2 = (fun i j => raw9750step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9750step1 permutation21 permutation3
    _ = injectiveMoment H node272 := by rfl

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

theorem canonical10000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10000 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw10000 = injectiveMoment H raw10000step0 := by
      have hz : ∀ i, raw10000 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw10000step0 = (fun i j => raw10000 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw10000 permutation3 hz
    injectiveMoment H raw10000step0 = injectiveMoment H raw10000step1 := by
      have heq : raw10000step1 = (fun i j => raw10000step0 (permutation2 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10000step0 permutation2 permutation1
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10098 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw10098 = injectiveMoment H raw10098step0 := by
      have heq : raw10098step0 = raw10098.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10098).symm
    injectiveMoment H raw10098step0 = injectiveMoment H raw10098step1 := by
      have heq : raw10098step1 = (fun i j => raw10098step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10098step0 permutation28 permutation4
    _ = injectiveMoment H node212 := by rfl

theorem canonical10104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10104 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw10104 = injectiveMoment H raw10104step0 := by
      have heq : raw10104step0 = raw10104.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10104).symm
    injectiveMoment H raw10104step0 = injectiveMoment H raw10104step1 := by
      have heq : raw10104step1 = (fun i j => raw10104step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10104step0 permutation27 permutation3
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical317
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10152 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw10152 = injectiveMoment H raw10152step0 := by
      have heq : raw10152step0 = raw10152.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10152).symm
    injectiveMoment H raw10152step0 = injectiveMoment H raw10152step1 := by
      have heq : raw10152step1 = (fun i j => raw10152step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10152step0 permutation30 permutation4
    _ = injectiveMoment H node212 := by rfl

theorem canonical10161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10161 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw10161 = injectiveMoment H raw10161step0 := by
      have heq : raw10161step0 = raw10161.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10161).symm
    injectiveMoment H raw10161step0 = injectiveMoment H raw10161step1 := by
      have heq : raw10161step1 = (fun i j => raw10161step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10161step0 permutation29 permutation3
    _ = injectiveMoment H node226 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1294 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1294 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw1294 = injectiveMoment H raw1294step0 := by
      have heq : raw1294step0 = raw1294.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1294).symm
    injectiveMoment H raw1294step0 = injectiveMoment H raw1294step1 := by
      have heq : raw1294step1 = (fun i j => raw1294step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1294step0 permutation23 permutation20
    _ = injectiveMoment H node1059 := by rfl

theorem canonical1306 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1306 = injectiveMoment H node828 := by
  calc
    injectiveMoment H raw1306 = injectiveMoment H raw1306step0 := by
      have heq : raw1306step0 = raw1306.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1306).symm
    injectiveMoment H raw1306step0 = injectiveMoment H raw1306step1 := by
      have heq : raw1306step1 = (fun i j => raw1306step0 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1306step0 permutation32 permutation26
    _ = injectiveMoment H node828 := by rfl

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

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2283 = injectiveMoment H node1259 := by
  calc
    injectiveMoment H raw2283 = injectiveMoment H raw2283step0 := by
      have heq : raw2283step0 = -raw2283 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2283).symm
    injectiveMoment H raw2283step0 = injectiveMoment H raw2283step1 := by
      have heq : raw2283step1 = (fun i j => raw2283step0 (permutation32 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2283step0 permutation32 permutation17
    _ = injectiveMoment H node1259 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2403 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2403 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw2403 = injectiveMoment H raw2403step0 := by
      have heq : raw2403step0 = raw2403.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2403).symm
    injectiveMoment H raw2403step0 = injectiveMoment H raw2403step1 := by
      have heq : raw2403step1 = -raw2403step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2403step0).symm
    injectiveMoment H raw2403step1 = injectiveMoment H raw2403step2 := by
      have heq : raw2403step2 = (fun i j => raw2403step1 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2403step1 permutation14 permutation24
    _ = injectiveMoment H node1249 := by rfl

theorem canonical2404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2404 = injectiveMoment H node513 := by
  rfl

theorem canonical2406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2406 = injectiveMoment H node838 := by
  calc
    injectiveMoment H raw2406 = injectiveMoment H raw2406step0 := by
      have heq : raw2406step0 = raw2406.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2406).symm
    injectiveMoment H raw2406step0 = injectiveMoment H raw2406step1 := by
      have heq : raw2406step1 = (fun i j => raw2406step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2406step0 permutation30 permutation26
    _ = injectiveMoment H node838 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2434 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw2434 = injectiveMoment H raw2434step0 := by
      have heq : raw2434step0 = raw2434.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2434).symm
    injectiveMoment H raw2434step0 = injectiveMoment H raw2434step1 := by
      have heq : raw2434step1 = -raw2434step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2434step0).symm
    injectiveMoment H raw2434step1 = injectiveMoment H raw2434step2 := by
      have heq : raw2434step2 = (fun i j => raw2434step1 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2434step1 permutation14 permutation24
    _ = injectiveMoment H node1265 := by rfl

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

theorem canonical2471 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2471 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw2471 = injectiveMoment H raw2471step0 := by
      have heq : raw2471step0 = raw2471.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2471).symm
    injectiveMoment H raw2471step0 = injectiveMoment H raw2471step1 := by
      have heq : raw2471step1 = -raw2471step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2471step0).symm
    injectiveMoment H raw2471step1 = injectiveMoment H raw2471step2 := by
      have heq : raw2471step2 = (fun i j => raw2471step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2471step1 permutation14 permutation26
    _ = injectiveMoment H node1058 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2544 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2544 = injectiveMoment H node521 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2578 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw2578 = injectiveMoment H raw2578step0 := by
      have heq : raw2578step0 = raw2578.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2578).symm
    injectiveMoment H raw2578step0 = injectiveMoment H raw2578step1 := by
      have heq : raw2578step1 = (fun i j => raw2578step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2578step0 permutation21 permutation18
    _ = injectiveMoment H node1265 := by rfl

theorem canonical2585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2585 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw2585 = injectiveMoment H raw2585step0 := by
      have heq : raw2585step0 = raw2585.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2585).symm
    injectiveMoment H raw2585step0 = injectiveMoment H raw2585step1 := by
      have heq : raw2585step1 = (fun i j => raw2585step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2585step0 permutation23 permutation20
    _ = injectiveMoment H node1010 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2597 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2597 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw2597 = injectiveMoment H raw2597step0 := by
      have heq : raw2597step0 = raw2597.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2597).symm
    injectiveMoment H raw2597step0 = injectiveMoment H raw2597step1 := by
      have heq : raw2597step1 = -raw2597step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2597step0).symm
    injectiveMoment H raw2597step1 = injectiveMoment H raw2597step2 := by
      have heq : raw2597step2 = (fun i j => raw2597step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2597step1 permutation12 permutation26
    _ = injectiveMoment H node1058 := by rfl

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

theorem canonical2632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2632 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw2632 = injectiveMoment H raw2632step0 := by
      have heq : raw2632step0 = raw2632.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2632).symm
    injectiveMoment H raw2632step0 = injectiveMoment H raw2632step1 := by
      have heq : raw2632step1 = (fun i j => raw2632step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2632step0 permutation28 permutation5
    _ = injectiveMoment H node224 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound64 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node64 = Sparse.eval value64 (momentVector H) := by
  have heq : pivotMatrix64 = (fun u v => node64 (pivotPermutation64 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node64 = injectiveMoment H pivotMatrix64 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix64 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix64 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix64 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix64 (0 : Fin 2) = raw7895 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7895 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix64 (1 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix64 (1 : Fin 2) = raw10000 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical10000 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node64 + (injectiveMoment H (mergeFirst pivotMatrix64 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix64 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value64, value5, Sparse.eval] at hc ⊢
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

theorem sound197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node197 = Sparse.eval value197 (momentVector H) := by
  have hc : momentVector H 23 = injectiveMoment H node197 := rfl
  simp [value197, Sparse.eval, hc]

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

theorem sound209 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node209 = Sparse.eval value209 (momentVector H) := by
  have heq : pivotMatrix209 = (fun u v => node209 (pivotPermutation209 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node209 = injectiveMoment H pivotMatrix209 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix209 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix209 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix209 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix209 (0 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix209 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix209 (1 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix209 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix209 (2 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node209 + (injectiveMoment H (mergeFirst pivotMatrix209 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix209 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix209 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value209, value32, value36, value43, Sparse.eval] at hc ⊢
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

theorem sound224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node224 = Sparse.eval value224 (momentVector H) := by
  have hc : momentVector H 25 = injectiveMoment H node224 := rfl
  simp [value224, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node261 = Sparse.eval value261 (momentVector H) := by
  have heq : pivotMatrix261 = (fun u v => node261 (pivotPermutation261 u) v) := by apply Matrix.ext; unfold pivotMatrix261 node261 pivotPermutation261; decide +kernel
  have hmoment : injectiveMoment H node261 = injectiveMoment H pivotMatrix261 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix261 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix261 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (0 : Fin 3) = raw7995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw7995; decide +kernel
    rw [heq]
    exact (canonical7995 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (1 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (2 : Fin 3) = raw5891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5891; decide +kernel
    rw [heq]
    exact (canonical5891 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node261 + (injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value261, value36, value56, value63, Sparse.eval] at hc ⊢
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

theorem sound287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node287 = Sparse.eval value287 (momentVector H) := by
  have heq : pivotMatrix287 = (fun u v => node287 (pivotPermutation287 u) v) := by apply Matrix.ext; unfold pivotMatrix287 node287 pivotPermutation287; decide +kernel
  have hmoment : injectiveMoment H node287 = injectiveMoment H pivotMatrix287 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix287 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix287 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix287 (0 : Fin 3)) =
      Sparse.eval value64 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (0 : Fin 3) = raw7453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw7453; decide +kernel
    rw [heq]
    exact (canonical7453 hH).trans (sound64 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix287 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (1 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix287 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (2 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node287 + (injectiveMoment H (mergeFirst pivotMatrix287 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix287 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix287 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value287, value61, value62, value64, Sparse.eval] at hc ⊢
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

theorem sound828 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node828 = Sparse.eval value828 (momentVector H) := by
  have heq : pivotMatrix828 = (fun u v => node828.transpose (pivotPermutation828 u) v) := by apply Matrix.ext; unfold pivotMatrix828 node828 pivotPermutation828; decide +kernel
  have hmoment : injectiveMoment H node828 = injectiveMoment H pivotMatrix828 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix828 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix828 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix828 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix828 (0 : Fin 3) = raw349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix828 raw349; decide +kernel
    rw [heq]
    exact (canonical349 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix828 (1 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix828 (1 : Fin 3) = raw3674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix828 raw3674; decide +kernel
    rw [heq]
    exact (canonical3674 hH).trans (sound202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix828 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix828 (2 : Fin 3) = raw3858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix828 raw3858; decide +kernel
    rw [heq]
    exact (canonical3858 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node828 + (injectiveMoment H (mergeFirst pivotMatrix828 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix828 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix828 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value828, value202, value210, value212, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound13
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound838 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node838 = Sparse.eval value838 (momentVector H) := by
  have heq : pivotMatrix838 = (fun u v => node838 (pivotPermutation838 u) v) := by apply Matrix.ext; unfold pivotMatrix838 node838 pivotPermutation838; decide +kernel
  have hmoment : injectiveMoment H node838 = injectiveMoment H pivotMatrix838 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix838 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix838 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix838 (0 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix838 (0 : Fin 3) = raw5837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix838 raw5837; decide +kernel
    rw [heq]
    exact (canonical5837 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix838 (1 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix838 (1 : Fin 3) = raw5786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix838 raw5786; decide +kernel
    rw [heq]
    exact (canonical5786 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix838 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix838 (2 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix838 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node838 + (injectiveMoment H (mergeFirst pivotMatrix838 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix838 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix838 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value838, value210, value229, value284, Sparse.eval] at hc ⊢
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

theorem sound1009 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1009 = Sparse.eval value1009 (momentVector H) := by
  have heq : pivotMatrix1009 = (fun u v => node1009 (pivotPermutation1009 u) v) := by apply Matrix.ext; unfold pivotMatrix1009 node1009 pivotPermutation1009; decide +kernel
  have hmoment : injectiveMoment H node1009 = injectiveMoment H pivotMatrix1009 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1009 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1009 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1009 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1009 (0 : Fin 3) = raw8316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1009 raw8316; decide +kernel
    rw [heq]
    exact (canonical8316 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1009 (1 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1009 (1 : Fin 3) = raw6562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1009 raw6562; decide +kernel
    rw [heq]
    exact (canonical6562 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1009 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1009 (2 : Fin 3) = raw6418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1009 raw6418; decide +kernel
    rw [heq]
    exact (canonical6418 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1009 + (injectiveMoment H (mergeFirst pivotMatrix1009 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1009 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1009 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1009, value210, value230, value44, Sparse.eval] at hc ⊢
  linarith

theorem sound1010 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1010 = Sparse.eval value1010 (momentVector H) := by
  have heq : pivotMatrix1010 = (fun u v => node1010.transpose (pivotPermutation1010 u) v) := by apply Matrix.ext; unfold pivotMatrix1010 node1010 pivotPermutation1010; decide +kernel
  have hmoment : injectiveMoment H node1010 = injectiveMoment H pivotMatrix1010 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1010 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1010 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1010 (0 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1010 (0 : Fin 3) = raw2632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1010 raw2632; decide +kernel
    rw [heq]
    exact (canonical2632 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1010 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1010 (1 : Fin 3) = raw6907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1010 raw6907; decide +kernel
    rw [heq]
    exact (canonical6907 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1010 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1010 (2 : Fin 3) = raw6935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1010 raw6935; decide +kernel
    rw [heq]
    exact (canonical6935 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1010 + (injectiveMoment H (mergeFirst pivotMatrix1010 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1010 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1010 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1010, value203, value210, value224, Sparse.eval] at hc ⊢
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

theorem sound1058 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1058 = Sparse.eval value1058 (momentVector H) := by
  have heq : pivotMatrix1058 = (fun u v => node1058.transpose (pivotPermutation1058 u) v) := by apply Matrix.ext; unfold pivotMatrix1058 node1058 pivotPermutation1058; decide +kernel
  have hmoment : injectiveMoment H node1058 = injectiveMoment H pivotMatrix1058 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1058 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1058 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1058 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1058 (0 : Fin 3) = raw4196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1058 raw4196; decide +kernel
    rw [heq]
    exact (canonical4196 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1058 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1058 (1 : Fin 3) = raw7538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1058 raw7538; decide +kernel
    rw [heq]
    exact (canonical7538 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1058 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1058 (2 : Fin 3) = raw7590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1058 raw7590; decide +kernel
    rw [heq]
    exact (canonical7590 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1058 + (injectiveMoment H (mergeFirst pivotMatrix1058 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1058 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1058 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1058, value203, value210, Sparse.eval] at hc ⊢
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
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1204 = Sparse.eval value1204 (momentVector H) := by
  have heq : pivotMatrix1204 = (fun u v => node1204 (pivotPermutation1204 u) v) := by apply Matrix.ext; unfold pivotMatrix1204 node1204 pivotPermutation1204; decide +kernel
  have hmoment : injectiveMoment H node1204 = injectiveMoment H pivotMatrix1204 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1204 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1204 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1204 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1204 (0 : Fin 3) = raw6331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1204 raw6331; decide +kernel
    rw [heq]
    exact (canonical6331 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1204 (1 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1204 (1 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1204 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1204 (2 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1204 (2 : Fin 3) = raw7122 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1204 raw7122; decide +kernel
    rw [heq]
    exact (canonical7122 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1204 + (injectiveMoment H (mergeFirst pivotMatrix1204 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1204 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1204 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1204, value209, value229, value272, Sparse.eval] at hc ⊢
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

theorem sound1246 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1246 = Sparse.eval value1246 (momentVector H) := by
  have heq : pivotMatrix1246 = (fun u v => node1246 (pivotPermutation1246 u) v) := by apply Matrix.ext; unfold pivotMatrix1246 node1246 pivotPermutation1246; decide +kernel
  have hmoment : injectiveMoment H node1246 = injectiveMoment H pivotMatrix1246 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1246 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1246 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1246 (0 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1246 (0 : Fin 3) = raw7841 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1246 raw7841; decide +kernel
    rw [heq]
    exact (canonical7841 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1246 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1246 (1 : Fin 3) = raw7218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1246 raw7218; decide +kernel
    rw [heq]
    exact (canonical7218 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1246 (2 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1246 (2 : Fin 3) = raw7181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1246 raw7181; decide +kernel
    rw [heq]
    exact (canonical7181 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1246 + (injectiveMoment H (mergeFirst pivotMatrix1246 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1246 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1246 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1246, value230, value287, value62, Sparse.eval] at hc ⊢
  linarith

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

theorem sound1259 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1259 = Sparse.eval value1259 (momentVector H) := by
  have heq : pivotMatrix1259 = (fun u v => node1259 (pivotPermutation1259 u) v) := by apply Matrix.ext; unfold pivotMatrix1259 node1259 pivotPermutation1259; decide +kernel
  have hmoment : injectiveMoment H node1259 = injectiveMoment H pivotMatrix1259 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1259 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1259 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1259 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1259 (0 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1259 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1259 (1 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1259 (1 : Fin 3) = raw7241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1259 raw7241; decide +kernel
    rw [heq]
    exact (canonical7241 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1259 (2 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1259 (2 : Fin 3) = raw7242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1259 raw7242; decide +kernel
    rw [heq]
    exact (canonical7242 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1259 + (injectiveMoment H (mergeFirst pivotMatrix1259 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1259 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1259 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1259, value272, value284, value287, Sparse.eval] at hc ⊢
  linarith

theorem sound1265 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1265 = Sparse.eval value1265 (momentVector H) := by
  have heq : pivotMatrix1265 = (fun u v => node1265 (pivotPermutation1265 u) v) := by apply Matrix.ext; unfold pivotMatrix1265 node1265 pivotPermutation1265; decide +kernel
  have hmoment : injectiveMoment H node1265 = injectiveMoment H pivotMatrix1265 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1265 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1265 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1265 (0 : Fin 3)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1265 (0 : Fin 3) = raw7869 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1265 raw7869; decide +kernel
    rw [heq]
    exact (canonical7869 hH).trans (sound227 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1265 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1265 (1 : Fin 3) = raw7245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1265 raw7245; decide +kernel
    rw [heq]
    exact (canonical7245 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1265 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1265 (2 : Fin 3) = raw7218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1265 raw7218; decide +kernel
    rw [heq]
    exact (canonical7218 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1265 + (injectiveMoment H (mergeFirst pivotMatrix1265 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1265 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1265 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1265, value181, value227, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound1277 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1277 = Sparse.eval value1277 (momentVector H) := by
  have heq : pivotMatrix1277 = (fun u v => node1277.transpose (pivotPermutation1277 u) v) := by apply Matrix.ext; unfold pivotMatrix1277 node1277 pivotPermutation1277; decide +kernel
  have hmoment : injectiveMoment H node1277 = injectiveMoment H pivotMatrix1277 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1277 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1277 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1277 (0 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1277 (0 : Fin 3) = raw7914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1277 raw7914; decide +kernel
    rw [heq]
    exact (canonical7914 hH).trans (sound261 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1277 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1277 (1 : Fin 3) = raw10098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1277 raw10098; decide +kernel
    rw [heq]
    exact (canonical10098 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1277 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1277 (2 : Fin 3) = raw10104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1277 raw10104; decide +kernel
    rw [heq]
    exact (canonical10104 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1277 + (injectiveMoment H (mergeFirst pivotMatrix1277 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1277 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1277 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1277, value212, value229, value261, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound8
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound513 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node513 = Sparse.eval value513 (momentVector H) := by
  have hc : momentVector H 44 = injectiveMoment H node513 := rfl
  simp [value513, Sparse.eval, hc]

theorem sound521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node521 = Sparse.eval value521 (momentVector H) := by
  have hc : momentVector H 48 = injectiveMoment H node521 := rfl
  simp [value521, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound9
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node617 = Sparse.eval value617 (momentVector H) := by
  have hc : momentVector H 191 = injectiveMoment H node617 := rfl
  simp [value617, Sparse.eval, hc]

theorem sound620 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node620 = Sparse.eval value620 (momentVector H) := by
  have hc : momentVector H 21 = injectiveMoment H node620 := rfl
  simp [value620, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound21
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1347 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1347 = Sparse.eval value1347 (momentVector H) := by
  have heq : pivotMatrix1347 = (fun u v => node1347.transpose (pivotPermutation1347 u) v) := by apply Matrix.ext; unfold pivotMatrix1347 node1347 pivotPermutation1347; decide +kernel
  have hmoment : injectiveMoment H node1347 = injectiveMoment H pivotMatrix1347 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1347 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1347 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1347 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1347 (0 : Fin 3) = raw9750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1347 raw9750; decide +kernel
    rw [heq]
    exact (canonical9750 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1347 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1347 (1 : Fin 3) = raw10152 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1347 raw10152; decide +kernel
    rw [heq]
    exact (canonical10152 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1347 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1347 (2 : Fin 3) = raw10161 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1347 raw10161; decide +kernel
    rw [heq]
    exact (canonical10161 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1347 + (injectiveMoment H (mergeFirst pivotMatrix1347 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1347 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1347 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1347, value212, value226, value272, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound27
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1745 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1745 = Sparse.eval value1745 (momentVector H) := by
  have heq : pivotMatrix1745 = (fun u v => node1745 (pivotPermutation1745 u) v) := by apply Matrix.ext; unfold pivotMatrix1745 node1745 pivotPermutation1745; decide +kernel
  have hmoment : injectiveMoment H node1745 = injectiveMoment H pivotMatrix1745 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1745 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1745 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1745 (0 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1745 (0 : Fin 4) = raw1306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1745 raw1306; decide +kernel
    rw [heq]
    exact (canonical1306 hH).trans (sound828 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1745 (1 : Fin 4)) =
      Sparse.eval value1259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1745 (1 : Fin 4) = raw2283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1745 raw2283; decide +kernel
    rw [heq]
    exact (canonical2283 hH).trans (sound1259 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1745 (2 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1745 (2 : Fin 4) = raw2404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1745 raw2404; decide +kernel
    rw [heq]
    exact (canonical2404 hH).trans (sound513 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1745 (3 : Fin 4)) =
      Sparse.eval value838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1745 (3 : Fin 4) = raw2406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1745 raw2406; decide +kernel
    rw [heq]
    exact (canonical2406 hH).trans (sound838 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1745 + (injectiveMoment H (mergeFirst pivotMatrix1745 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1745 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1745 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1745 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1745, value1259, value513, value828, value838, Sparse.eval] at hc ⊢
  linarith

theorem sound1784 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1784 = Sparse.eval value1784 (momentVector H) := by
  have heq : pivotMatrix1784 = (fun u v => node1784 (pivotPermutation1784 u) v) := by apply Matrix.ext; unfold pivotMatrix1784 node1784 pivotPermutation1784; decide +kernel
  have hmoment : injectiveMoment H node1784 = injectiveMoment H pivotMatrix1784 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1784 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1784 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1784 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1784 (0 : Fin 4) = raw2597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1784 raw2597; decide +kernel
    rw [heq]
    exact (canonical2597 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1784 (1 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1784 (1 : Fin 4) = raw2434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1784 raw2434; decide +kernel
    rw [heq]
    exact (canonical2434 hH).trans (sound1265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1784 (2 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1784 (2 : Fin 4) = raw2404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1784 raw2404; decide +kernel
    rw [heq]
    exact (canonical2404 hH).trans (sound513 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1784 (3 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1784 (3 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1784 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1784 + (injectiveMoment H (mergeFirst pivotMatrix1784 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1784 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1784 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1784 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1784, value1058, value1249, value1265, value513, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound28
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1840 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1840 = Sparse.eval value1840 (momentVector H) := by
  have heq : pivotMatrix1840 = (fun u v => node1840 (pivotPermutation1840 u) v) := by apply Matrix.ext; unfold pivotMatrix1840 node1840 pivotPermutation1840; decide +kernel
  have hmoment : injectiveMoment H node1840 = injectiveMoment H pivotMatrix1840 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1840 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1840 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1840 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1840 (0 : Fin 4) = raw1294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1840 raw1294; decide +kernel
    rw [heq]
    exact (canonical1294 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1840 (1 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1840 (1 : Fin 4) = raw2544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1840 raw2544; decide +kernel
    rw [heq]
    exact (canonical2544 hH).trans (sound521 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1840 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1840 (2 : Fin 4) = raw2578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1840 raw2578; decide +kernel
    rw [heq]
    exact (canonical2578 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1840 (3 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1840 (3 : Fin 4) = raw2585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1840 raw2585; decide +kernel
    rw [heq]
    exact (canonical2585 hH).trans (sound1010 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1840 + (injectiveMoment H (mergeFirst pivotMatrix1840 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1840 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1840 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1840 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1840, value1010, value1059, value1265, value521, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound32
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2073 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2073 = Sparse.eval value2073 (momentVector H) := by
  have heq : pivotMatrix2073 = (fun u v => node2073 (pivotPermutation2073 u) v) := by apply Matrix.ext; unfold pivotMatrix2073 node2073 pivotPermutation2073; decide +kernel
  have hmoment : injectiveMoment H node2073 = injectiveMoment H pivotMatrix2073 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2073 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2073 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2073 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2073 (0 : Fin 4) = raw2471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2073 raw2471; decide +kernel
    rw [heq]
    exact (canonical2471 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2073 (1 : Fin 4)) =
      Sparse.eval value1246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2073 (1 : Fin 4) = raw3778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2073 raw3778; decide +kernel
    rw [heq]
    exact (canonical3778 hH).trans (sound1246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2073 (2 : Fin 4)) =
      Sparse.eval value620 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2073 (2 : Fin 4) = raw3836 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2073 raw3836; decide +kernel
    rw [heq]
    exact (canonical3836 hH).trans (sound620 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2073 (3 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2073 (3 : Fin 4) = raw3839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2073 raw3839; decide +kernel
    rw [heq]
    exact (canonical3839 hH).trans (sound1009 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2073 + (injectiveMoment H (mergeFirst pivotMatrix2073 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2073 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2073 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2073 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2073, value1009, value1058, value1246, value620, Sparse.eval] at hc ⊢
  linarith

theorem sound2086 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2086 = Sparse.eval value2086 (momentVector H) := by
  have heq : pivotMatrix2086 = (fun u v => node2086 (pivotPermutation2086 u) v) := by apply Matrix.ext; unfold pivotMatrix2086 node2086 pivotPermutation2086; decide +kernel
  have hmoment : injectiveMoment H node2086 = injectiveMoment H pivotMatrix2086 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2086 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2086 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2086 (0 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2086 (0 : Fin 4) = raw5039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2086 raw5039; decide +kernel
    rw [heq]
    exact (canonical5039 hH).trans (sound1277 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2086 (1 : Fin 4)) =
      Sparse.eval value1347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2086 (1 : Fin 4) = raw3844 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2086 raw3844; decide +kernel
    rw [heq]
    exact (canonical3844 hH).trans (sound1347 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2086 (2 : Fin 4)) =
      Sparse.eval value1204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2086 (2 : Fin 4) = raw3794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2086 raw3794; decide +kernel
    rw [heq]
    exact (canonical3794 hH).trans (sound1204 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2086 (3 : Fin 4)) =
      Sparse.eval value617 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2086 (3 : Fin 4) = raw3791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2086 raw3791; decide +kernel
    rw [heq]
    exact (canonical3791 hH).trans (sound617 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2086 + (injectiveMoment H (mergeFirst pivotMatrix2086 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2086 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2086 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2086 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2086, value1204, value1277, value1347, value617, Sparse.eval] at hc ⊢
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

theorem sound3215_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3215 = Sparse.eval value3215 (momentVector H) := by
  have heq : pivotMatrix3215 = (fun u v => node3215 (pivotPermutation3215 u) v) := by apply Matrix.ext; unfold pivotMatrix3215 node3215 pivotPermutation3215; decide +kernel
  have hmoment : injectiveMoment H node3215 = injectiveMoment H pivotMatrix3215 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3215 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3215 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3215 (0 : Fin 5)) =
      Sparse.eval value1840 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3215 (0 : Fin 5) = raw3526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3215 raw3526; decide +kernel
    rw [heq]
    exact (canonical3526 hH).trans (sound1840 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3215 (1 : Fin 5)) =
      Sparse.eval value2086 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3215 (1 : Fin 5) = raw3786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3215 raw3786; decide +kernel
    rw [heq]
    exact (canonical3786 hH).trans (sound2086 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3215 (2 : Fin 5)) =
      Sparse.eval value1745 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3215 (2 : Fin 5) = raw3795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3215 raw3795; decide +kernel
    rw [heq]
    exact (canonical3795 hH).trans (sound1745 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3215 (3 : Fin 5)) =
      Sparse.eval value2073 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3215 (3 : Fin 5) = raw3797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3215 raw3797; decide +kernel
    rw [heq]
    exact (canonical3797 hH).trans (sound2073 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3215 (4 : Fin 5)) =
      Sparse.eval value1784 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3215 (4 : Fin 5) = raw3798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3215 raw3798; decide +kernel
    rw [heq]
    exact (canonical3798 hH).trans (sound1784 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3215 + (injectiveMoment H (mergeFirst pivotMatrix3215 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3215 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3215 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3215 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3215 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3215, value1745, value1784, value1840, value2073, value2086, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3215_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3215_e_oai
