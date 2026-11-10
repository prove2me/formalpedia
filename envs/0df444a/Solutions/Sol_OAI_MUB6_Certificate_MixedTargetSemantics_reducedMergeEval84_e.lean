-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:51:27.865188+00:00
-- url     : https://prove2.me/submissions/c381c960-4df1-48a9-a4b2-a79c13bda49b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E122
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E138
import Definitions.Def_OAIQ106E139
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval79_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Transitions
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sqrt_six_square : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
  have h : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h

theorem sqrt_six_normSq : Complex.normSq (Real.sqrt 6 : ℂ) = 6 := by
  rw [Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

theorem transition_column_inner (b c d : Basis) (k l : Coord) :
    (∑ i, conj (transition b c i k) * transition b d i l) =
      6 * inner ℂ (c k) (d l) := by
  have hterm (i : Coord) : conj (transition b c i k) * transition b d i l =
      6 * (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by
    simp only [transition, map_mul, Complex.conj_ofReal, inner_conj_symm]
    calc
      _ = (Real.sqrt 6 : ℂ) ^ 2 *
        (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by ring
      _ = _ := by rw [sqrt_six_square]
  simp_rw [hterm]
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

theorem transition_isHadamard {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) : IsHadamard (transition (B r) (B s)) := by
  refine ⟨?_, ?_⟩
  · intro i k
    rw [transition, map_mul, sqrt_six_normSq, hB r s hrs i k]
    norm_num
  · ext i j
    change (∑ k, conj (transition (B r) (B s) k i) * transition (B r) (B s) k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [transition_column_inner, (B s).inner_eq_ite]

theorem transition_reverse (b c : Basis) :
    transition c b = (transition b c).conjTranspose := by
  ext i j
  simp [transition, Matrix.conjTranspose_apply]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem relativeMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : IsHadamard (relativeMatrix B r s) :=
  transition_isHadamard B hB r (r.succAbove s) (r.ne_succAbove s)

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

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_GroupedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit grouping formulas for the two- and three-column equality
patterns. These discharge the dependent finite-label calculations once,
so concrete certificate rows need only ordinary integer arithmetic. -/

open scoped BigOperators
namespace MUB6

theorem groupedColumns_family3_0 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1 + A i 2) := by
  change groupedColumns A (fun _ : Fin 3 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family3_1 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 1) =
      (fun i => ![A i 0 + A i 1, A i 2]) := by
  change groupedColumns A (![0, 0, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_2 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 2) =
      (fun i => ![A i 0 + A i 2, A i 1]) := by
  change groupedColumns A (![0, 1, 0] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_3 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 3) =
      (fun i => ![A i 0, A i 1 + A i 2]) := by
  change groupedColumns A (![0, 1, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_4 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 4) = A := by
  change groupedColumns A (fun j : Fin 3 => j) = _
  ext i b
  simp [groupedColumns, Finset.sum_filter]

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_OrderedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem familyAverage_add (B : Fin 7 → Basis) (F G : CMatrix → ℝ) :
    familyAverage B (fun H => F H + G H) = familyAverage B F + familyAverage B G := by
  simp only [familyAverage, average_add]

theorem familyAverage_mul (B : Fin 7 → Basis) (c : ℝ) (F : CMatrix → ℝ) :
    familyAverage B (fun H => c * F H) = c * familyAverage B F := by
  simp only [familyAverage, average_mul]

theorem relativeMatrix_reverse (B : Fin 7 → Basis) (p : Fin 7 × Coord) :
    relativeMatrix B (reversePair p).1 (reversePair p).2 =
      (relativeMatrix B p.1 p.2).conjTranspose := by
  simp only [relativeMatrix, reversePair, Fin.succAbove_succAbove_predAbove]
  exact transition_reverse _ _

theorem familyAverage_transpose (B : Fin 7 → Basis) (F : CMatrix → ℝ)
    (hF : ∀ H, F (fun i j => conj (H i j)) = F H) :
    familyAverage B (fun H => F H.transpose) = familyAverage B F := by
  change (average (fun r : Fin 7 => average (fun s : Coord => F ((relativeMatrix B r s).transpose)))) =
    average (fun r : Fin 7 => average (fun s : Coord => F (relativeMatrix B r s)))
  rw [← average_prod (fun p : Fin 7 × Coord => F ((relativeMatrix B p.1 p.2).transpose)),
    ← average_prod (fun p : Fin 7 × Coord => F (relativeMatrix B p.1 p.2))]
  have h (p : Fin 7 × Coord) :
      F ((relativeMatrix B p.1 p.2).transpose) =
        F (relativeMatrix B (reversePair p).1 (reversePair p).2) := by
    rw [relativeMatrix_reverse]
    exact (hF ((relativeMatrix B p.1 p.2).transpose)).symm
  simp_rw [h]
  exact average_equiv reversePairEquiv (fun p => F (relativeMatrix B p.1 p.2))

theorem rowFourier_conjugate {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier (fun i j => conj (H i j)) ρ a = conj (rowFourier H ρ a) := by
  simp only [rowFourier, map_mul, map_sum, map_prod, map_zpow₀, map_inv₀, map_ofNat]

theorem unorientedRowProducts_conjugate {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    unorientedRowProducts (fun i j => conj (H i j)) A = unorientedRowProducts H A := by
  apply average_congr
  intro ρ
  simp only [rowFourier_conjugate, ← map_prod, Complex.conj_re]

theorem averagedRowProducts_split {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    averagedRowProducts H A =
      (1 / 2 : ℝ) * unorientedRowProducts H A +
        (1 / 2 : ℝ) * unorientedRowProducts H.transpose A := by
  have h (ρ : Fin p ↪ Coord) :
      ((∏ j, rowFourier H ρ (fun i => A i j)).re +
        (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (1 / 2 : ℝ) * (∏ j, rowFourier H ρ (fun i => A i j)).re +
        (1 / 2 : ℝ) * (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re := by ring
  simp only [averagedRowProducts, h, average_add, average_mul, unorientedRowProducts]

theorem familyAverage_averagedRowProducts {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    familyAverage B (fun H => averagedRowProducts H A) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  simp only [averagedRowProducts_split, familyAverage_add, familyAverage_mul]
  rw [familyAverage_transpose B (fun H => unorientedRowProducts H A)
    (fun H => unorientedRowProducts_conjugate H A)]
  ring

theorem mixedMoment_single_label {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) :
      average (fun τ : Fin 1 ↪ Coord =>
        (mixedIntegrand B A (fun _ => (0 : Fin 1)) r ρ τ).re) =
      average (fun s : Coord => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re) := by
    exact average_equiv singletonEmbeddingEquiv
      (fun s => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re)
  simp_rw [h]
  exact average_comm _

/-- Single-label mixed moments expand into the manuscript's transpose-averaged
pair moments with the exact falling-factorial weights. -/
theorem mixedMoment_single_label_partition {p n : ℕ} {P : Type*} [Fintype P]
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        familyPairMoment B (groupedColumns A (F.label s)) := by
  rw [mixedMoment_single_label, ← familyAverage_averagedRowProducts]
  unfold familyAverage
  simp_rw [averagedRowProducts_partition (relativeMatrix_isHadamard B hB _ _) A F cover,
    average_sum, average_mul]
  rfl

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

theorem familyPairMoment_of_pointwise {p n : ℕ} (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ) (v : Sparse (Fin 909))
    (h : ∀ H, IsHadamard H →
      injectiveMoment H A = Sparse.eval v (PairSemantics.momentVector H)) :
    familyPairMoment B A = Sparse.eval v (familyPairVector B) := by
  rw [eval_familyPairVector]
  unfold familyPairMoment familyAverage
  apply average_congr
  intro r
  apply average_congr
  intro s
  exact h _ (relativeMatrix_isHadamard B hB r s)

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleRules
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

/-- The five equality patterns for three sampled column indices. -/
theorem single_label_three {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 3) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family3 EqualityPatterns.covers3
  rw [sum_fin_five] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3,
    EqualityPatterns.blocks3, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Nat.descFactorial] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5125 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5125 = injectiveMoment H raw5125step0 := by
      have hz : ∀ j, raw5125 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5125step0 = (fun i j => raw5125 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5125 permutation104 hz
    injectiveMoment H raw5125step0 = injectiveMoment H raw5125step1 := by
      have hz : ∀ j, raw5125step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5125step1 = (fun i j => raw5125step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5125step0 permutation21 hz
    injectiveMoment H raw5125step1 = injectiveMoment H raw5125step2 := by
      have heq : raw5125step2 = (fun i j => raw5125step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5125step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical5128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5128 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5128 = injectiveMoment H raw5128step0 := by
      have hz : ∀ j, raw5128 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5128step0 = (fun i j => raw5128 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5128 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

theorem canonical5132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5132 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5132 = injectiveMoment H raw5132step0 := by
      have hz : ∀ j, raw5132 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5132step0 = (fun i j => raw5132 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5132 permutation21 hz
    injectiveMoment H raw5132step0 = injectiveMoment H raw5132step1 := by
      have heq : raw5132step1 = (fun i j => raw5132step0 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5132step0 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical5136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5136 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5136 = injectiveMoment H raw5136step0 := by
      have hz : ∀ j, raw5136 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5136step0 = (fun i j => raw5136 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5136 permutation104 hz
    _ = injectiveMoment H node46 := by rfl

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

theorem canonical5147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5147 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5147 = injectiveMoment H raw5147step0 := by
      have hz : ∀ j, raw5147 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5147step0 = (fun i j => raw5147 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5147 permutation104 hz
    injectiveMoment H raw5147step0 = injectiveMoment H raw5147step1 := by
      have heq : raw5147step1 = (fun i j => raw5147step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5147step0 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5159 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5159 = injectiveMoment H raw5159step0 := by
      have hz : ∀ j, raw5159 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5159step0 = (fun i j => raw5159 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5159 permutation57 hz
    injectiveMoment H raw5159step0 = injectiveMoment H raw5159step1 := by
      have heq : raw5159step1 = (fun i j => raw5159step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5159step0 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

theorem canonical5170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5170 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5170 = injectiveMoment H raw5170step0 := by
      have hz : ∀ j, raw5170 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5170step0 = (fun i j => raw5170 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5170 permutation128 hz
    injectiveMoment H raw5170step0 = injectiveMoment H raw5170step1 := by
      have hz : ∀ j, raw5170step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5170step1 = (fun i j => raw5170step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5170step0 permutation21 hz
    injectiveMoment H raw5170step1 = injectiveMoment H raw5170step2 := by
      have hz : ∀ j, raw5170step1 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5170step2 = (fun i j => raw5170step1 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5170step1 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

theorem canonical5179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5179 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5179 = injectiveMoment H raw5179step0 := by
      have hz : ∀ j, raw5179 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5179step0 = (fun i j => raw5179 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5179 permutation128 hz
    injectiveMoment H raw5179step0 = injectiveMoment H raw5179step1 := by
      have hz : ∀ j, raw5179step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5179step1 = (fun i j => raw5179step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5179step0 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5182 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5182 = injectiveMoment H raw5182step0 := by
      have hz : ∀ j, raw5182 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5182step0 = (fun i j => raw5182 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5182 permutation57 hz
    injectiveMoment H raw5182step0 = injectiveMoment H raw5182step1 := by
      have heq : raw5182step1 = (fun i j => raw5182step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5182step0 permutation13 permutation1
    _ = injectiveMoment H node46 := by rfl

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem canonical5185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5185 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5185 = injectiveMoment H raw5185step0 := by
      have hz : ∀ j, raw5185 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5185step0 = (fun i j => raw5185 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185 permutation27 hz
    injectiveMoment H raw5185step0 = injectiveMoment H raw5185step1 := by
      have hz : ∀ j, raw5185step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5185step1 = (fun i j => raw5185step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
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

theorem canonical7980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7980 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7980 = injectiveMoment H raw7980step0 := by
      have hz : ∀ j, raw7980 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7980step0 = (fun i j => raw7980 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980 permutation27 hz
    injectiveMoment H raw7980step0 = injectiveMoment H raw7980step1 := by
      have hz : ∀ j, raw7980step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7980step1 = (fun i j => raw7980step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step0 permutation7 hz
    injectiveMoment H raw7980step1 = injectiveMoment H raw7980step2 := by
      have hz : ∀ j, raw7980step1 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7980step2 = (fun i j => raw7980step1 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step1 permutation2 hz
    injectiveMoment H raw7980step2 = injectiveMoment H raw7980step3 := by
      have hz : ∀ j, raw7980step2 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7980step3 = (fun i j => raw7980step2 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step2 permutation0 hz
    injectiveMoment H raw7980step3 = injectiveMoment H raw7980step4 := by
      have hz : ∀ i, raw7980step3 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7980step4 = (fun i j => raw7980step3 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7980step3 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

theorem canonical7981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7981 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7981 = injectiveMoment H raw7981step0 := by
      have hz : ∀ j, raw7981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7981step0 = (fun i j => raw7981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981 permutation128 hz
    injectiveMoment H raw7981step0 = injectiveMoment H raw7981step1 := by
      have hz : ∀ j, raw7981step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7981step1 = (fun i j => raw7981step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step0 permutation27 hz
    injectiveMoment H raw7981step1 = injectiveMoment H raw7981step2 := by
      have hz : ∀ j, raw7981step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7981step2 = (fun i j => raw7981step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step1 permutation7 hz
    injectiveMoment H raw7981step2 = injectiveMoment H raw7981step3 := by
      have hz : ∀ j, raw7981step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7981step3 = (fun i j => raw7981step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step2 permutation2 hz
    injectiveMoment H raw7981step3 = injectiveMoment H raw7981step4 := by
      have hz : ∀ j, raw7981step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7981step4 = (fun i j => raw7981step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step3 permutation0 hz
    injectiveMoment H raw7981step4 = injectiveMoment H raw7981step5 := by
      have hz : ∀ i, raw7981step4 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7981step5 = (fun i j => raw7981step4 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7981step4 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw141 = injectiveMoment H node352 := by
  calc
    injectiveMoment H raw141 = injectiveMoment H raw141step0 := by
      have heq : raw141step0 = (fun i j => raw141 (permutation150 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw141 permutation150 permutation8
    _ = injectiveMoment H node352 := by rfl

theorem canonical142 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw142 = injectiveMoment H node434 := by
  calc
    injectiveMoment H raw142 = injectiveMoment H raw142step0 := by
      have heq : raw142step0 = -raw142 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw142).symm
    injectiveMoment H raw142step0 = injectiveMoment H raw142step1 := by
      have heq : raw142step1 = (fun i j => raw142step0 (permutation37 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw142step0 permutation37 permutation6
    _ = injectiveMoment H node434 := by rfl

theorem canonical145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw145 = injectiveMoment H node430 := by
  calc
    injectiveMoment H raw145 = injectiveMoment H raw145step0 := by
      have heq : raw145step0 = -raw145 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw145).symm
    injectiveMoment H raw145step0 = injectiveMoment H raw145step1 := by
      have heq : raw145step1 = (fun i j => raw145step0 (permutation34 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw145step0 permutation34 permutation6
    _ = injectiveMoment H node430 := by rfl

theorem canonical147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw147 = injectiveMoment H node139 := by
  calc
    injectiveMoment H raw147 = injectiveMoment H raw147step0 := by
      have heq : raw147step0 = (fun i j => raw147 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw147 permutation32 permutation6
    _ = injectiveMoment H node139 := by rfl

theorem canonical148 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw148 = injectiveMoment H node417 := by
  calc
    injectiveMoment H raw148 = injectiveMoment H raw148step0 := by
      have heq : raw148step0 = -raw148 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw148).symm
    injectiveMoment H raw148step0 = injectiveMoment H raw148step1 := by
      have heq : raw148step1 = (fun i j => raw148step0 (permutation36 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw148step0 permutation36 permutation8
    _ = injectiveMoment H node417 := by rfl

theorem canonical149 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw149 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw149 = injectiveMoment H raw149step0 := by
      have heq : raw149step0 = -raw149 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw149).symm
    injectiveMoment H raw149step0 = injectiveMoment H raw149step1 := by
      have heq : raw149step1 = (fun i j => raw149step0 (permutation10 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw149step0 permutation10 permutation6
    _ = injectiveMoment H node141 := by rfl

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

theorem canonical189 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw189 = injectiveMoment H node68 := by
  rfl

theorem canonical190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw190 = injectiveMoment H node14 := by
  rfl

theorem canonical191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw191 = injectiveMoment H node15 := by
  rfl

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

theorem canonical199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw199 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw199 = injectiveMoment H raw199step0 := by
      have hz : ∀ j, raw199 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw199step0 = (fun i j => raw199 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw199 permutation15 hz
    _ = injectiveMoment H node9 := by rfl

theorem canonical200 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw200 = injectiveMoment H node2 := by
  calc
    injectiveMoment H raw200 = injectiveMoment H raw200step0 := by
      have hz : ∀ j, raw200 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw200step0 = (fun i j => raw200 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw200 permutation5 hz
    _ = injectiveMoment H node2 := by rfl

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

theorem canonical210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw210 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw210 = injectiveMoment H raw210step0 := by
      have heq : raw210step0 = (fun i j => raw210 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw210 permutation10 permutation1
    _ = injectiveMoment H node16 := by rfl

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

theorem canonical34 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw34 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw34 = injectiveMoment H raw34step0 := by
      have heq : raw34step0 = raw34.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw34).symm
    _ = injectiveMoment H node7 := by rfl

theorem canonical47 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw47 = injectiveMoment H node13 := by
  rfl

theorem canonical48 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw48 = injectiveMoment H node6 := by
  rfl

theorem canonical51 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw51 = injectiveMoment H node7 := by
  rfl

theorem canonical52 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw52 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw52 = injectiveMoment H raw52step0 := by
      have heq : raw52step0 = (fun i j => raw52 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw52 permutation4 permutation1
    _ = injectiveMoment H node7 := by rfl

theorem canonical53 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw53 = injectiveMoment H node1 := by
  rfl

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

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

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

theorem canonical940 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw940 = injectiveMoment H node120 := by
  rfl

theorem canonical946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw946 = injectiveMoment H node48 := by
  calc
    injectiveMoment H raw946 = injectiveMoment H raw946step0 := by
      have heq : raw946step0 = raw946.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw946).symm
    injectiveMoment H raw946step0 = injectiveMoment H raw946step1 := by
      have heq : raw946step1 = (fun i j => raw946step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw946step0 permutation7 permutation6
    _ = injectiveMoment H node48 := by rfl

theorem canonical953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw953 = injectiveMoment H node127 := by
  rfl

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

theorem sound1 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node1 = Sparse.eval value1 (momentVector H) := by
  have hc : momentVector H 58 = injectiveMoment H node1 := rfl
  simp [value1, Sparse.eval, hc]

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

theorem sound6 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node6 = Sparse.eval value6 (momentVector H) := by
  have heq : pivotMatrix6 = (fun u v => node6 (pivotPermutation6 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node6 = injectiveMoment H pivotMatrix6 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix6 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix6 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix6 (0 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix6 (0 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix6 (1 : Fin 2)) =
      Sparse.eval value1 (momentVector H) := by
    have heq : mergeFirst pivotMatrix6 (1 : Fin 2) = raw53 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical53 hH).trans (sound1 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node6 + (injectiveMoment H (mergeFirst pivotMatrix6 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix6 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value6, value1, value2, Sparse.eval] at hc ⊢
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

theorem sound13 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node13 = Sparse.eval value13 (momentVector H) := by
  have heq : pivotMatrix13 = (fun u v => node13 (pivotPermutation13 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node13 = injectiveMoment H pivotMatrix13 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix13 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix13 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix13 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix13 (0 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix13 (1 : Fin 3)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix13 (1 : Fin 3) = raw52 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical52 hH).trans (sound7 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix13 (2 : Fin 3)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix13 (2 : Fin 3) = raw51 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical51 hH).trans (sound7 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node13 + (injectiveMoment H (mergeFirst pivotMatrix13 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix13 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix13 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value13, value7, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound14 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node14 = Sparse.eval value14 (momentVector H) := by
  have heq : pivotMatrix14 = (fun u v => node14 (pivotPermutation14 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node14 = injectiveMoment H pivotMatrix14 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix14 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix14 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix14 (0 : Fin 3)) =
      Sparse.eval value6 (momentVector H) := by
    have heq : mergeFirst pivotMatrix14 (0 : Fin 3) = raw48 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical48 hH).trans (sound6 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix14 (1 : Fin 3)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix14 (1 : Fin 3) = raw200 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical200 hH).trans (sound2 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix14 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix14 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node14 + (injectiveMoment H (mergeFirst pivotMatrix14 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix14 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix14 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value14, value2, value6, value8, Sparse.eval] at hc ⊢
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

theorem sound16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node16 = Sparse.eval value16 (momentVector H) := by
  have heq : pivotMatrix16 = (fun u v => node16 (pivotPermutation16 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node16 = injectiveMoment H pivotMatrix16 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix16 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix16 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (1 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node16 + (injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value16, value10, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound17 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node17 = Sparse.eval value17 (momentVector H) := by
  have hc : momentVector H 257 = injectiveMoment H node17 := rfl
  simp [value17, Sparse.eval, hc]

theorem sound20 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node20 = Sparse.eval value20 (momentVector H) := by
  have hc : momentVector H 67 = injectiveMoment H node20 := rfl
  simp [value20, Sparse.eval, hc]

theorem sound27 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node27 = Sparse.eval value27 (momentVector H) := by
  have hc : momentVector H 69 = injectiveMoment H node27 := rfl
  simp [value27, Sparse.eval, hc]

theorem sound28 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node28 = Sparse.eval value28 (momentVector H) := by
  have hc : momentVector H 70 = injectiveMoment H node28 := rfl
  simp [value28, Sparse.eval, hc]

theorem sound30 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node30 = Sparse.eval value30 (momentVector H) := by
  have hc : momentVector H 71 = injectiveMoment H node30 := rfl
  simp [value30, Sparse.eval, hc]

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

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound48 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node48 = Sparse.eval value48 (momentVector H) := by
  have heq : pivotMatrix48 = (fun u v => node48.transpose (pivotPermutation48 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node48 = injectiveMoment H pivotMatrix48 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix48 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix48 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix48 (0 : Fin 2)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix48 (0 : Fin 2) = raw34 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical34 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix48 (1 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix48 (1 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node48 + (injectiveMoment H (mergeFirst pivotMatrix48 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix48 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value48, value7, value9, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical572 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw572 = injectiveMoment H node17 := by
  calc
    injectiveMoment H raw572 = injectiveMoment H raw572step0 := by
      have heq : raw572step0 = -raw572 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw572).symm
    injectiveMoment H raw572step0 = injectiveMoment H raw572step1 := by
      have heq : raw572step1 = (fun i j => raw572step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw572step0 permutation7 permutation5
    _ = injectiveMoment H node17 := by rfl

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

theorem canonical577 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw577 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw577 = injectiveMoment H raw577step0 := by
      have heq : raw577step0 = -raw577 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw577).symm
    injectiveMoment H raw577step0 = injectiveMoment H raw577step1 := by
      have heq : raw577step1 = (fun i j => raw577step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw577step0 permutation7 permutation5
    _ = injectiveMoment H node32 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical708 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw708 = injectiveMoment H node102 := by
  rfl

theorem canonical711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw711 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw711 = injectiveMoment H raw711step0 := by
      have heq : raw711step0 = (fun i j => raw711 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw711 permutation17 permutation5
    _ = injectiveMoment H node209 := by rfl

theorem canonical719 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw719 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw719 = injectiveMoment H raw719step0 := by
      have heq : raw719step0 = raw719.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw719).symm
    injectiveMoment H raw719step0 = injectiveMoment H raw719step1 := by
      have heq : raw719step1 = -raw719step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw719step0).symm
    injectiveMoment H raw719step1 = injectiveMoment H raw719step2 := by
      have heq : raw719step2 = (fun i j => raw719step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw719step1 permutation7 permutation5
    _ = injectiveMoment H node32 := by rfl

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

theorem canonical801 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw801 = injectiveMoment H node20 := by
  rfl

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

theorem canonical964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw964 = injectiveMoment H node30 := by
  calc
    injectiveMoment H raw964 = injectiveMoment H raw964step0 := by
      have heq : raw964step0 = (fun i j => raw964 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw964 permutation4 permutation3
    _ = injectiveMoment H node30 := by rfl

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

theorem canonical1409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1409 = injectiveMoment H node146 := by
  rfl

theorem canonical1417 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1417 = injectiveMoment H node150 := by
  rfl

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

theorem canonical1426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1426 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw1426 = injectiveMoment H raw1426step0 := by
      have heq : raw1426step0 = (fun i j => raw1426 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1426 permutation11 permutation3
    _ = injectiveMoment H node146 := by rfl

theorem canonical1432 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1432 = injectiveMoment H node153 := by
  rfl

theorem canonical1433 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1433 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw1433 = injectiveMoment H raw1433step0 := by
      have heq : raw1433step0 = (fun i j => raw1433 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1433 permutation12 permutation5
    _ = injectiveMoment H node145 := by rfl

theorem canonical1434 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1434 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw1434 = injectiveMoment H raw1434step0 := by
      have heq : raw1434step0 = (fun i j => raw1434 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1434 permutation10 permutation3
    _ = injectiveMoment H node153 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical239 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw239 = injectiveMoment H node74 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound68 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node68 = Sparse.eval value68 (momentVector H) := by
  have heq : pivotMatrix68 = (fun u v => node68 (pivotPermutation68 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node68 = injectiveMoment H pivotMatrix68 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix68 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix68 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix68 (0 : Fin 4)) =
      Sparse.eval value13 (momentVector H) := by
    have heq : mergeFirst pivotMatrix68 (0 : Fin 4) = raw47 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical47 hH).trans (sound13 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix68 (1 : Fin 4)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix68 (1 : Fin 4) = raw199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical199 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix68 (2 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix68 (2 : Fin 4) = raw208 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical208 hH).trans (sound16 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix68 (3 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix68 (3 : Fin 4) = raw210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical210 hH).trans (sound16 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node68 + (injectiveMoment H (mergeFirst pivotMatrix68 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix68 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix68 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix68 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value68, value13, value16, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound74 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node74 = Sparse.eval value74 (momentVector H) := by
  have hc : momentVector H 256 = injectiveMoment H node74 := rfl
  simp [value74, Sparse.eval, hc]

theorem sound94 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node94 = Sparse.eval value94 (momentVector H) := by
  have heq : pivotMatrix94 = (fun u v => node94 (pivotPermutation94 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node94 = injectiveMoment H pivotMatrix94 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix94 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix94 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix94 (0 : Fin 3)) =
      Sparse.eval value20 (momentVector H) := by
    have heq : mergeFirst pivotMatrix94 (0 : Fin 3) = raw801 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical801 hH).trans (sound20 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix94 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix94 (1 : Fin 3) = raw577 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical577 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix94 (2 : Fin 3)) =
      Sparse.eval value17 (momentVector H) := by
    have heq : mergeFirst pivotMatrix94 (2 : Fin 3) = raw572 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical572 hH).trans (sound17 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node94 + (injectiveMoment H (mergeFirst pivotMatrix94 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix94 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix94 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value94, value17, value20, value32, Sparse.eval] at hc ⊢
  linarith

theorem sound102 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node102 = Sparse.eval value102 (momentVector H) := by
  have heq : pivotMatrix102 = (fun u v => node102 (pivotPermutation102 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node102 = injectiveMoment H pivotMatrix102 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix102 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix102 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix102 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix102 (0 : Fin 3) = raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4048 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix102 (1 : Fin 3)) =
      Sparse.eval value20 (momentVector H) := by
    have heq : mergeFirst pivotMatrix102 (1 : Fin 3) = raw801 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical801 hH).trans (sound20 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix102 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix102 (2 : Fin 3) = raw719 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical719 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node102 + (injectiveMoment H (mergeFirst pivotMatrix102 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix102 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix102 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value102, value20, value31, value32, Sparse.eval] at hc ⊢
  linarith

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

theorem sound127 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node127 = Sparse.eval value127 (momentVector H) := by
  have heq : pivotMatrix127 = (fun u v => node127 (pivotPermutation127 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node127 = injectiveMoment H pivotMatrix127 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix127 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix127 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix127 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix127 (0 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix127 (1 : Fin 3)) =
      Sparse.eval value30 (momentVector H) := by
    have heq : mergeFirst pivotMatrix127 (1 : Fin 3) = raw964 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical964 hH).trans (sound30 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix127 (2 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix127 (2 : Fin 3) = raw955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical955 hH).trans (sound27 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node127 + (injectiveMoment H (mergeFirst pivotMatrix127 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix127 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix127 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value127, value27, value30, value52, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1353 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1353 = injectiveMoment H node134 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1384 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw1384 = injectiveMoment H raw1384step0 := by
      have hz : ∀ j, raw1384 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw1384step0 = (fun i j => raw1384 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1384 permutation15 hz
    _ = injectiveMoment H node31 := by rfl

theorem canonical1389 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1389 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw1389 = injectiveMoment H raw1389step0 := by
      have heq : raw1389step0 = raw1389.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1389).symm
    injectiveMoment H raw1389step0 = injectiveMoment H raw1389step1 := by
      have hz : ∀ i, raw1389step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw1389step1 = (fun i j => raw1389step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1389step0 permutation5 hz
    injectiveMoment H raw1389step1 = injectiveMoment H raw1389step2 := by
      have heq : raw1389step2 = (fun i j => raw1389step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1389step1 permutation7 permutation2
    _ = injectiveMoment H node9 := by rfl

theorem canonical1403 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1403 = injectiveMoment H node145 := by
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

theorem sound139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node139 = Sparse.eval value139 (momentVector H) := by
  have heq : pivotMatrix139 = (fun u v => node139 (pivotPermutation139 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node139 = injectiveMoment H pivotMatrix139 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix139 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix139 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix139 (0 : Fin 3)) =
      Sparse.eval value48 (momentVector H) := by
    have heq : mergeFirst pivotMatrix139 (0 : Fin 3) = raw946 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical946 hH).trans (sound48 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix139 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix139 (1 : Fin 3) = raw1389 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1389 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix139 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix139 (2 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node139 + (injectiveMoment H (mergeFirst pivotMatrix139 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix139 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix139 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value139, value48, value52, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound141 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node141 = Sparse.eval value141 (momentVector H) := by
  have heq : pivotMatrix141 = (fun u v => node141 (pivotPermutation141 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node141 = injectiveMoment H pivotMatrix141 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix141 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix141 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix141 (0 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix141 (0 : Fin 3) = raw958 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical958 hH).trans (sound28 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix141 (1 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix141 (1 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix141 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix141 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node141 + (injectiveMoment H (mergeFirst pivotMatrix141 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix141 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix141 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value141, value28, value31, value32, Sparse.eval] at hc ⊢
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

theorem canonical480 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw480 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw480 = injectiveMoment H raw480step0 := by
      have heq : raw480step0 = -raw480 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw480).symm
    injectiveMoment H raw480step0 = injectiveMoment H raw480step1 := by
      have heq : raw480step1 = (fun i j => raw480step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw480step0 permutation31 permutation5
    _ = injectiveMoment H node141 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw687 = injectiveMoment H node94 := by
  calc
    injectiveMoment H raw687 = injectiveMoment H raw687step0 := by
      have heq : raw687step0 = (fun i j => raw687 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw687 permutation17 permutation5
    _ = injectiveMoment H node94 := by rfl

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

theorem sound352 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node352 = Sparse.eval value352 (momentVector H) := by
  have heq : pivotMatrix352 = (fun u v => node352 (pivotPermutation352 u) v) := by apply Matrix.ext; unfold pivotMatrix352 node352 pivotPermutation352; decide +kernel
  have hmoment : injectiveMoment H node352 = injectiveMoment H pivotMatrix352 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix352 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix352 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix352 (0 : Fin 4)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix352 (0 : Fin 4) = raw480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix352 raw480; decide +kernel
    rw [heq]
    exact (canonical480 hH).trans (sound141 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix352 (1 : Fin 4)) =
      Sparse.eval value94 (momentVector H) := by
    have heq : mergeFirst pivotMatrix352 (1 : Fin 4) = raw687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix352 raw687; decide +kernel
    rw [heq]
    exact (canonical687 hH).trans (sound94 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix352 (2 : Fin 4)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix352 (2 : Fin 4) = raw708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix352 raw708; decide +kernel
    rw [heq]
    exact (canonical708 hH).trans (sound102 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix352 (3 : Fin 4)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix352 (3 : Fin 4) = raw711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix352 raw711; decide +kernel
    rw [heq]
    exact (canonical711 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node352 + (injectiveMoment H (mergeFirst pivotMatrix352 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix352 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix352 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix352 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value352, value102, value141, value209, value94, Sparse.eval] at hc ⊢
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

theorem sound417 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node417 = Sparse.eval value417 (momentVector H) := by
  have heq : pivotMatrix417 = (fun u v => node417 (pivotPermutation417 u) v) := by apply Matrix.ext; unfold pivotMatrix417 node417 pivotPermutation417; decide +kernel
  have hmoment : injectiveMoment H node417 = injectiveMoment H pivotMatrix417 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix417 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix417 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix417 (0 : Fin 4)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix417 (0 : Fin 4) = raw239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix417 raw239; decide +kernel
    rw [heq]
    exact (canonical239 hH).trans (sound74 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix417 (1 : Fin 4)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix417 (1 : Fin 4) = raw1353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix417 raw1353; decide +kernel
    rw [heq]
    exact (canonical1353 hH).trans (sound134 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix417 (2 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix417 (2 : Fin 4) = raw1426 := by apply Matrix.ext; unfold mergeFirst pivotMatrix417 raw1426; decide +kernel
    rw [heq]
    exact (canonical1426 hH).trans (sound146 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix417 (3 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix417 (3 : Fin 4) = raw1434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix417 raw1434; decide +kernel
    rw [heq]
    exact (canonical1434 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node417 + (injectiveMoment H (mergeFirst pivotMatrix417 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix417 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix417 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix417 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value417, value134, value146, value153, value74, Sparse.eval] at hc ⊢
  linarith

theorem sound430 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node430 = Sparse.eval value430 (momentVector H) := by
  have heq : pivotMatrix430 = (fun u v => node430 (pivotPermutation430 u) v) := by apply Matrix.ext; unfold pivotMatrix430 node430 pivotPermutation430; decide +kernel
  have hmoment : injectiveMoment H node430 = injectiveMoment H pivotMatrix430 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix430 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix430 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix430 (0 : Fin 4)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix430 (0 : Fin 4) = raw940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix430 raw940; decide +kernel
    rw [heq]
    exact (canonical940 hH).trans (sound120 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix430 (1 : Fin 4)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix430 (1 : Fin 4) = raw1384 := by apply Matrix.ext; unfold mergeFirst pivotMatrix430 raw1384; decide +kernel
    rw [heq]
    exact (canonical1384 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix430 (2 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix430 (2 : Fin 4) = raw1403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix430 raw1403; decide +kernel
    rw [heq]
    exact (canonical1403 hH).trans (sound145 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix430 (3 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix430 (3 : Fin 4) = raw1409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix430 raw1409; decide +kernel
    rw [heq]
    exact (canonical1409 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node430 + (injectiveMoment H (mergeFirst pivotMatrix430 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix430 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix430 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix430 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value430, value120, value145, value146, value31, Sparse.eval] at hc ⊢
  linarith

theorem sound434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node434 = Sparse.eval value434 (momentVector H) := by
  have heq : pivotMatrix434 = (fun u v => node434 (pivotPermutation434 u) v) := by apply Matrix.ext; unfold pivotMatrix434 node434 pivotPermutation434; decide +kernel
  have hmoment : injectiveMoment H node434 = injectiveMoment H pivotMatrix434 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix434 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix434 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix434 (0 : Fin 4)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix434 (0 : Fin 4) = raw953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix434 raw953; decide +kernel
    rw [heq]
    exact (canonical953 hH).trans (sound127 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix434 (1 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix434 (1 : Fin 4) = raw1417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix434 raw1417; decide +kernel
    rw [heq]
    exact (canonical1417 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix434 (2 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix434 (2 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix434 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix434 (3 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix434 (3 : Fin 4) = raw1433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix434 raw1433; decide +kernel
    rw [heq]
    exact (canonical1433 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node434 + (injectiveMoment H (mergeFirst pivotMatrix434 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix434 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix434 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix434 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value434, value127, value145, value150, value153, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node123 node123Labels = Sparse.eval singlePairValue123 (familyPairVector B) := by
  have hp := single_label_three B hB node123
  have hl : node123Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node123 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 1) = PairSemantics.raw5125 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node123 PairSemantics.raw5125; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5125 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 2) = PairSemantics.raw5182 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node123 PairSemantics.raw5182; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5182 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node123 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value352 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 4) = PairSemantics.raw141 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node123 PairSemantics.raw141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical141 hH).trans (PairSemantics.sound352 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue123, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value68, PairSemantics.value352, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node124 node124Labels = Sparse.eval singlePairValue124 (familyPairVector B) := by
  have hp := single_label_three B hB node124
  have hl : node124Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node124 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 1) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node124 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 2) = PairSemantics.raw5179 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node124 PairSemantics.raw5179; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5179 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node124 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value434 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 4) = PairSemantics.raw142 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node124 PairSemantics.raw142; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical142 hH).trans (PairSemantics.sound434 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue124, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value68, PairSemantics.value434, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node127 node127Labels = Sparse.eval singlePairValue127 (familyPairVector B) := by
  have hp := single_label_three B hB node127
  have hl : node127Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node127 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node127 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 2) = PairSemantics.raw5170 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node127 PairSemantics.raw5170; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5170 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node127 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value430 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 4) = PairSemantics.raw145 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node127 PairSemantics.raw145; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical145 hH).trans (PairSemantics.sound430 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue127, PairSemantics.value0, PairSemantics.value4, PairSemantics.value46, PairSemantics.value68, PairSemantics.value430, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node129 node129Labels = Sparse.eval singlePairValue129 (familyPairVector B) := by
  have hp := single_label_three B hB node129
  have hl : node129Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node129 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node129 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 2) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node129 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value14 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 3) = PairSemantics.raw190 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node129 PairSemantics.raw190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical190 hH).trans (PairSemantics.sound14 hH)
  have hm4 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value139 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 4) = PairSemantics.raw147 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node129 PairSemantics.raw147; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical147 hH).trans (PairSemantics.sound139 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue129, PairSemantics.value0, PairSemantics.value4, PairSemantics.value14, PairSemantics.value46, PairSemantics.value139, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node130 node130Labels = Sparse.eval singlePairValue130 (familyPairVector B) := by
  have hp := single_label_three B hB node130
  have hl : node130Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node130 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 1) = PairSemantics.raw5147 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node130 PairSemantics.raw5147; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5147 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 2) = PairSemantics.raw5159 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node130 PairSemantics.raw5159; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5159 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node130 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value417 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 4) = PairSemantics.raw148 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node130 PairSemantics.raw148; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical148 hH).trans (PairSemantics.sound417 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue130, PairSemantics.value0, PairSemantics.value46, PairSemantics.value68, PairSemantics.value417, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node131 node131Labels = Sparse.eval singlePairValue131 (familyPairVector B) := by
  have hp := single_label_three B hB node131
  have hl : node131Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node131 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node131 PairSemantics.raw5132; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 2) = PairSemantics.raw5185 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node131 PairSemantics.raw5185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5185 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node131 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value141 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 4) = PairSemantics.raw149 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node131 PairSemantics.raw149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical149 hH).trans (PairSemantics.sound141 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue131, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value15, PairSemantics.value141, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node123 node123Labels = Sparse.eval nodeValue123 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue123 (familyPairVector B) := singlePair123 B _hB
    _ = _ := by norm_num [singlePairValue123, nodeValue123, Sparse.eval, mixedVector] <;> ring

theorem sound124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node124 node124Labels = Sparse.eval nodeValue124 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue124 (familyPairVector B) := singlePair124 B _hB
    _ = _ := by norm_num [singlePairValue124, nodeValue124, Sparse.eval, mixedVector] <;> ring

theorem sound127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node127 node127Labels = Sparse.eval nodeValue127 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue127 (familyPairVector B) := singlePair127 B _hB
    _ = _ := by norm_num [singlePairValue127, nodeValue127, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node129 node129Labels = Sparse.eval nodeValue129 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue129 (familyPairVector B) := singlePair129 B _hB
    _ = _ := by
      norm_num [singlePairValue129, nodeValue129, Sparse.eval, mixedVector]
      ring

theorem sound130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node130 node130Labels = Sparse.eval nodeValue130 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue130 (familyPairVector B) := singlePair130 B _hB
    _ = _ := by
      norm_num [singlePairValue130, nodeValue130, Sparse.eval, mixedVector]
      ring

theorem sound131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node131 node131Labels = Sparse.eval nodeValue131 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue131 (familyPairVector B) := singlePair131 B _hB
    _ = _ := by
      norm_num [singlePairValue131, nodeValue131, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic81 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm81 x = (-185267666693652480000 : ℝ) * Sparse.eval nodeValue123 x := by
  norm_num [reducedTerm81, nodeValue123, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic82 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm82 x = (2068047807947735040000 : ℝ) * Sparse.eval nodeValue124 x := by
  norm_num [reducedTerm82, nodeValue124, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic85 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm85 x = (-4402737275558952960000 : ℝ) * Sparse.eval nodeValue127 x := by
  norm_num [reducedTerm85, nodeValue127, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic86 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm86 x = (-1100684318889738240000 : ℝ) * Sparse.eval nodeValue129 x := by
  norm_num [reducedTerm86, nodeValue129, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic87 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm87 x = (5849795392074547200000 : ℝ) * Sparse.eval nodeValue130 x := by
  norm_num [reducedTerm87, nodeValue130, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic88 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm88 x = (-782015458785361920000 : ℝ) * Sparse.eval nodeValue131 x := by
  norm_num [reducedTerm88, nodeValue131, Integer.Sparse.eval, Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge78Check : reducedMerge78 = Integer.Sparse.mergeBy masterLess reducedTerm81 reducedTerm82 := by decide +kernel

theorem reducedMerge80Check : reducedMerge80 = Integer.Sparse.mergeBy masterLess reducedMerge78 reducedMerge79 := by decide +kernel

theorem reducedMerge81Check : reducedMerge81 = Integer.Sparse.mergeBy masterLess reducedTerm85 reducedTerm86 := by decide +kernel

theorem reducedMerge82Check : reducedMerge82 = Integer.Sparse.mergeBy masterLess reducedTerm87 reducedTerm88 := by decide +kernel

theorem reducedMerge83Check : reducedMerge83 = Integer.Sparse.mergeBy masterLess reducedMerge81 reducedMerge82 := by decide +kernel

theorem reducedMerge84Check : reducedMerge84 = Integer.Sparse.mergeBy masterLess reducedMerge80 reducedMerge83 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval81 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm81 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm81 (originalVector B) := by
  rw [reducedTermArithmetic81, ← sound123 B hB hF]
  change (-185267666693652480000 : ℝ) * mixedMoment B node123 node123Labels =
    (37623398400 : ℝ) * (((-4924267200 : ℤ) : ℝ) * mixedMoment B node123 node123Labels + 0)
  ring

theorem reducedTermEval82 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm82 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm82 (originalVector B) := by
  rw [reducedTermArithmetic82, ← sound124 B hB hF]
  change (2068047807947735040000 : ℝ) * mixedMoment B node124 node124Labels =
    (37623398400 : ℝ) * ((54967065600 : ℝ) * mixedMoment B node124 node124Labels + 0)
  ring

theorem reducedTermEval85 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm85 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm85 (originalVector B) := by
  rw [reducedTermArithmetic85, ← sound127 B hB hF]
  change (-4402737275558952960000 : ℝ) * mixedMoment B node127 node127Labels =
    (37623398400 : ℝ) * (((-117021254400 : ℤ) : ℝ) * mixedMoment B node127 node127Labels + 0)
  ring

theorem reducedTermEval86 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm86 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm86 (originalVector B) := by
  rw [reducedTermArithmetic86, ← sound129 B hB hF]
  change (-1100684318889738240000 : ℝ) * mixedMoment B node129 node129Labels =
    (37623398400 : ℝ) * (((-29255313600 : ℤ) : ℝ) * mixedMoment B node129 node129Labels + 0)
  ring

theorem reducedTermEval87 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm87 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm87 (originalVector B) := by
  rw [reducedTermArithmetic87, ← sound130 B hB hF]
  change (5849795392074547200000 : ℝ) * mixedMoment B node130 node130Labels =
    (37623398400 : ℝ) * ((155482908000 : ℝ) * mixedMoment B node130 node130Labels + 0)
  ring

theorem reducedTermEval88 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm88 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm88 (originalVector B) := by
  rw [reducedTermArithmetic88, ← sound131 B hB hF]
  change (-782015458785361920000 : ℝ) * mixedMoment B node131 node131Labels =
    (37623398400 : ℝ) * (((-20785348800 : ℤ) : ℝ) * mixedMoment B node131 node131Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval78 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge78 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge78 (originalVector B) := by
  rw [reducedMerge78Check, Integer.Sparse.eval_mergeBy, reducedTermEval81 B hB hF, reducedTermEval82 B hB hF]
  rw [originalMerge78, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval80 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge80 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge80 (originalVector B) := by
  rw [reducedMerge80Check, Integer.Sparse.eval_mergeBy, reducedMergeEval78 B hB hF, reducedMergeEval79_e B hB hF]
  rw [originalMerge80, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval81 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge81 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge81 (originalVector B) := by
  rw [reducedMerge81Check, Integer.Sparse.eval_mergeBy, reducedTermEval85 B hB hF, reducedTermEval86 B hB hF]
  rw [originalMerge81, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval82 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge82 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge82 (originalVector B) := by
  rw [reducedMerge82Check, Integer.Sparse.eval_mergeBy, reducedTermEval87 B hB hF, reducedTermEval88 B hB hF]
  rw [originalMerge82, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval83 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge83 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge83 (originalVector B) := by
  rw [reducedMerge83Check, Integer.Sparse.eval_mergeBy, reducedMergeEval81 B hB hF, reducedMergeEval82 B hB hF]
  rw [originalMerge83, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval84_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge84 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge84 (originalVector B) := by
  rw [reducedMerge84Check, Integer.Sparse.eval_mergeBy, reducedMergeEval80 B hB hF, reducedMergeEval83 B hB hF]
  rw [originalMerge84, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e_oai
