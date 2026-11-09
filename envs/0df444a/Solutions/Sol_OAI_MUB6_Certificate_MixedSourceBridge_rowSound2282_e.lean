-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:11:58.982359+00:00
-- url     : https://prove2.me/submissions/8210c8c6-c014-462b-83ce-9640f6977c10

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3090_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3096_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3181_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_perm {a b : Sparse ι} (h : a.Perm b) (x : ι → ℝ) :
    eval a x = eval b x := by
  unfold eval
  exact (h.map fun p : ι × ℤ => (p.2 : ℝ) * x p.1).sum_eq

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

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_NumericVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem integer_eval_numericVector (B : Fin 7 → Basis) (v : Integer.Sparse (Fin 3237)) :
    Integer.Sparse.eval v (numericVector B) =
      Integer.Sparse.eval (Integer.Sparse.reindex keyMap v) (mixedVector B) := by
  rw [Integer.Sparse.eval_reindex]
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem integer_eval_familyPairVector (B : Fin 7 → Basis)
    (v : Integer.Sparse (Fin 909)) :
    Integer.Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Integer.Sparse.eval v (PairSemantics.momentVector H)) := by
  rw [← Integer.Sparse.eval_toRational, eval_familyPairVector]
  simp only [Integer.Sparse.eval_toRational]

theorem pair_row_zero (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (v : Integer.Sparse (Fin 909))
    (h : ∀ H, IsHadamard H → Integer.Sparse.eval v (PairSemantics.momentVector H) = 0) :
    Integer.Sparse.eval v (familyPairVector B) = 0 := by
  rw [integer_eval_familyPairVector]
  unfold familyAverage
  trans average (fun _ : Fin 7 => (0 : ℝ))
  · apply average_congr
    intro r
    trans average (fun _ : Coord => (0 : ℝ))
    · apply average_congr
      intro s
      exact h _ (relativeMatrix_isHadamard B hB r s)
    · exact average_zero
  · exact average_zero

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical284
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9090 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9090 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw9090 = injectiveMoment H raw9090step0 := by
      have heq : raw9090step0 = raw9090.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9090).symm
    injectiveMoment H raw9090step0 = injectiveMoment H raw9090step1 := by
      have heq : raw9090step1 = -raw9090step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9090step0).symm
    injectiveMoment H raw9090step1 = injectiveMoment H raw9090step2 := by
      have heq : raw9090step2 = (fun i j => raw9090step1 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9090step1 permutation27 permutation4
    _ = injectiveMoment H node169 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1320 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw1320 = injectiveMoment H raw1320step0 := by
      have heq : raw1320step0 = raw1320.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1320).symm
    injectiveMoment H raw1320step0 = injectiveMoment H raw1320step1 := by
      have heq : raw1320step1 = (fun i j => raw1320step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1320step0 permutation31 permutation18
    _ = injectiveMoment H node1027 := by rfl

theorem canonical1332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1332 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw1332 = injectiveMoment H raw1332step0 := by
      have heq : raw1332step0 = raw1332.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1332).symm
    _ = injectiveMoment H node45 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2441 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2441 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2441 = injectiveMoment H raw2441step0 := by
      have heq : raw2441step0 = raw2441.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2441).symm
    injectiveMoment H raw2441step0 = injectiveMoment H raw2441step1 := by
      have heq : raw2441step1 = (fun i j => raw2441step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2441step0 permutation28 permutation18
    _ = injectiveMoment H node1053 := by rfl

theorem canonical2451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2451 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw2451 = injectiveMoment H raw2451step0 := by
      have heq : raw2451step0 = raw2451.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2451).symm
    injectiveMoment H raw2451step0 = injectiveMoment H raw2451step1 := by
      have heq : raw2451step1 = (fun i j => raw2451step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2451step0 permutation31 permutation18
    _ = injectiveMoment H node1040 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9986 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9986 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw9986 = injectiveMoment H raw9986step0 := by
      have heq : raw9986step0 = raw9986.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9986).symm
    injectiveMoment H raw9986step0 = injectiveMoment H raw9986step1 := by
      have heq : raw9986step1 = -raw9986step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9986step0).symm
    injectiveMoment H raw9986step1 = injectiveMoment H raw9986step2 := by
      have heq : raw9986step2 = (fun i j => raw9986step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9986step1 permutation21 permutation3
    _ = injectiveMoment H node203 := by rfl

theorem canonical9987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9987 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw9987 = injectiveMoment H raw9987step0 := by
      have heq : raw9987step0 = raw9987.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9987).symm
    injectiveMoment H raw9987step0 = injectiveMoment H raw9987step1 := by
      have heq : raw9987step1 = -raw9987step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9987step0).symm
    injectiveMoment H raw9987step1 = injectiveMoment H raw9987step2 := by
      have heq : raw9987step2 = (fun i j => raw9987step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9987step1 permutation21 permutation3
    _ = injectiveMoment H node169 := by rfl

theorem canonical9990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9990 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw9990 = injectiveMoment H raw9990step0 := by
      have heq : raw9990step0 = raw9990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9990).symm
    injectiveMoment H raw9990step0 = injectiveMoment H raw9990step1 := by
      have heq : raw9990step1 = (fun i j => raw9990step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9990step0 permutation29 permutation3
    _ = injectiveMoment H node197 := by rfl

theorem canonical9991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9991 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw9991 = injectiveMoment H raw9991step0 := by
      have heq : raw9991step0 = raw9991.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9991).symm
    injectiveMoment H raw9991step0 = injectiveMoment H raw9991step1 := by
      have heq : raw9991step1 = (fun i j => raw9991step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9991step0 permutation29 permutation3
    _ = injectiveMoment H node162 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
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

theorem sound162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node162 = Sparse.eval value162 (momentVector H) := by
  have hc : momentVector H 124 = injectiveMoment H node162 := rfl
  simp [value162, Sparse.eval, hc]

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

theorem canonical5848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5848 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5848 = injectiveMoment H raw5848step0 := by
      have heq : raw5848step0 = raw5848.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5848).symm
    injectiveMoment H raw5848step0 = injectiveMoment H raw5848step1 := by
      have heq : raw5848step1 = (fun i j => raw5848step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5848step0 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

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

theorem sound279 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node279 = Sparse.eval value279 (momentVector H) := by
  have heq : pivotMatrix279 = (fun u v => node279.transpose (pivotPermutation279 u) v) := by apply Matrix.ext; unfold pivotMatrix279 node279 pivotPermutation279; decide +kernel
  have hmoment : injectiveMoment H node279 = injectiveMoment H pivotMatrix279 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix279 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix279 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix279 (0 : Fin 2)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix279 (0 : Fin 2) = raw1332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix279 raw1332; decide +kernel
    rw [heq]
    exact (canonical1332 hH).trans (sound45 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix279 (1 : Fin 2)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix279 (1 : Fin 2) = raw5848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix279 raw5848; decide +kernel
    rw [heq]
    exact (canonical5848 hH).trans (sound46 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node279 + (injectiveMoment H (mergeFirst pivotMatrix279 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix279 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value279, value45, value46, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3336 = injectiveMoment H node1314 := by
  calc
    injectiveMoment H raw3336 = injectiveMoment H raw3336step0 := by
      have heq : raw3336step0 = raw3336.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3336).symm
    injectiveMoment H raw3336step0 = injectiveMoment H raw3336step1 := by
      have heq : raw3336step1 = (fun i j => raw3336step0 (permutation28 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3336step0 permutation28 permutation23
    _ = injectiveMoment H node1314 := by rfl

theorem canonical3342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3342 = injectiveMoment H node607 := by
  rfl

theorem canonical3349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3349 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw3349 = injectiveMoment H raw3349step0 := by
      have heq : raw3349step0 = raw3349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3349).symm
    _ = injectiveMoment H node197 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6563 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw6563 = injectiveMoment H raw6563step0 := by
      have heq : raw6563step0 = raw6563.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6563).symm
    injectiveMoment H raw6563step0 = injectiveMoment H raw6563step1 := by
      have heq : raw6563step1 = (fun i j => raw6563step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6563step0 permutation22 permutation7
    _ = injectiveMoment H node203 := by rfl

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

theorem canonical7247 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7247 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw7247 = injectiveMoment H raw7247step0 := by
      have heq : raw7247step0 = raw7247.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7247).symm
    injectiveMoment H raw7247step0 = injectiveMoment H raw7247step1 := by
      have heq : raw7247step1 = -raw7247step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7247step0).symm
    injectiveMoment H raw7247step1 = injectiveMoment H raw7247step2 := by
      have heq : raw7247step2 = (fun i j => raw7247step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7247step1 permutation29 permutation4
    _ = injectiveMoment H node185 := by rfl

theorem canonical7257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7257 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw7257 = injectiveMoment H raw7257step0 := by
      have heq : raw7257step0 = raw7257.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7257).symm
    _ = injectiveMoment H node279 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical202
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6494 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6494 = injectiveMoment H raw6494step0 := by
      have heq : raw6494step0 = raw6494.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6494).symm
    injectiveMoment H raw6494step0 = injectiveMoment H raw6494step1 := by
      have heq : raw6494step1 = (fun i j => raw6494step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6494step0 permutation27 permutation6
    _ = injectiveMoment H node287 := by rfl

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

theorem canonical6510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6510 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw6510 = injectiveMoment H raw6510step0 := by
      have heq : raw6510step0 = raw6510.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6510).symm
    injectiveMoment H raw6510step0 = injectiveMoment H raw6510step1 := by
      have heq : raw6510step1 = (fun i j => raw6510step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6510step0 permutation27 permutation6
    _ = injectiveMoment H node207 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7281 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7281 = injectiveMoment H raw7281step0 := by
      have heq : raw7281step0 = raw7281.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7281).symm
    _ = injectiveMoment H node291 := by rfl

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

theorem canonical7605 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7605 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw7605 = injectiveMoment H raw7605step0 := by
      have heq : raw7605step0 = raw7605.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7605).symm
    injectiveMoment H raw7605step0 = injectiveMoment H raw7605step1 := by
      have heq : raw7605step1 = (fun i j => raw7605step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7605step0 permutation20 permutation5
    _ = injectiveMoment H node203 := by rfl

theorem canonical7606 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7606 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw7606 = injectiveMoment H raw7606step0 := by
      have heq : raw7606step0 = raw7606.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7606).symm
    injectiveMoment H raw7606step0 = injectiveMoment H raw7606step1 := by
      have heq : raw7606step1 = -raw7606step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7606step0).symm
    injectiveMoment H raw7606step1 = injectiveMoment H raw7606step2 := by
      have heq : raw7606step2 = (fun i j => raw7606step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7606step1 permutation23 permutation3
    _ = injectiveMoment H node184 := by rfl

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

theorem canonical8491 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8491 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8491 = injectiveMoment H raw8491step0 := by
      have heq : raw8491step0 = -raw8491 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8491).symm
    injectiveMoment H raw8491step0 = injectiveMoment H raw8491step1 := by
      have hz : ∀ i, raw8491step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8491step1 = (fun i j => raw8491step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8491step0 permutation9 hz
    injectiveMoment H raw8491step1 = injectiveMoment H raw8491step2 := by
      have heq : raw8491step2 = (fun i j => raw8491step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8491step1 permutation8 permutation4
    _ = injectiveMoment H node62 := by rfl

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

theorem sound1027 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1027 = Sparse.eval value1027 (momentVector H) := by
  have heq : pivotMatrix1027 = (fun u v => node1027.transpose (pivotPermutation1027 u) v) := by apply Matrix.ext; unfold pivotMatrix1027 node1027 pivotPermutation1027; decide +kernel
  have hmoment : injectiveMoment H node1027 = injectiveMoment H pivotMatrix1027 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1027 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1027 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1027 (0 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (0 : Fin 3) = raw3349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw3349; decide +kernel
    rw [heq]
    exact (canonical3349 hH).trans (sound197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1027 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (1 : Fin 3) = raw7257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw7257; decide +kernel
    rw [heq]
    exact (canonical7257 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1027 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (2 : Fin 3) = raw7281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw7281; decide +kernel
    rw [heq]
    exact (canonical7281 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1027 + (injectiveMoment H (mergeFirst pivotMatrix1027 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1027 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1027 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1027, value197, value279, value291, Sparse.eval] at hc ⊢
  linarith

theorem sound1040 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1040 = Sparse.eval value1040 (momentVector H) := by
  have heq : pivotMatrix1040 = (fun u v => node1040 (pivotPermutation1040 u) v) := by apply Matrix.ext; unfold pivotMatrix1040 node1040 pivotPermutation1040; decide +kernel
  have hmoment : injectiveMoment H node1040 = injectiveMoment H pivotMatrix1040 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1040 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1040 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1040 (0 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1040 (0 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1040 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1040 (1 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1040 (1 : Fin 3) = raw6494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1040 raw6494; decide +kernel
    rw [heq]
    exact (canonical6494 hH).trans (sound287 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1040 (2 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1040 (2 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1040 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1040 + (injectiveMoment H (mergeFirst pivotMatrix1040 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1040 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1040 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1040, value176, value207, value287, Sparse.eval] at hc ⊢
  linarith

theorem sound1053 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1053 = Sparse.eval value1053 (momentVector H) := by
  have heq : pivotMatrix1053 = (fun u v => node1053 (pivotPermutation1053 u) v) := by apply Matrix.ext; unfold pivotMatrix1053 node1053 pivotPermutation1053; decide +kernel
  have hmoment : injectiveMoment H node1053 = injectiveMoment H pivotMatrix1053 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1053 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1053 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1053 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1053 (0 : Fin 3) = raw8491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1053 raw8491; decide +kernel
    rw [heq]
    exact (canonical8491 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1053 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1053 (1 : Fin 3) = raw6567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1053 raw6567; decide +kernel
    rw [heq]
    exact (canonical6567 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1053 (2 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1053 (2 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1053 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1053 + (injectiveMoment H (mergeFirst pivotMatrix1053 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1053 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1053 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1053, value185, value207, value62, Sparse.eval] at hc ⊢
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

theorem sound1057 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1057 = Sparse.eval value1057 (momentVector H) := by
  have heq : pivotMatrix1057 = (fun u v => node1057 (pivotPermutation1057 u) v) := by apply Matrix.ext; unfold pivotMatrix1057 node1057 pivotPermutation1057; decide +kernel
  have hmoment : injectiveMoment H node1057 = injectiveMoment H pivotMatrix1057 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1057 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1057 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1057 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1057 (0 : Fin 3) = raw8093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1057 raw8093; decide +kernel
    rw [heq]
    exact (canonical8093 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1057 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1057 (1 : Fin 3) = raw6563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1057 raw6563; decide +kernel
    rw [heq]
    exact (canonical6563 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1057 (2 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1057 (2 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1057 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1057 + (injectiveMoment H (mergeFirst pivotMatrix1057 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1057 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1057 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1057, value203, value207, value41, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

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

theorem canonical9176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9176 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw9176 = injectiveMoment H raw9176step0 := by
      have heq : raw9176step0 = -raw9176 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9176).symm
    injectiveMoment H raw9176step0 = injectiveMoment H raw9176step1 := by
      have hz : ∀ i, raw9176step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9176step1 = (fun i j => raw9176step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9176step0 permutation9 hz
    injectiveMoment H raw9176step1 = injectiveMoment H raw9176step2 := by
      have heq : raw9176step2 = (fun i j => raw9176step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9176step1 permutation5 permutation3
    _ = injectiveMoment H node36 := by rfl

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

theorem sound1301 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1301 = Sparse.eval value1301 (momentVector H) := by
  have heq : pivotMatrix1301 = (fun u v => node1301 (pivotPermutation1301 u) v) := by apply Matrix.ext; unfold pivotMatrix1301 node1301 pivotPermutation1301; decide +kernel
  have hmoment : injectiveMoment H node1301 = injectiveMoment H pivotMatrix1301 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1301 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1301 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1301 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1301 (0 : Fin 3) = raw7247 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1301 raw7247; decide +kernel
    rw [heq]
    exact (canonical7247 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1301 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1301 (1 : Fin 3) = raw9090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1301 raw9090; decide +kernel
    rw [heq]
    exact (canonical9090 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1301 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1301 (2 : Fin 3) = raw9176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1301 raw9176; decide +kernel
    rw [heq]
    exact (canonical9176 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1301 + (injectiveMoment H (mergeFirst pivotMatrix1301 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1301 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1301 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1301, value169, value185, value36, Sparse.eval] at hc ⊢
  linarith

theorem sound1314 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1314 = Sparse.eval value1314 (momentVector H) := by
  have heq : pivotMatrix1314 = (fun u v => node1314.transpose (pivotPermutation1314 u) v) := by apply Matrix.ext; unfold pivotMatrix1314 node1314 pivotPermutation1314; decide +kernel
  have hmoment : injectiveMoment H node1314 = injectiveMoment H pivotMatrix1314 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1314 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1314 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1314 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1314 (0 : Fin 3) = raw7605 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1314 raw7605; decide +kernel
    rw [heq]
    exact (canonical7605 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1314 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1314 (1 : Fin 3) = raw9986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1314 raw9986; decide +kernel
    rw [heq]
    exact (canonical9986 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1314 (2 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1314 (2 : Fin 3) = raw9990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1314 raw9990; decide +kernel
    rw [heq]
    exact (canonical9990 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1314 + (injectiveMoment H (mergeFirst pivotMatrix1314 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1314 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1314 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1314, value197, value203, Sparse.eval] at hc ⊢
  linarith

theorem sound1315 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1315 = Sparse.eval value1315 (momentVector H) := by
  have heq : pivotMatrix1315 = (fun u v => node1315.transpose (pivotPermutation1315 u) v) := by apply Matrix.ext; unfold pivotMatrix1315 node1315 pivotPermutation1315; decide +kernel
  have hmoment : injectiveMoment H node1315 = injectiveMoment H pivotMatrix1315 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1315 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1315 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1315 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (0 : Fin 3) = raw7606 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw7606; decide +kernel
    rw [heq]
    exact (canonical7606 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1315 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (1 : Fin 3) = raw9987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw9987; decide +kernel
    rw [heq]
    exact (canonical9987 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1315 (2 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (2 : Fin 3) = raw9991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw9991; decide +kernel
    rw [heq]
    exact (canonical9991 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1315 + (injectiveMoment H (mergeFirst pivotMatrix1315 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1315 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1315 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1315, value162, value169, value184, Sparse.eval] at hc ⊢
  linarith

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

theorem sound520 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node520 = Sparse.eval value520 (momentVector H) := by
  have hc : momentVector H 47 = injectiveMoment H node520 := rfl
  simp [value520, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2337 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2337 = injectiveMoment H raw2337step0 := by
      have heq : raw2337step0 = raw2337.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2337).symm
    injectiveMoment H raw2337step0 = injectiveMoment H raw2337step1 := by
      have heq : raw2337step1 = (fun i j => raw2337step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2337step0 permutation28 permutation24
    _ = injectiveMoment H node1053 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound27
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1749 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1749 = Sparse.eval value1749 (momentVector H) := by
  have heq : pivotMatrix1749 = (fun u v => node1749 (pivotPermutation1749 u) v) := by apply Matrix.ext; unfold pivotMatrix1749 node1749 pivotPermutation1749; decide +kernel
  have hmoment : injectiveMoment H node1749 = injectiveMoment H pivotMatrix1749 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1749 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1749 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1749 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1749 (0 : Fin 4) = raw1320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1749 raw1320; decide +kernel
    rw [heq]
    exact (canonical1320 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1749 (1 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1749 (1 : Fin 4) = raw2337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1749 raw2337; decide +kernel
    rw [heq]
    exact (canonical2337 hH).trans (sound1053 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1749 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1749 (2 : Fin 4) = raw2441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1749 raw2441; decide +kernel
    rw [heq]
    exact (canonical2441 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1749 (3 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1749 (3 : Fin 4) = raw2451 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1749 raw2451; decide +kernel
    rw [heq]
    exact (canonical2451 hH).trans (sound1040 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1749 + (injectiveMoment H (mergeFirst pivotMatrix1749 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1749 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1749 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1749 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1749, value1027, value1040, value1053, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical3497 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3497 = injectiveMoment H node2036 := by
  rfl

theorem canonical3498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3498 = injectiveMoment H node1314 := by
  calc
    injectiveMoment H raw3498 = injectiveMoment H raw3498step0 := by
      have heq : raw3498step0 = (fun i j => raw3498 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3498 permutation27 permutation17
    _ = injectiveMoment H node1314 := by rfl

theorem canonical3499 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3499 = injectiveMoment H node2036 := by
  calc
    injectiveMoment H raw3499 = injectiveMoment H raw3499step0 := by
      have heq : raw3499step0 = (fun i j => raw3499 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3499 permutation35 permutation9
    _ = injectiveMoment H node2036 := by rfl

theorem canonical3500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3500 = injectiveMoment H node2001 := by
  calc
    injectiveMoment H raw3500 = injectiveMoment H raw3500step0 := by
      have heq : raw3500step0 = (fun i j => raw3500 (permutation77 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3500 permutation77 permutation29
    _ = injectiveMoment H node2001 := by rfl

theorem canonical3504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3504 = injectiveMoment H node591 := by
  calc
    injectiveMoment H raw3504 = injectiveMoment H raw3504step0 := by
      have heq : raw3504step0 = -raw3504 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3504).symm
    injectiveMoment H raw3504step0 = injectiveMoment H raw3504step1 := by
      have heq : raw3504step1 = (fun i j => raw3504step0 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3504step0 permutation23 permutation16
    _ = injectiveMoment H node591 := by rfl

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

theorem canonical3596 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3596 = injectiveMoment H node520 := by
  calc
    injectiveMoment H raw3596 = injectiveMoment H raw3596step0 := by
      have heq : raw3596step0 = -raw3596 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3596).symm
    injectiveMoment H raw3596step0 = injectiveMoment H raw3596step1 := by
      have heq : raw3596step1 = (fun i j => raw3596step0 (permutation30 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3596step0 permutation30 permutation11
    _ = injectiveMoment H node520 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical285
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9129 = injectiveMoment H node3182 := by
  calc
    injectiveMoment H raw9129 = injectiveMoment H raw9129step0 := by
      have heq : raw9129step0 = (fun i j => raw9129 (permutation277 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9129 permutation277 permutation10
    _ = injectiveMoment H node3182 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node683 = Sparse.eval value683 (momentVector H) := by
  have hc : momentVector H 205 = injectiveMoment H node683 := rfl
  simp [value683, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound9
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node591 = Sparse.eval value591 (momentVector H) := by
  have hc : momentVector H 140 = injectiveMoment H node591 := rfl
  simp [value591, Sparse.eval, hc]

theorem sound607 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node607 = Sparse.eval value607 (momentVector H) := by
  have hc : momentVector H 16 = injectiveMoment H node607 := rfl
  simp [value607, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3239 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3239 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw3239 = injectiveMoment H raw3239step0 := by
      have heq : raw3239step0 = raw3239.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3239).symm
    injectiveMoment H raw3239step0 = injectiveMoment H raw3239step1 := by
      have heq : raw3239step1 = -raw3239step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3239step0).symm
    injectiveMoment H raw3239step1 = injectiveMoment H raw3239step2 := by
      have heq : raw3239step2 = (fun i j => raw3239step1 (permutation16 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3239step1 permutation16 permutation23
    _ = injectiveMoment H node1056 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical295
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9459 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9459 = injectiveMoment H node3090 := by
  calc
    injectiveMoment H raw9459 = injectiveMoment H raw9459step0 := by
      have heq : raw9459step0 = -raw9459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9459).symm
    injectiveMoment H raw9459step0 = injectiveMoment H raw9459step1 := by
      have heq : raw9459step1 = (fun i j => raw9459step0 (permutation316 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9459step0 permutation316 permutation13
    _ = injectiveMoment H node3090 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3415 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw3415 = injectiveMoment H raw3415step0 := by
      have heq : raw3415step0 = (fun i j => raw3415 (permutation19 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3415 permutation19 permutation19
    _ = injectiveMoment H node1057 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3137 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3137 = injectiveMoment H node1960 := by
  rfl

theorem canonical3141 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3141 = injectiveMoment H node1301 := by
  calc
    injectiveMoment H raw3141 = injectiveMoment H raw3141step0 := by
      have heq : raw3141step0 = -raw3141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3141).symm
    injectiveMoment H raw3141step0 = injectiveMoment H raw3141step1 := by
      have heq : raw3141step1 = (fun i j => raw3141step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3141step0 permutation23 permutation15
    _ = injectiveMoment H node1301 := by rfl

theorem canonical3150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3150 = injectiveMoment H node591 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3487 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3487 = injectiveMoment H node1749 := by
  calc
    injectiveMoment H raw3487 = injectiveMoment H raw3487step0 := by
      have heq : raw3487step0 = -raw3487 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3487).symm
    injectiveMoment H raw3487step0 = injectiveMoment H raw3487step1 := by
      have heq : raw3487step1 = (fun i j => raw3487step0 (permutation136 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3487step0 permutation136 permutation12
    _ = injectiveMoment H node1749 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4391 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4391 = injectiveMoment H node1315 := by
  calc
    injectiveMoment H raw4391 = injectiveMoment H raw4391step0 := by
      have heq : raw4391step0 = raw4391.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4391).symm
    injectiveMoment H raw4391step0 = injectiveMoment H raw4391step1 := by
      have heq : raw4391step1 = -raw4391step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4391step0).symm
    injectiveMoment H raw4391step1 = injectiveMoment H raw4391step2 := by
      have heq : raw4391step2 = (fun i j => raw4391step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4391step1 permutation16 permutation24
    _ = injectiveMoment H node1315 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4576 = injectiveMoment H node683 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound30
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1960 = Sparse.eval value1960 (momentVector H) := by
  have heq : pivotMatrix1960 = (fun u v => node1960 (pivotPermutation1960 u) v) := by apply Matrix.ext; unfold pivotMatrix1960 node1960 pivotPermutation1960; decide +kernel
  have hmoment : injectiveMoment H node1960 = injectiveMoment H pivotMatrix1960 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1960 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1960 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1960 (0 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1960 (0 : Fin 4) = raw4391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1960 raw4391; decide +kernel
    rw [heq]
    exact (canonical4391 hH).trans (sound1315 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1960 (1 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1960 (1 : Fin 4) = raw3239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1960 raw3239; decide +kernel
    rw [heq]
    exact (canonical3239 hH).trans (sound1056 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1960 (2 : Fin 4)) =
      Sparse.eval value591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1960 (2 : Fin 4) = raw3150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1960 raw3150; decide +kernel
    rw [heq]
    exact (canonical3150 hH).trans (sound591 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1960 (3 : Fin 4)) =
      Sparse.eval value1301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1960 (3 : Fin 4) = raw3141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1960 raw3141; decide +kernel
    rw [heq]
    exact (canonical3141 hH).trans (sound1301 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1960 + (injectiveMoment H (mergeFirst pivotMatrix1960 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1960 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1960 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1960 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1960, value1056, value1301, value1315, value591, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4649 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4649 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw4649 = injectiveMoment H raw4649step0 := by
      have heq : raw4649step0 = -raw4649 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4649).symm
    injectiveMoment H raw4649step0 = injectiveMoment H raw4649step1 := by
      have heq : raw4649step1 = (fun i j => raw4649step0 (permutation13 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4649step0 permutation13 permutation30
    _ = injectiveMoment H node1057 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound31
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2001 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2001 = Sparse.eval value2001 (momentVector H) := by
  have heq : pivotMatrix2001 = (fun u v => node2001 (pivotPermutation2001 u) v) := by apply Matrix.ext; unfold pivotMatrix2001 node2001 pivotPermutation2001; decide +kernel
  have hmoment : injectiveMoment H node2001 = injectiveMoment H pivotMatrix2001 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2001 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2001 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2001 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2001 (0 : Fin 4) = raw4649 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2001 raw4649; decide +kernel
    rw [heq]
    exact (canonical4649 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2001 (1 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2001 (1 : Fin 4) = raw3415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2001 raw3415; decide +kernel
    rw [heq]
    exact (canonical3415 hH).trans (sound1057 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2001 (2 : Fin 4)) =
      Sparse.eval value607 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2001 (2 : Fin 4) = raw3342 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2001 raw3342; decide +kernel
    rw [heq]
    exact (canonical3342 hH).trans (sound607 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2001 (3 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2001 (3 : Fin 4) = raw3336 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2001 raw3336; decide +kernel
    rw [heq]
    exact (canonical3336 hH).trans (sound1314 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2001 + (injectiveMoment H (mergeFirst pivotMatrix2001 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2001 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2001 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2001 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2001, value1057, value1314, value607, Sparse.eval] at hc ⊢
  linarith

theorem sound2036 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2036 = Sparse.eval value2036 (momentVector H) := by
  have heq : pivotMatrix2036 = (fun u v => node2036 (pivotPermutation2036 u) v) := by apply Matrix.ext; unfold pivotMatrix2036 node2036 pivotPermutation2036; decide +kernel
  have hmoment : injectiveMoment H node2036 = injectiveMoment H pivotMatrix2036 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2036 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2036 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2036 (0 : Fin 4)) =
      Sparse.eval value683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2036 (0 : Fin 4) = raw4576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2036 raw4576; decide +kernel
    rw [heq]
    exact (canonical4576 hH).trans (sound683 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2036 (1 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2036 (1 : Fin 4) = raw3596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2036 raw3596; decide +kernel
    rw [heq]
    exact (canonical3596 hH).trans (sound520 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2036 (2 : Fin 4)) =
      Sparse.eval value591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2036 (2 : Fin 4) = raw3504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2036 raw3504; decide +kernel
    rw [heq]
    exact (canonical3504 hH).trans (sound591 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2036 (3 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2036 (3 : Fin 4) = raw3498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2036 raw3498; decide +kernel
    rw [heq]
    exact (canonical3498 hH).trans (sound1314 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2036 + (injectiveMoment H (mergeFirst pivotMatrix2036 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2036 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2036 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2036 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2036, value1314, value520, value591, value683, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound49
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3182 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3182 = Sparse.eval value3182 (momentVector H) := by
  have heq : pivotMatrix3182 = (fun u v => node3182 (pivotPermutation3182 u) v) := by apply Matrix.ext; unfold pivotMatrix3182 node3182 pivotPermutation3182; decide +kernel
  have hmoment : injectiveMoment H node3182 = injectiveMoment H pivotMatrix3182 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3182 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3182 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3182 (0 : Fin 5)) =
      Sparse.eval value1960 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (0 : Fin 5) = raw3137 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3137; decide +kernel
    rw [heq]
    exact (canonical3137 hH).trans (sound1960 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3182 (1 : Fin 5)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (1 : Fin 5) = raw3487 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3487; decide +kernel
    rw [heq]
    exact (canonical3487 hH).trans (sound1749 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3182 (2 : Fin 5)) =
      Sparse.eval value2036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (2 : Fin 5) = raw3497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3497; decide +kernel
    rw [heq]
    exact (canonical3497 hH).trans (sound2036 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3182 (3 : Fin 5)) =
      Sparse.eval value2036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (3 : Fin 5) = raw3499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3499; decide +kernel
    rw [heq]
    exact (canonical3499 hH).trans (sound2036 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3182 (4 : Fin 5)) =
      Sparse.eval value2001 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (4 : Fin 5) = raw3500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3500; decide +kernel
    rw [heq]
    exact (canonical3500 hH).trans (sound2001 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3182 + (injectiveMoment H (mergeFirst pivotMatrix3182 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3182 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3182 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3182 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3182 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3182, value1749, value1960, value2001, value2036, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical293
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9397 = injectiveMoment H node1749 := by
  calc
    injectiveMoment H raw9397 = injectiveMoment H raw9397step0 := by
      have heq : raw9397step0 = -raw9397 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9397).symm
    injectiveMoment H raw9397step0 = injectiveMoment H raw9397step1 := by
      have hz : ∀ j, raw9397step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9397step1 = (fun i j => raw9397step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9397step0 permutation202 hz
    injectiveMoment H raw9397step1 = injectiveMoment H raw9397step2 := by
      have heq : raw9397step2 = (fun i j => raw9397step1 (permutation128 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9397step1 permutation128 permutation14
    _ = injectiveMoment H node1749 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical296
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9480 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9480 = injectiveMoment H node3090 := by
  calc
    injectiveMoment H raw9480 = injectiveMoment H raw9480step0 := by
      have heq : raw9480step0 = -raw9480 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9480).symm
    injectiveMoment H raw9480step0 = injectiveMoment H raw9480step1 := by
      have heq : raw9480step1 = (fun i j => raw9480step0 (permutation322 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9480step0 permutation322 permutation13
    _ = injectiveMoment H node3090 := by rfl

theorem canonical9489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9489 = injectiveMoment H node3096 := by
  calc
    injectiveMoment H raw9489 = injectiveMoment H raw9489step0 := by
      have heq : raw9489step0 = (fun i j => raw9489 (permutation326 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9489 permutation326 permutation17
    _ = injectiveMoment H node3096 := by rfl

theorem canonical9490 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9490 = injectiveMoment H node3181 := by
  calc
    injectiveMoment H raw9490 = injectiveMoment H raw9490step0 := by
      have heq : raw9490step0 = (fun i j => raw9490 (permutation277 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9490 permutation277 permutation10
    _ = injectiveMoment H node3181 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary7
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound151 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow151 (momentVector H) = 0 := by
  have hshape : boundaryMatrix151 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix151 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix151 (0 : Fin 6)) =
      Sparse.eval value3182 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (0 : Fin 6) = raw9129 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9129 hH).trans (sound3182 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix151 (1 : Fin 6)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (1 : Fin 6) = raw9397 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9397 hH).trans (sound1749 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix151 (2 : Fin 6)) =
      Sparse.eval value3090 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (2 : Fin 6) = raw9459 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9459 hH).trans (sound3090_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix151 (3 : Fin 6)) =
      Sparse.eval value3090 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (3 : Fin 6) = raw9480 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9480 hH).trans (sound3090_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix151 (4 : Fin 6)) =
      Sparse.eval value3096 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (4 : Fin 6) = raw9489 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9489 hH).trans (sound3096_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix151 (5 : Fin 6)) =
      Sparse.eval value3181 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix151 (5 : Fin 6) = raw9490 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9490 hH).trans (sound3181_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix151 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix151 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow151, value1749, value3090, value3096, value3181, value3182, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2282 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2282)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow151) := by decide +kernel

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound2282_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2282 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2282, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow151 (fun _ hH => PairSemantics.boundarySound151 hH)

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e_oai
