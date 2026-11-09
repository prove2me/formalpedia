-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:14:15.052257+00:00
-- url     : https://prove2.me/submissions/c02f9f07-8416-417a-bf96-5e4ef8fc7d1a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2368_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2369_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2371_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2373_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2374_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2375_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2376_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2377_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2378_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2379_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2380_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2381_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2382_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2383_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3272_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3290_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3291_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3324_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3328_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3456_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3468_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical260
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8320 = injectiveMoment H node3324 := by
  calc
    injectiveMoment H raw8320 = injectiveMoment H raw8320step0 := by
      have heq : raw8320step0 = -raw8320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8320).symm
    injectiveMoment H raw8320step0 = injectiveMoment H raw8320step1 := by
      have heq : raw8320step1 = (fun i j => raw8320step0 (permutation300 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8320step0 permutation300 permutation15
    _ = injectiveMoment H node3324 := by rfl

theorem canonical8325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8325 = injectiveMoment H node3272 := by
  calc
    injectiveMoment H raw8325 = injectiveMoment H raw8325step0 := by
      have heq : raw8325step0 = (fun i j => raw8325 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8325 permutation258 permutation9
    _ = injectiveMoment H node3272 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical287
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9207 = injectiveMoment H node3324 := by
  calc
    injectiveMoment H raw9207 = injectiveMoment H raw9207step0 := by
      have heq : raw9207step0 = -raw9207 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9207).symm
    injectiveMoment H raw9207step0 = injectiveMoment H raw9207step1 := by
      have heq : raw9207step1 = (fun i j => raw9207step0 (permutation297 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9207step0 permutation297 permutation15
    _ = injectiveMoment H node3324 := by rfl

theorem canonical9212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9212 = injectiveMoment H node3272 := by
  calc
    injectiveMoment H raw9212 = injectiveMoment H raw9212step0 := by
      have heq : raw9212step0 = (fun i j => raw9212 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9212 permutation277 permutation9
    _ = injectiveMoment H node3272 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical289
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9254 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9254 = injectiveMoment H node3324 := by
  calc
    injectiveMoment H raw9254 = injectiveMoment H raw9254step0 := by
      have heq : raw9254step0 = -raw9254 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9254).symm
    injectiveMoment H raw9254step0 = injectiveMoment H raw9254step1 := by
      have heq : raw9254step1 = (fun i j => raw9254step0 (permutation295 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9254step0 permutation295 permutation15
    _ = injectiveMoment H node3324 := by rfl

theorem canonical9270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9270 = injectiveMoment H node3286 := by
  calc
    injectiveMoment H raw9270 = injectiveMoment H raw9270step0 := by
      have heq : raw9270step0 = (fun i j => raw9270 (permutation242 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9270 permutation242 permutation15
    _ = injectiveMoment H node3286 := by rfl

theorem canonical9274 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9274 = injectiveMoment H node3468 := by
  calc
    injectiveMoment H raw9274 = injectiveMoment H raw9274step0 := by
      have heq : raw9274step0 = (fun i j => raw9274 (permutation242 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9274 permutation242 permutation15
    _ = injectiveMoment H node3468 := by rfl

theorem canonical9276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9276 = injectiveMoment H node3328 := by
  calc
    injectiveMoment H raw9276 = injectiveMoment H raw9276step0 := by
      have heq : raw9276step0 = (fun i j => raw9276 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9276 permutation258 permutation9
    _ = injectiveMoment H node3328 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical291
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9318 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9318 = injectiveMoment H node3290 := by
  calc
    injectiveMoment H raw9318 = injectiveMoment H raw9318step0 := by
      have heq : raw9318step0 = (fun i j => raw9318 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9318 permutation258 permutation9
    _ = injectiveMoment H node3290 := by rfl

theorem canonical9321 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9321 = injectiveMoment H node3456 := by
  calc
    injectiveMoment H raw9321 = injectiveMoment H raw9321step0 := by
      have heq : raw9321step0 = -raw9321 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9321).symm
    injectiveMoment H raw9321step0 = injectiveMoment H raw9321step1 := by
      have heq : raw9321step1 = (fun i j => raw9321step0 (permutation236 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9321step0 permutation236 permutation15
    _ = injectiveMoment H node3456 := by rfl

theorem canonical9323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9323 = injectiveMoment H node3291 := by
  calc
    injectiveMoment H raw9323 = injectiveMoment H raw9323step0 := by
      have heq : raw9323step0 = (fun i j => raw9323 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9323 permutation258 permutation9
    _ = injectiveMoment H node3291 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2528 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2528 = injectiveMoment H raw2528step0 := by
      have heq : raw2528step0 = raw2528.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2528).symm
    injectiveMoment H raw2528step0 = injectiveMoment H raw2528step1 := by
      have heq : raw2528step1 = -raw2528step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2528step0).symm
    injectiveMoment H raw2528step1 = injectiveMoment H raw2528step2 := by
      have heq : raw2528step2 = (fun i j => raw2528step1 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2528step1 permutation11 permutation8
    _ = injectiveMoment H node111 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical263 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw263 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw263 = injectiveMoment H raw263step0 := by
      have heq : raw263step0 = raw263.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw263).symm
    injectiveMoment H raw263step0 = injectiveMoment H raw263step1 := by
      have heq : raw263step1 = (fun i j => raw263step0 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw263step0 permutation22 permutation6
    _ = injectiveMoment H node191 := by rfl

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

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
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

theorem canonical2123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2123 = injectiveMoment H node1190 := by
  calc
    injectiveMoment H raw2123 = injectiveMoment H raw2123step0 := by
      have heq : raw2123step0 = raw2123.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2123).symm
    injectiveMoment H raw2123step0 = injectiveMoment H raw2123step1 := by
      have heq : raw2123step1 = (fun i j => raw2123step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2123step0 permutation32 permutation32
    _ = injectiveMoment H node1190 := by rfl

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

theorem canonical2523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2523 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw2523 = injectiveMoment H raw2523step0 := by
      have heq : raw2523step0 = raw2523.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2523).symm
    injectiveMoment H raw2523step0 = injectiveMoment H raw2523step1 := by
      have heq : raw2523step1 = (fun i j => raw2523step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2523step0 permutation10 permutation3
    _ = injectiveMoment H node135 := by rfl

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

theorem canonical6888 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6888 = injectiveMoment H node213 := by
  calc
    injectiveMoment H raw6888 = injectiveMoment H raw6888step0 := by
      have heq : raw6888step0 = raw6888.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6888).symm
    injectiveMoment H raw6888step0 = injectiveMoment H raw6888step1 := by
      have heq : raw6888step1 = -raw6888step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6888step0).symm
    injectiveMoment H raw6888step1 = injectiveMoment H raw6888step2 := by
      have heq : raw6888step2 = (fun i j => raw6888step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6888step1 permutation25 permutation4
    _ = injectiveMoment H node213 := by rfl

theorem canonical6894 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6894 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw6894 = injectiveMoment H raw6894step0 := by
      have heq : raw6894step0 = raw6894.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6894).symm
    injectiveMoment H raw6894step0 = injectiveMoment H raw6894step1 := by
      have heq : raw6894step1 = -raw6894step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6894step0).symm
    injectiveMoment H raw6894step1 = injectiveMoment H raw6894step2 := by
      have heq : raw6894step2 = (fun i j => raw6894step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6894step1 permutation25 permutation4
    _ = injectiveMoment H node212 := by rfl

theorem canonical6906 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6906 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw6906 = injectiveMoment H raw6906step0 := by
      have heq : raw6906step0 = raw6906.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6906).symm
    injectiveMoment H raw6906step0 = injectiveMoment H raw6906step1 := by
      have heq : raw6906step1 = -raw6906step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6906step0).symm
    injectiveMoment H raw6906step1 = injectiveMoment H raw6906step2 := by
      have heq : raw6906step2 = (fun i j => raw6906step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6906step1 permutation25 permutation4
    _ = injectiveMoment H node210 := by rfl

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

theorem canonical8222 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8222 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw8222 = injectiveMoment H raw8222step0 := by
      have heq : raw8222step0 = raw8222.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8222).symm
    injectiveMoment H raw8222step0 = injectiveMoment H raw8222step1 := by
      have heq : raw8222step1 = (fun i j => raw8222step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8222step0 permutation19 permutation4
    _ = injectiveMoment H node193 := by rfl

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

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node135 = Sparse.eval value135 (momentVector H) := by
  have hc : momentVector H 306 = injectiveMoment H node135 := rfl
  simp [value135, Sparse.eval, hc]

theorem sound191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node191 = Sparse.eval value191 (momentVector H) := by
  have hc : momentVector H 721 = injectiveMoment H node191 := rfl
  simp [value191, Sparse.eval, hc]

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

theorem sound193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node193 = Sparse.eval value193 (momentVector H) := by
  have hc : momentVector H 723 = injectiveMoment H node193 := rfl
  simp [value193, Sparse.eval, hc]

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

theorem sound213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node213 = Sparse.eval value213 (momentVector H) := by
  have hc : momentVector H 728 = injectiveMoment H node213 := rfl
  simp [value213, Sparse.eval, hc]

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

theorem sound757 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node757 = Sparse.eval value757 (momentVector H) := by
  have heq : pivotMatrix757 = (fun u v => node757.transpose (pivotPermutation757 u) v) := by apply Matrix.ext; unfold pivotMatrix757 node757 pivotPermutation757; decide +kernel
  have hmoment : injectiveMoment H node757 = injectiveMoment H pivotMatrix757 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix757 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix757 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix757 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix757 (0 : Fin 3) = raw263 := by apply Matrix.ext; unfold mergeFirst pivotMatrix757 raw263; decide +kernel
    rw [heq]
    exact (canonical263 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix757 (1 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix757 (1 : Fin 3) = raw2523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix757 raw2523; decide +kernel
    rw [heq]
    exact (canonical2523 hH).trans (sound135 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix757 (2 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix757 (2 : Fin 3) = raw2528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix757 raw2528; decide +kernel
    rw [heq]
    exact (canonical2528 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node757 + (injectiveMoment H (mergeFirst pivotMatrix757 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix757 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix757 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value757, value111, value135, value191, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical5808 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5808 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw5808 = injectiveMoment H raw5808step0 := by
      have heq : raw5808step0 = raw5808.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5808).symm
    injectiveMoment H raw5808step0 = injectiveMoment H raw5808step1 := by
      have heq : raw5808step1 = (fun i j => raw5808step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5808step0 permutation16 permutation4
    _ = injectiveMoment H node191 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound13
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound895 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node895 = Sparse.eval value895 (momentVector H) := by
  have heq : pivotMatrix895 = (fun u v => node895.transpose (pivotPermutation895 u) v) := by apply Matrix.ext; unfold pivotMatrix895 node895 pivotPermutation895; decide +kernel
  have hmoment : injectiveMoment H node895 = injectiveMoment H pivotMatrix895 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix895 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix895 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix895 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix895 (0 : Fin 3) = raw2523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix895 raw2523; decide +kernel
    rw [heq]
    exact (canonical2523 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix895 (1 : Fin 3)) =
      Sparse.eval value213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix895 (1 : Fin 3) = raw6888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix895 raw6888; decide +kernel
    rw [heq]
    exact (canonical6888 hH).trans (sound213 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix895 (2 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix895 (2 : Fin 3) = raw6894 := by apply Matrix.ext; unfold mergeFirst pivotMatrix895 raw6894; decide +kernel
    rw [heq]
    exact (canonical6894 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node895 + (injectiveMoment H (mergeFirst pivotMatrix895 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix895 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix895 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value895, value135, value212, value213, Sparse.eval] at hc ⊢
  linarith

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

theorem sound944 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node944 = Sparse.eval value944 (momentVector H) := by
  have heq : pivotMatrix944 = (fun u v => node944.transpose (pivotPermutation944 u) v) := by apply Matrix.ext; unfold pivotMatrix944 node944 pivotPermutation944; decide +kernel
  have hmoment : injectiveMoment H node944 = injectiveMoment H pivotMatrix944 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix944 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix944 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix944 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix944 (0 : Fin 3) = raw2528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix944 raw2528; decide +kernel
    rw [heq]
    exact (canonical2528 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix944 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix944 (1 : Fin 3) = raw6894 := by apply Matrix.ext; unfold mergeFirst pivotMatrix944 raw6894; decide +kernel
    rw [heq]
    exact (canonical6894 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix944 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix944 (2 : Fin 3) = raw6906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix944 raw6906; decide +kernel
    rw [heq]
    exact (canonical6906 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node944 + (injectiveMoment H (mergeFirst pivotMatrix944 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix944 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix944 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value944, value111, value210, value212, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical6414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6414 = injectiveMoment H node1008 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8414 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8414 = injectiveMoment H raw8414step0 := by
      have hz : ∀ i, raw8414 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8414step0 = (fun i j => raw8414 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8414 permutation9 hz
    injectiveMoment H raw8414step0 = injectiveMoment H raw8414step1 := by
      have heq : raw8414step1 = (fun i j => raw8414step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8414step0 permutation6 permutation7
    _ = injectiveMoment H node62 := by rfl

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

theorem sound1008 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1008 = Sparse.eval value1008 (momentVector H) := by
  have heq : pivotMatrix1008 = (fun u v => node1008 (pivotPermutation1008 u) v) := by apply Matrix.ext; unfold pivotMatrix1008 node1008 pivotPermutation1008; decide +kernel
  have hmoment : injectiveMoment H node1008 = injectiveMoment H pivotMatrix1008 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1008 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1008 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1008 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1008 (0 : Fin 3) = raw8414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1008 raw8414; decide +kernel
    rw [heq]
    exact (canonical8414 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1008 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1008 (1 : Fin 3) = raw6563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1008 raw6563; decide +kernel
    rw [heq]
    exact (canonical6563 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1008 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1008 (2 : Fin 3) = raw6418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1008 raw6418; decide +kernel
    rw [heq]
    exact (canonical6418 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1008 + (injectiveMoment H (mergeFirst pivotMatrix1008 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1008 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1008 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1008, value203, value210, value62, Sparse.eval] at hc ⊢
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

theorem sound1163 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1163 = Sparse.eval value1163 (momentVector H) := by
  have heq : pivotMatrix1163 = (fun u v => node1163.transpose (pivotPermutation1163 u) v) := by apply Matrix.ext; unfold pivotMatrix1163 node1163 pivotPermutation1163; decide +kernel
  have hmoment : injectiveMoment H node1163 = injectiveMoment H pivotMatrix1163 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1163 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1163 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1163 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1163 (0 : Fin 3) = raw5808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1163 raw5808; decide +kernel
    rw [heq]
    exact (canonical5808 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1163 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1163 (1 : Fin 3) = raw8222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1163 raw8222; decide +kernel
    rw [heq]
    exact (canonical8222 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1163 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1163 (2 : Fin 3) = raw8227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1163 raw8227; decide +kernel
    rw [heq]
    exact (canonical8227 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1163 + (injectiveMoment H (mergeFirst pivotMatrix1163 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1163 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1163 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1163, value191, value193, value198, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound7
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound448 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node448 = Sparse.eval value448 (momentVector H) := by
  have hc : momentVector H 312 = injectiveMoment H node448 := rfl
  simp [value448, Sparse.eval, hc]

theorem sound472 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node472 = Sparse.eval value472 (momentVector H) := by
  have hc : momentVector H 36 = injectiveMoment H node472 := rfl
  simp [value472, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1786 = injectiveMoment H node472 := by
  rfl

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

theorem canonical1798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1798 = injectiveMoment H node944 := by
  calc
    injectiveMoment H raw1798 = injectiveMoment H raw1798step0 := by
      have heq : raw1798step0 = raw1798.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1798).symm
    injectiveMoment H raw1798step0 = injectiveMoment H raw1798step1 := by
      have heq : raw1798step1 = (fun i j => raw1798step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1798step0 permutation30 permutation30
    _ = injectiveMoment H node944 := by rfl

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

theorem sound691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node691 = Sparse.eval value691 (momentVector H) := by
  have hc : momentVector H 783 = injectiveMoment H node691 := rfl
  simp [value691, Sparse.eval, hc]

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

theorem sound576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node576 = Sparse.eval value576 (momentVector H) := by
  have hc : momentVector H 498 = injectiveMoment H node576 := rfl
  simp [value576, Sparse.eval, hc]

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

theorem sound1654 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1654 = Sparse.eval value1654 (momentVector H) := by
  have heq : pivotMatrix1654 = (fun u v => node1654 (pivotPermutation1654 u) v) := by apply Matrix.ext; unfold pivotMatrix1654 node1654 pivotPermutation1654; decide +kernel
  have hmoment : injectiveMoment H node1654 = injectiveMoment H pivotMatrix1654 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1654 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1654 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1654 (0 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1654 (0 : Fin 4) = raw6414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1654 raw6414; decide +kernel
    rw [heq]
    exact (canonical6414 hH).trans (sound1008 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1654 (1 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1654 (1 : Fin 4) = raw2123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1654 raw2123; decide +kernel
    rw [heq]
    exact (canonical2123 hH).trans (sound1190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1654 (2 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1654 (2 : Fin 4) = raw1798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1654 raw1798; decide +kernel
    rw [heq]
    exact (canonical1798 hH).trans (sound944 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1654 (3 : Fin 4)) =
      Sparse.eval value472 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1654 (3 : Fin 4) = raw1786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1654 raw1786; decide +kernel
    rw [heq]
    exact (canonical1786 hH).trans (sound472 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1654 + (injectiveMoment H (mergeFirst pivotMatrix1654 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1654 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1654 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1654 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1654, value1008, value1190, value472, value944, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4343 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4343 = injectiveMoment H node1163 := by
  calc
    injectiveMoment H raw4343 = injectiveMoment H raw4343step0 := by
      have heq : raw4343step0 = raw4343.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4343).symm
    injectiveMoment H raw4343step0 = injectiveMoment H raw4343step1 := by
      have heq : raw4343step1 = -raw4343step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4343step0).symm
    injectiveMoment H raw4343step1 = injectiveMoment H raw4343step2 := by
      have heq : raw4343step2 = (fun i j => raw4343step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4343step1 permutation27 permutation19
    _ = injectiveMoment H node1163 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4498 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4498 = injectiveMoment H node576 := by
  calc
    injectiveMoment H raw4498 = injectiveMoment H raw4498step0 := by
      have heq : raw4498step0 = raw4498.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4498).symm
    injectiveMoment H raw4498step0 = injectiveMoment H raw4498step1 := by
      have heq : raw4498step1 = -raw4498step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4498step0).symm
    injectiveMoment H raw4498step1 = injectiveMoment H raw4498step2 := by
      have heq : raw4498step2 = (fun i j => raw4498step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4498step1 permutation27 permutation19
    _ = injectiveMoment H node576 := by rfl

theorem canonical4511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4511 = injectiveMoment H node2219 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4739 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4739 = injectiveMoment H node472 := by
  calc
    injectiveMoment H raw4739 = injectiveMoment H raw4739step0 := by
      have heq : raw4739step0 = -raw4739 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4739).symm
    injectiveMoment H raw4739step0 = injectiveMoment H raw4739step1 := by
      have heq : raw4739step1 = (fun i j => raw4739step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4739step0 permutation22 permutation23
    _ = injectiveMoment H node472 := by rfl

theorem canonical4742 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4742 = injectiveMoment H node448 := by
  calc
    injectiveMoment H raw4742 = injectiveMoment H raw4742step0 := by
      have heq : raw4742step0 = raw4742.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4742).symm
    injectiveMoment H raw4742step0 = injectiveMoment H raw4742step1 := by
      have heq : raw4742step1 = -raw4742step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4742step0).symm
    injectiveMoment H raw4742step1 = injectiveMoment H raw4742step2 := by
      have heq : raw4742step2 = (fun i j => raw4742step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4742step1 permutation29 permutation16
    _ = injectiveMoment H node448 := by rfl

theorem canonical4752 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4752 = injectiveMoment H node2270 := by
  calc
    injectiveMoment H raw4752 = injectiveMoment H raw4752step0 := by
      have heq : raw4752step0 = (fun i j => raw4752 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4752 permutation39 permutation9
    _ = injectiveMoment H node2270 := by rfl

theorem canonical4754 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4754 = injectiveMoment H node1654 := by
  calc
    injectiveMoment H raw4754 = injectiveMoment H raw4754step0 := by
      have heq : raw4754step0 = -raw4754 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4754).symm
    injectiveMoment H raw4754step0 = injectiveMoment H raw4754step1 := by
      have heq : raw4754step1 = (fun i j => raw4754step0 (permutation108 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4754step0 permutation108 permutation23
    _ = injectiveMoment H node1654 := by rfl

theorem canonical4755 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4755 = injectiveMoment H node2278 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4531 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4531 = injectiveMoment H node1190 := by
  calc
    injectiveMoment H raw4531 = injectiveMoment H raw4531step0 := by
      have heq : raw4531step0 = raw4531.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4531).symm
    injectiveMoment H raw4531step0 = injectiveMoment H raw4531step1 := by
      have heq : raw4531step1 = -raw4531step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4531step0).symm
    injectiveMoment H raw4531step1 = injectiveMoment H raw4531step2 := by
      have heq : raw4531step2 = (fun i j => raw4531step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4531step1 permutation27 permutation19
    _ = injectiveMoment H node1190 := by rfl

theorem canonical4534 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4534 = injectiveMoment H node757 := by
  calc
    injectiveMoment H raw4534 = injectiveMoment H raw4534step0 := by
      have heq : raw4534step0 = raw4534.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4534).symm
    injectiveMoment H raw4534step0 = injectiveMoment H raw4534step1 := by
      have heq : raw4534step1 = -raw4534step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4534step0).symm
    injectiveMoment H raw4534step1 = injectiveMoment H raw4534step2 := by
      have heq : raw4534step2 = (fun i j => raw4534step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4534step1 permutation29 permutation16
    _ = injectiveMoment H node757 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4777 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4777 = injectiveMoment H node944 := by
  calc
    injectiveMoment H raw4777 = injectiveMoment H raw4777step0 := by
      have heq : raw4777step0 = raw4777.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4777).symm
    injectiveMoment H raw4777step0 = injectiveMoment H raw4777step1 := by
      have heq : raw4777step1 = -raw4777step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4777step0).symm
    injectiveMoment H raw4777step1 = injectiveMoment H raw4777step2 := by
      have heq : raw4777step2 = (fun i j => raw4777step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4777step1 permutation29 permutation16
    _ = injectiveMoment H node944 := by rfl

theorem canonical4781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4781 = injectiveMoment H node895 := by
  calc
    injectiveMoment H raw4781 = injectiveMoment H raw4781step0 := by
      have heq : raw4781step0 = raw4781.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4781).symm
    injectiveMoment H raw4781step0 = injectiveMoment H raw4781step1 := by
      have heq : raw4781step1 = -raw4781step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4781step0).symm
    injectiveMoment H raw4781step1 = injectiveMoment H raw4781step2 := by
      have heq : raw4781step2 = (fun i j => raw4781step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4781step1 permutation29 permutation16
    _ = injectiveMoment H node895 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound34
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2219 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2219 = Sparse.eval value2219 (momentVector H) := by
  have heq : pivotMatrix2219 = (fun u v => node2219 (pivotPermutation2219 u) v) := by apply Matrix.ext; unfold pivotMatrix2219 node2219 pivotPermutation2219; decide +kernel
  have hmoment : injectiveMoment H node2219 = injectiveMoment H pivotMatrix2219 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2219 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2219 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2219 (0 : Fin 4)) =
      Sparse.eval value1163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2219 (0 : Fin 4) = raw4343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2219 raw4343; decide +kernel
    rw [heq]
    exact (canonical4343 hH).trans (sound1163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2219 (1 : Fin 4)) =
      Sparse.eval value576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2219 (1 : Fin 4) = raw4498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2219 raw4498; decide +kernel
    rw [heq]
    exact (canonical4498 hH).trans (sound576 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2219 (2 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2219 (2 : Fin 4) = raw4531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2219 raw4531; decide +kernel
    rw [heq]
    exact (canonical4531 hH).trans (sound1190 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2219 (3 : Fin 4)) =
      Sparse.eval value757 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2219 (3 : Fin 4) = raw4534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2219 raw4534; decide +kernel
    rw [heq]
    exact (canonical4534 hH).trans (sound757 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2219 + (injectiveMoment H (mergeFirst pivotMatrix2219 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2219 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2219 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2219 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2219, value1163, value1190, value576, value757, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4721 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4721 = injectiveMoment H node691 := by
  rfl

theorem canonical4725 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4725 = injectiveMoment H node2270 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound35
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2270 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2270 = Sparse.eval value2270 (momentVector H) := by
  have heq : pivotMatrix2270 = (fun u v => node2270 (pivotPermutation2270 u) v) := by apply Matrix.ext; unfold pivotMatrix2270 node2270 pivotPermutation2270; decide +kernel
  have hmoment : injectiveMoment H node2270 = injectiveMoment H pivotMatrix2270 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2270 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2270 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2270 (0 : Fin 4)) =
      Sparse.eval value576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2270 (0 : Fin 4) = raw4498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2270 raw4498; decide +kernel
    rw [heq]
    exact (canonical4498 hH).trans (sound576 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2270 (1 : Fin 4)) =
      Sparse.eval value691 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2270 (1 : Fin 4) = raw4721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2270 raw4721; decide +kernel
    rw [heq]
    exact (canonical4721 hH).trans (sound691 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2270 (2 : Fin 4)) =
      Sparse.eval value472 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2270 (2 : Fin 4) = raw4739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2270 raw4739; decide +kernel
    rw [heq]
    exact (canonical4739 hH).trans (sound472 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2270 (3 : Fin 4)) =
      Sparse.eval value448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2270 (3 : Fin 4) = raw4742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2270 raw4742; decide +kernel
    rw [heq]
    exact (canonical4742 hH).trans (sound448 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2270 + (injectiveMoment H (mergeFirst pivotMatrix2270 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2270 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2270 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2270 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2270, value448, value472, value576, value691, Sparse.eval] at hc ⊢
  linarith

theorem sound2278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2278 = Sparse.eval value2278 (momentVector H) := by
  have heq : pivotMatrix2278 = (fun u v => node2278 (pivotPermutation2278 u) v) := by apply Matrix.ext; unfold pivotMatrix2278 node2278 pivotPermutation2278; decide +kernel
  have hmoment : injectiveMoment H node2278 = injectiveMoment H pivotMatrix2278 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2278 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2278 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2278 (0 : Fin 4)) =
      Sparse.eval value757 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2278 (0 : Fin 4) = raw4534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2278 raw4534; decide +kernel
    rw [heq]
    exact (canonical4534 hH).trans (sound757 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2278 (1 : Fin 4)) =
      Sparse.eval value448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2278 (1 : Fin 4) = raw4742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2278 raw4742; decide +kernel
    rw [heq]
    exact (canonical4742 hH).trans (sound448 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2278 (2 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2278 (2 : Fin 4) = raw4777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2278 raw4777; decide +kernel
    rw [heq]
    exact (canonical4777 hH).trans (sound944 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2278 (3 : Fin 4)) =
      Sparse.eval value895 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2278 (3 : Fin 4) = raw4781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2278 raw4781; decide +kernel
    rw [heq]
    exact (canonical4781 hH).trans (sound895 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2278 + (injectiveMoment H (mergeFirst pivotMatrix2278 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2278 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2278 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2278 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2278, value448, value757, value895, value944, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound51
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3286 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3286 = Sparse.eval value3286 (momentVector H) := by
  have heq : pivotMatrix3286 = (fun u v => node3286 (pivotPermutation3286 u) v) := by apply Matrix.ext; unfold pivotMatrix3286 node3286 pivotPermutation3286; decide +kernel
  have hmoment : injectiveMoment H node3286 = injectiveMoment H pivotMatrix3286 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3286 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3286 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3286 (0 : Fin 5)) =
      Sparse.eval value2219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3286 (0 : Fin 5) = raw4511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3286 raw4511; decide +kernel
    rw [heq]
    exact (canonical4511 hH).trans (sound2219 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3286 (1 : Fin 5)) =
      Sparse.eval value2270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3286 (1 : Fin 5) = raw4725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3286 raw4725; decide +kernel
    rw [heq]
    exact (canonical4725 hH).trans (sound2270 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3286 (2 : Fin 5)) =
      Sparse.eval value2270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3286 (2 : Fin 5) = raw4752 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3286 raw4752; decide +kernel
    rw [heq]
    exact (canonical4752 hH).trans (sound2270 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3286 (3 : Fin 5)) =
      Sparse.eval value1654 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3286 (3 : Fin 5) = raw4754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3286 raw4754; decide +kernel
    rw [heq]
    exact (canonical4754 hH).trans (sound1654 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3286 (4 : Fin 5)) =
      Sparse.eval value2278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3286 (4 : Fin 5) = raw4755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3286 raw4755; decide +kernel
    rw [heq]
    exact (canonical4755 hH).trans (sound2278 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3286 + (injectiveMoment H (mergeFirst pivotMatrix3286 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3286 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3286 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3286 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3286 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3286, value1654, value2219, value2270, value2278, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary12
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound365 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow365 (momentVector H) = 0 := by
  have hshape : boundaryMatrix365 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix365 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix365 (0 : Fin 6)) =
      Sparse.eval value3324 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (0 : Fin 6) = raw8320 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8320 hH).trans (sound3324_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix365 (1 : Fin 6)) =
      Sparse.eval value3324 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (1 : Fin 6) = raw9207 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9207 hH).trans (sound3324_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix365 (2 : Fin 6)) =
      Sparse.eval value3324 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (2 : Fin 6) = raw9254 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9254 hH).trans (sound3324_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix365 (3 : Fin 6)) =
      Sparse.eval value3286 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (3 : Fin 6) = raw9270 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9270 hH).trans (sound3286 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix365 (4 : Fin 6)) =
      Sparse.eval value3468 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (4 : Fin 6) = raw9274 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9274 hH).trans (sound3468_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix365 (5 : Fin 6)) =
      Sparse.eval value3328 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix365 (5 : Fin 6) = raw9276 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9276 hH).trans (sound3328_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix365 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix365 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow365, value3286, value3324, value3328, value3468, Sparse.eval, Integer.Sparse.eval] at hc ⊢
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

theorem boundarySound369 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow369 (momentVector H) = 0 := by
  have hshape : boundaryMatrix369 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix369 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix369 (0 : Fin 6)) =
      Sparse.eval value3272 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (0 : Fin 6) = raw8325 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8325 hH).trans (sound3272_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix369 (1 : Fin 6)) =
      Sparse.eval value3272 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (1 : Fin 6) = raw9212 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9212 hH).trans (sound3272_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix369 (2 : Fin 6)) =
      Sparse.eval value3468 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (2 : Fin 6) = raw9274 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9274 hH).trans (sound3468_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix369 (3 : Fin 6)) =
      Sparse.eval value3290 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (3 : Fin 6) = raw9318 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9318 hH).trans (sound3290_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix369 (4 : Fin 6)) =
      Sparse.eval value3456 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (4 : Fin 6) = raw9321 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9321 hH).trans (sound3456_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix369 (5 : Fin 6)) =
      Sparse.eval value3291 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix369 (5 : Fin 6) = raw9323 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9323 hH).trans (sound3291_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix369 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix369 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow369, value3272, value3290, value3291, value3456, value3468, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2370 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2370)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow365) := by decide +kernel

theorem reindexCheck2372 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2372)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow369) := by decide +kernel

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound2370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2370 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2370, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow365 (fun _ hH => PairSemantics.boundarySound365 hH)

theorem rowSound2372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2372 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2372, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow369 (fun _ hH => PairSemantics.boundarySound369 hH)

theorem sourceRowsAt2368 : MixedData.sourceRows (2368 : Fin 2425) =
    MixedData.row2368 := by decide +kernel

theorem sourceRowsAt2369 : MixedData.sourceRows (2369 : Fin 2425) =
    MixedData.row2369 := by decide +kernel

theorem sourceRowsAt2370 : MixedData.sourceRows (2370 : Fin 2425) =
    MixedData.row2370 := by decide +kernel

theorem sourceRowsAt2371 : MixedData.sourceRows (2371 : Fin 2425) =
    MixedData.row2371 := by decide +kernel

theorem sourceRowsAt2372 : MixedData.sourceRows (2372 : Fin 2425) =
    MixedData.row2372 := by decide +kernel

theorem sourceRowsAt2373 : MixedData.sourceRows (2373 : Fin 2425) =
    MixedData.row2373 := by decide +kernel

theorem sourceRowsAt2374 : MixedData.sourceRows (2374 : Fin 2425) =
    MixedData.row2374 := by decide +kernel

theorem sourceRowsAt2375 : MixedData.sourceRows (2375 : Fin 2425) =
    MixedData.row2375 := by decide +kernel

theorem sourceRowsAt2376 : MixedData.sourceRows (2376 : Fin 2425) =
    MixedData.row2376 := by decide +kernel

theorem sourceRowsAt2377 : MixedData.sourceRows (2377 : Fin 2425) =
    MixedData.row2377 := by decide +kernel

theorem sourceRowsAt2378 : MixedData.sourceRows (2378 : Fin 2425) =
    MixedData.row2378 := by decide +kernel

theorem sourceRowsAt2379 : MixedData.sourceRows (2379 : Fin 2425) =
    MixedData.row2379 := by decide +kernel

theorem sourceRowsAt2380 : MixedData.sourceRows (2380 : Fin 2425) =
    MixedData.row2380 := by decide +kernel

theorem sourceRowsAt2381 : MixedData.sourceRows (2381 : Fin 2425) =
    MixedData.row2381 := by decide +kernel

theorem sourceRowsAt2382 : MixedData.sourceRows (2382 : Fin 2425) =
    MixedData.row2382 := by decide +kernel

theorem sourceRowsAt2383 : MixedData.sourceRows (2383 : Fin 2425) =
    MixedData.row2383 := by decide +kernel

theorem chunkSound148_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 148) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2368 ∨ k.val = 2369 ∨ k.val = 2370 ∨ k.val = 2371 ∨ k.val = 2372 ∨ k.val = 2373 ∨ k.val = 2374 ∨ k.val = 2375 ∨ k.val = 2376 ∨ k.val = 2377 ∨ k.val = 2378 ∨ k.val = 2379 ∨ k.val = 2380 ∨ k.val = 2381 ∨ k.val = 2382 ∨ k.val = 2383 := by omega
  rcases heq with h2368 | h2369 | h2370 | h2371 | h2372 | h2373 | h2374 | h2375 | h2376 | h2377 | h2378 | h2379 | h2380 | h2381 | h2382 | h2383
  · have he : k = (2368 : Fin 2425) := Fin.ext h2368
    subst k
    rw [sourceRowsAt2368]
    exact rowSound2368_e B hB hF
  · have he : k = (2369 : Fin 2425) := Fin.ext h2369
    subst k
    rw [sourceRowsAt2369]
    exact rowSound2369_e B hB hF
  · have he : k = (2370 : Fin 2425) := Fin.ext h2370
    subst k
    rw [sourceRowsAt2370]
    exact rowSound2370 B hB hF
  · have he : k = (2371 : Fin 2425) := Fin.ext h2371
    subst k
    rw [sourceRowsAt2371]
    exact rowSound2371_e B hB hF
  · have he : k = (2372 : Fin 2425) := Fin.ext h2372
    subst k
    rw [sourceRowsAt2372]
    exact rowSound2372 B hB hF
  · have he : k = (2373 : Fin 2425) := Fin.ext h2373
    subst k
    rw [sourceRowsAt2373]
    exact rowSound2373_e B hB hF
  · have he : k = (2374 : Fin 2425) := Fin.ext h2374
    subst k
    rw [sourceRowsAt2374]
    exact rowSound2374_e B hB hF
  · have he : k = (2375 : Fin 2425) := Fin.ext h2375
    subst k
    rw [sourceRowsAt2375]
    exact rowSound2375_e B hB hF
  · have he : k = (2376 : Fin 2425) := Fin.ext h2376
    subst k
    rw [sourceRowsAt2376]
    exact rowSound2376_e B hB hF
  · have he : k = (2377 : Fin 2425) := Fin.ext h2377
    subst k
    rw [sourceRowsAt2377]
    exact rowSound2377_e B hB hF
  · have he : k = (2378 : Fin 2425) := Fin.ext h2378
    subst k
    rw [sourceRowsAt2378]
    exact rowSound2378_e B hB hF
  · have he : k = (2379 : Fin 2425) := Fin.ext h2379
    subst k
    rw [sourceRowsAt2379]
    exact rowSound2379_e B hB hF
  · have he : k = (2380 : Fin 2425) := Fin.ext h2380
    subst k
    rw [sourceRowsAt2380]
    exact rowSound2380_e B hB hF
  · have he : k = (2381 : Fin 2425) := Fin.ext h2381
    subst k
    rw [sourceRowsAt2381]
    exact rowSound2381_e B hB hF
  · have he : k = (2382 : Fin 2425) := Fin.ext h2382
    subst k
    rw [sourceRowsAt2382]
    exact rowSound2382_e B hB hF
  · have he : k = (2383 : Fin 2425) := Fin.ext h2383
    subst k
    rw [sourceRowsAt2383]
    exact rowSound2383_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e_oai
