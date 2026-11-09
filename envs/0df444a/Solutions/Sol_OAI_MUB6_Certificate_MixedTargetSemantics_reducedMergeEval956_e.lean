-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:51:32.465471+00:00
-- url     : https://prove2.me/submissions/88e88a03-e0f9-4adc-9d9c-568d45c733fd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E122
import Definitions.Def_OAIQ106E136
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E138
import Definitions.Def_OAIQ106E139
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval716_e

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

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

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

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
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

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

theorem g_difference {H : CMatrix} (hH : IsHadamard H) (i j : Coord) :
    g H (difference i j) = if i = j then 1 else 0 := by
  simp only [g, character_difference _ (fun k => hH.1 k _)]
  rw [hH.row_orthogonal]
  split_ifs <;> norm_num

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_ChargeDecomposition
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem weightMultiset_card (w : Coord → ℕ) :
    (weightMultiset w).card = ∑ i, w i := by
  have h (s : Finset Coord) : (∑ i ∈ s, Multiset.replicate (w i) i).card = ∑ i ∈ s, w i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.card_add, ih]
  exact h Finset.univ

theorem weightMultiset_count (w : Coord → ℕ) (k : Coord) :
    (weightMultiset w).count k = w k := by
  have h (s : Finset Coord) :
      (∑ i ∈ s, Multiset.replicate (w i) i).count k = ∑ i ∈ s, if i = k then w i else 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.count_add, Multiset.count_replicate, ih]
  simpa [weightMultiset] using h Finset.univ

theorem positivePositions_card (a : Charge) : (positivePositions a).card = order a :=
  weightMultiset_card _

theorem negativePositions_card {a : Charge} (ha : Balanced a) :
    (negativePositions a).card = order a := by
  have h : (∑ i, ((a i).toNat : ℤ)) - ∑ i, ((-a i).toNat : ℤ) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [Int.toNat_sub_toNat_neg] using (show ∑ i, a i = 0 from ha)
  rw [negativePositions, weightMultiset_card, order]
  exact_mod_cast (sub_eq_zero.mp h).symm

theorem charge_eq_counts (a : Charge) (k : Coord) :
    a k = ((positivePositions a).count k : ℤ) - (negativePositions a).count k := by
  rw [positivePositions, negativePositions, weightMultiset_count, weightMultiset_count]
  exact (Int.toNat_sub_toNat_neg _).symm

theorem positive_negative_ne {a : Charge} {i j : Coord}
    (hi : i ∈ positivePositions a) (hj : j ∈ negativePositions a) : i ≠ j := by
  intro h
  subst j
  rw [← Multiset.count_pos, positivePositions, weightMultiset_count] at hi
  rw [← Multiset.count_pos, negativePositions, weightMultiset_count] at hj
  have hp := Int.pos_iff_toNat_pos.mpr hi
  have hn := Int.pos_iff_toNat_pos.mpr hj
  omega

/-- A balanced charge of order one is one positive and one negative coordinate. -/
theorem order_one_decomposition {a : Charge} (ha : Balanced a) (ho : order a = 1) :
    ∃ i j, i ≠ j ∧ a = difference i j := by
  obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp ((positivePositions_card a).trans ho)
  obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp ((negativePositions_card ha).trans ho)
  refine ⟨i, j, positive_negative_ne (a := a) (by simp [hi]) (by simp [hj]), ?_⟩
  funext k
  rw [charge_eq_counts a k, hi, hj]
  simp [difference, Pi.single_apply, Multiset.count_singleton, eq_comm]

theorem g_order_one {H : CMatrix} (hH : IsHadamard H) {a : Charge}
    (ha : Balanced a) (ho : order a = 1) : g H a = 0 := by
  obtain ⟨i, j, hij, rfl⟩ := order_one_decomposition ha ho
  simp [g_difference hH, hij]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem embedCharge_outside {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (i : Coord)
    (hi : i ∉ Set.range ρ) : embedCharge ρ a i = 0 :=
  Function.extend_apply' _ _ _ hi

theorem embedCharge_sum {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    ∑ i, embedCharge ρ a i = ∑ i, a i := by
  symm
  exact Fintype.sum_of_injective ρ ρ.injective a (embedCharge ρ a)
    (embedCharge_outside ρ a) (fun i => (embedCharge_apply ρ a i).symm)

theorem embedCharge_order {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    order (embedCharge ρ a) = ∑ i, (a i).toNat := by
  symm
  apply Fintype.sum_of_injective ρ ρ.injective (fun i => (a i).toNat)
    (fun i => (embedCharge ρ a i).toNat)
  · intro i hi
    rw [embedCharge_outside ρ a i hi]
    rfl
  · intro i
    rw [embedCharge_apply]

theorem character_embedCharge {p : ℕ} (x : Coord → ℂ) (ρ : Fin p ↪ Coord)
    (a : Fin p → ℤ) : character x (embedCharge ρ a) = ∏ i, x (ρ i) ^ a i := by
  symm
  apply Fintype.prod_of_injective ρ ρ.injective (fun i => x (ρ i) ^ a i)
    (fun i => x i ^ embedCharge ρ a i)
  · intro i hi
    rw [embedCharge_outside ρ a i hi, zpow_zero]
  · intro i
    rw [embedCharge_apply]

theorem rowFourier_eq_g {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ a = g H (embedCharge ρ a) := by
  simp only [rowFourier, g, character_embedCharge]

theorem rowFourier_order_one {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (ha : ∑ i, a i = 0)
    (ho : ∑ i, (a i).toNat = 1) : rowFourier H ρ a = 0 := by
  rw [rowFourier_eq_g]
  apply g_order_one hH
  · exact (embedCharge_sum ρ a).trans ha
  · exact (embedCharge_order ρ a).trans ho

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_order_one {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (ha : ∑ i, A i j = 0) (ho : ∑ i, (A i j).toNat = 1) : mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact rowFourier_order_one (relativeMatrix_isHadamard B hB r _) ρ _ ha ho
  simp [mixedMoment, h]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2281 node2281Labels = Sparse.eval nodeValue2281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2281) = mixedMoment B node2281 node2281Labels := rfl
  simpa [nodeValue2281, Sparse.eval] using hc.symm

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1804 node1804Labels = Sparse.eval nodeValue1804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1804) = mixedMoment B node1804 node1804Labels := rfl
  simpa [nodeValue1804, Sparse.eval] using hc.symm

theorem sound1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1805 node1805Labels = Sparse.eval nodeValue1805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1805) = mixedMoment B node1805 node1805Labels := rfl
  simpa [nodeValue1805, Sparse.eval] using hc.symm

theorem sound1806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1806 node1806Labels = Sparse.eval nodeValue1806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1806) = mixedMoment B node1806 node1806Labels := rfl
  simpa [nodeValue1806, Sparse.eval] using hc.symm

theorem sound1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1807 node1807Labels = Sparse.eval nodeValue1807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1807) = mixedMoment B node1807 node1807Labels := rfl
  simpa [nodeValue1807, Sparse.eval] using hc.symm

theorem sound1808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1808 node1808Labels = Sparse.eval nodeValue1808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1808) = mixedMoment B node1808 node1808Labels := rfl
  simpa [nodeValue1808, Sparse.eval] using hc.symm

theorem sound1809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1809 node1809Labels = Sparse.eval nodeValue1809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1809) = mixedMoment B node1809 node1809Labels := rfl
  simpa [nodeValue1809, Sparse.eval] using hc.symm

theorem sound1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1810 node1810Labels = Sparse.eval nodeValue1810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1810) = mixedMoment B node1810 node1810Labels := rfl
  simpa [nodeValue1810, Sparse.eval] using hc.symm

theorem sound1811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1811 node1811Labels = Sparse.eval nodeValue1811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1811) = mixedMoment B node1811 node1811Labels := rfl
  simpa [nodeValue1811, Sparse.eval] using hc.symm

theorem sound1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1812 node1812Labels = Sparse.eval nodeValue1812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1812) = mixedMoment B node1812 node1812Labels := rfl
  simpa [nodeValue1812, Sparse.eval] using hc.symm

theorem sound1813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1813 node1813Labels = Sparse.eval nodeValue1813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1813) = mixedMoment B node1813 node1813Labels := rfl
  simpa [nodeValue1813, Sparse.eval] using hc.symm

theorem sound1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1814 node1814Labels = Sparse.eval nodeValue1814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1814) = mixedMoment B node1814 node1814Labels := rfl
  simpa [nodeValue1814, Sparse.eval] using hc.symm

theorem sound1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1815 node1815Labels = Sparse.eval nodeValue1815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1815) = mixedMoment B node1815 node1815Labels := rfl
  simpa [nodeValue1815, Sparse.eval] using hc.symm

theorem sound1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1816 node1816Labels = Sparse.eval nodeValue1816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1816) = mixedMoment B node1816 node1816Labels := rfl
  simpa [nodeValue1816, Sparse.eval] using hc.symm

theorem sound1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1817 node1817Labels = Sparse.eval nodeValue1817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1817) = mixedMoment B node1817 node1817Labels := rfl
  simpa [nodeValue1817, Sparse.eval] using hc.symm

theorem sound1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1818 node1818Labels = Sparse.eval nodeValue1818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1818) = mixedMoment B node1818 node1818Labels := rfl
  simpa [nodeValue1818, Sparse.eval] using hc.symm

theorem sound1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1819 node1819Labels = Sparse.eval nodeValue1819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1819) = mixedMoment B node1819 node1819Labels := rfl
  simpa [nodeValue1819, Sparse.eval] using hc.symm

theorem sound1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1820 node1820Labels = Sparse.eval nodeValue1820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1820) = mixedMoment B node1820 node1820Labels := rfl
  simpa [nodeValue1820, Sparse.eval] using hc.symm

theorem sound1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1821 node1821Labels = Sparse.eval nodeValue1821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1821) = mixedMoment B node1821 node1821Labels := rfl
  simpa [nodeValue1821, Sparse.eval] using hc.symm

theorem sound1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1822 node1822Labels = Sparse.eval nodeValue1822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1822) = mixedMoment B node1822 node1822Labels := rfl
  simpa [nodeValue1822, Sparse.eval] using hc.symm

theorem sound1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1823 node1823Labels = Sparse.eval nodeValue1823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1823) = mixedMoment B node1823 node1823Labels := rfl
  simpa [nodeValue1823, Sparse.eval] using hc.symm

theorem sound1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1824 node1824Labels = Sparse.eval nodeValue1824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1824) = mixedMoment B node1824 node1824Labels := rfl
  simpa [nodeValue1824, Sparse.eval] using hc.symm

theorem sound1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1825 node1825Labels = Sparse.eval nodeValue1825 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1825) = mixedMoment B node1825 node1825Labels := rfl
  simpa [nodeValue1825, Sparse.eval] using hc.symm

theorem sound1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1826 node1826Labels = Sparse.eval nodeValue1826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1826) = mixedMoment B node1826 node1826Labels := rfl
  simpa [nodeValue1826, Sparse.eval] using hc.symm

theorem sound1827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1827 node1827Labels = Sparse.eval nodeValue1827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1827) = mixedMoment B node1827 node1827Labels := rfl
  simpa [nodeValue1827, Sparse.eval] using hc.symm

theorem sound1828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1828 node1828Labels = Sparse.eval nodeValue1828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1828) = mixedMoment B node1828 node1828Labels := rfl
  simpa [nodeValue1828, Sparse.eval] using hc.symm

theorem sound1829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1829 node1829Labels = Sparse.eval nodeValue1829 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1829) = mixedMoment B node1829 node1829Labels := rfl
  simpa [nodeValue1829, Sparse.eval] using hc.symm

theorem sound1830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1830 node1830Labels = Sparse.eval nodeValue1830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1830) = mixedMoment B node1830 node1830Labels := rfl
  simpa [nodeValue1830, Sparse.eval] using hc.symm

theorem sound1831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1831 node1831Labels = Sparse.eval nodeValue1831 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1831) = mixedMoment B node1831 node1831Labels := rfl
  simpa [nodeValue1831, Sparse.eval] using hc.symm

theorem sound1832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1832 node1832Labels = Sparse.eval nodeValue1832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1832) = mixedMoment B node1832 node1832Labels := rfl
  simpa [nodeValue1832, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1957 node1957Labels = Sparse.eval nodeValue1957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1957) = mixedMoment B node1957 node1957Labels := rfl
  simpa [nodeValue1957, Sparse.eval] using hc.symm

theorem sound1964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1964 node1964Labels = Sparse.eval nodeValue1964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1964) = mixedMoment B node1964 node1964Labels := rfl
  simpa [nodeValue1964, Sparse.eval] using hc.symm

theorem sound1965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1965 node1965Labels = Sparse.eval nodeValue1965 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1965) = mixedMoment B node1965 node1965Labels := rfl
  simpa [nodeValue1965, Sparse.eval] using hc.symm

theorem sound1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1966 node1966Labels = Sparse.eval nodeValue1966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1966) = mixedMoment B node1966 node1966Labels := rfl
  simpa [nodeValue1966, Sparse.eval] using hc.symm

theorem sound1967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1967 node1967Labels = Sparse.eval nodeValue1967 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1967) = mixedMoment B node1967 node1967Labels := rfl
  simpa [nodeValue1967, Sparse.eval] using hc.symm

theorem sound1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1970 node1970Labels = Sparse.eval nodeValue1970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1970) = mixedMoment B node1970 node1970Labels := rfl
  simpa [nodeValue1970, Sparse.eval] using hc.symm

theorem sound1971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1971 node1971Labels = Sparse.eval nodeValue1971 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1971) = mixedMoment B node1971 node1971Labels := rfl
  simpa [nodeValue1971, Sparse.eval] using hc.symm

theorem sound1973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1973 node1973Labels = Sparse.eval nodeValue1973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1973) = mixedMoment B node1973 node1973Labels := rfl
  simpa [nodeValue1973, Sparse.eval] using hc.symm

theorem sound1976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1976 node1976Labels = Sparse.eval nodeValue1976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1976) = mixedMoment B node1976 node1976Labels := rfl
  simpa [nodeValue1976, Sparse.eval] using hc.symm

theorem sound1977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1977 node1977Labels = Sparse.eval nodeValue1977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1977) = mixedMoment B node1977 node1977Labels := rfl
  simpa [nodeValue1977, Sparse.eval] using hc.symm

theorem sound1978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1978 node1978Labels = Sparse.eval nodeValue1978 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1978) = mixedMoment B node1978 node1978Labels := rfl
  simpa [nodeValue1978, Sparse.eval] using hc.symm

theorem sound1979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1979 node1979Labels = Sparse.eval nodeValue1979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1979) = mixedMoment B node1979 node1979Labels := rfl
  simpa [nodeValue1979, Sparse.eval] using hc.symm

theorem sound1980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1980 node1980Labels = Sparse.eval nodeValue1980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1980) = mixedMoment B node1980 node1980Labels := rfl
  simpa [nodeValue1980, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2010 node2010Labels = Sparse.eval nodeValue2010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2010) = mixedMoment B node2010 node2010Labels := rfl
  simpa [nodeValue2010, Sparse.eval] using hc.symm

theorem sound2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2019 node2019Labels = Sparse.eval nodeValue2019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2019) = mixedMoment B node2019 node2019Labels := rfl
  simpa [nodeValue2019, Sparse.eval] using hc.symm

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

theorem sound2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2026 node2026Labels = Sparse.eval nodeValue2026 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2026) = mixedMoment B node2026 node2026Labels := rfl
  simpa [nodeValue2026, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

theorem sound2037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2037 node2037Labels = Sparse.eval nodeValue2037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2037) = mixedMoment B node2037 node2037Labels := rfl
  simpa [nodeValue2037, Sparse.eval] using hc.symm

theorem sound2039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2039 node2039Labels = Sparse.eval nodeValue2039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2039) = mixedMoment B node2039 node2039Labels := rfl
  simpa [nodeValue2039, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2051 node2051Labels = Sparse.eval nodeValue2051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2051) = mixedMoment B node2051 node2051Labels := rfl
  simpa [nodeValue2051, Sparse.eval] using hc.symm

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

theorem sound2088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2088 node2088Labels = Sparse.eval nodeValue2088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2088) = mixedMoment B node2088 node2088Labels := rfl
  simpa [nodeValue2088, Sparse.eval] using hc.symm

theorem sound2089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2089 node2089Labels = Sparse.eval nodeValue2089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2089) = mixedMoment B node2089 node2089Labels := rfl
  simpa [nodeValue2089, Sparse.eval] using hc.symm

theorem sound2090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2090 node2090Labels = Sparse.eval nodeValue2090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2090) = mixedMoment B node2090 node2090Labels := rfl
  simpa [nodeValue2090, Sparse.eval] using hc.symm

theorem sound2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2092 node2092Labels = Sparse.eval nodeValue2092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2092) = mixedMoment B node2092 node2092Labels := rfl
  simpa [nodeValue2092, Sparse.eval] using hc.symm

theorem sound2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2094 node2094Labels = Sparse.eval nodeValue2094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2094) = mixedMoment B node2094 node2094Labels := rfl
  simpa [nodeValue2094, Sparse.eval] using hc.symm

theorem sound2104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2104 node2104Labels = Sparse.eval nodeValue2104 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2104) = mixedMoment B node2104 node2104Labels := rfl
  simpa [nodeValue2104, Sparse.eval] using hc.symm

theorem sound2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2105 node2105Labels = Sparse.eval nodeValue2105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2105) = mixedMoment B node2105 node2105Labels := rfl
  simpa [nodeValue2105, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

theorem sound2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2108 node2108Labels = Sparse.eval nodeValue2108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2108) = mixedMoment B node2108 node2108Labels := rfl
  simpa [nodeValue2108, Sparse.eval] using hc.symm

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

theorem sound2113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2113 node2113Labels = Sparse.eval nodeValue2113 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2113) = mixedMoment B node2113 node2113Labels := rfl
  simpa [nodeValue2113, Sparse.eval] using hc.symm

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

theorem sound2116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2116 node2116Labels = Sparse.eval nodeValue2116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2116) = mixedMoment B node2116 node2116Labels := rfl
  simpa [nodeValue2116, Sparse.eval] using hc.symm

theorem sound2131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2131 node2131Labels = Sparse.eval nodeValue2131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2131) = mixedMoment B node2131 node2131Labels := rfl
  simpa [nodeValue2131, Sparse.eval] using hc.symm

theorem sound2132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2132 node2132Labels = Sparse.eval nodeValue2132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2132) = mixedMoment B node2132 node2132Labels := rfl
  simpa [nodeValue2132, Sparse.eval] using hc.symm

theorem sound2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2133 node2133Labels = Sparse.eval nodeValue2133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2133) = mixedMoment B node2133 node2133Labels := rfl
  simpa [nodeValue2133, Sparse.eval] using hc.symm

theorem sound2134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2134 node2134Labels = Sparse.eval nodeValue2134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2134) = mixedMoment B node2134 node2134Labels := rfl
  simpa [nodeValue2134, Sparse.eval] using hc.symm

theorem sound2136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2136 node2136Labels = Sparse.eval nodeValue2136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2136) = mixedMoment B node2136 node2136Labels := rfl
  simpa [nodeValue2136, Sparse.eval] using hc.symm

theorem sound2138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2138 node2138Labels = Sparse.eval nodeValue2138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2138) = mixedMoment B node2138 node2138Labels := rfl
  simpa [nodeValue2138, Sparse.eval] using hc.symm

theorem sound2140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2140 node2140Labels = Sparse.eval nodeValue2140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2140) = mixedMoment B node2140 node2140Labels := rfl
  simpa [nodeValue2140, Sparse.eval] using hc.symm

theorem sound2142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2142 node2142Labels = Sparse.eval nodeValue2142 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2142) = mixedMoment B node2142 node2142Labels := rfl
  simpa [nodeValue2142, Sparse.eval] using hc.symm

theorem sound2144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2144 node2144Labels = Sparse.eval nodeValue2144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2144) = mixedMoment B node2144 node2144Labels := rfl
  simpa [nodeValue2144, Sparse.eval] using hc.symm

theorem sound2145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2145 node2145Labels = Sparse.eval nodeValue2145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2145) = mixedMoment B node2145 node2145Labels := rfl
  simpa [nodeValue2145, Sparse.eval] using hc.symm

theorem sound2146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2146 node2146Labels = Sparse.eval nodeValue2146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2146) = mixedMoment B node2146 node2146Labels := rfl
  simpa [nodeValue2146, Sparse.eval] using hc.symm

theorem sound2147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2147 node2147Labels = Sparse.eval nodeValue2147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2147) = mixedMoment B node2147 node2147Labels := rfl
  simpa [nodeValue2147, Sparse.eval] using hc.symm

theorem sound2148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2148 node2148Labels = Sparse.eval nodeValue2148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2148) = mixedMoment B node2148 node2148Labels := rfl
  simpa [nodeValue2148, Sparse.eval] using hc.symm

theorem sound2149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2149 node2149Labels = Sparse.eval nodeValue2149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2149) = mixedMoment B node2149 node2149Labels := rfl
  simpa [nodeValue2149, Sparse.eval] using hc.symm

theorem sound2153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2153 node2153Labels = Sparse.eval nodeValue2153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2153) = mixedMoment B node2153 node2153Labels := rfl
  simpa [nodeValue2153, Sparse.eval] using hc.symm

theorem sound2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2154 node2154Labels = Sparse.eval nodeValue2154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2154) = mixedMoment B node2154 node2154Labels := rfl
  simpa [nodeValue2154, Sparse.eval] using hc.symm

theorem sound2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2155 node2155Labels = Sparse.eval nodeValue2155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2155) = mixedMoment B node2155 node2155Labels := rfl
  simpa [nodeValue2155, Sparse.eval] using hc.symm

theorem sound2158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2158 node2158Labels = Sparse.eval nodeValue2158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2158) = mixedMoment B node2158 node2158Labels := rfl
  simpa [nodeValue2158, Sparse.eval] using hc.symm

theorem sound2160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2160 node2160Labels = Sparse.eval nodeValue2160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2160) = mixedMoment B node2160 node2160Labels := rfl
  simpa [nodeValue2160, Sparse.eval] using hc.symm

theorem sound2161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2161 node2161Labels = Sparse.eval nodeValue2161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2161) = mixedMoment B node2161 node2161Labels := rfl
  simpa [nodeValue2161, Sparse.eval] using hc.symm

theorem sound2162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2162 node2162Labels = Sparse.eval nodeValue2162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2162) = mixedMoment B node2162 node2162Labels := rfl
  simpa [nodeValue2162, Sparse.eval] using hc.symm

theorem sound2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2163 node2163Labels = Sparse.eval nodeValue2163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2163) = mixedMoment B node2163 node2163Labels := rfl
  simpa [nodeValue2163, Sparse.eval] using hc.symm

theorem sound2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2164 node2164Labels = Sparse.eval nodeValue2164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2164) = mixedMoment B node2164 node2164Labels := rfl
  simpa [nodeValue2164, Sparse.eval] using hc.symm

theorem sound2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2171 node2171Labels = Sparse.eval nodeValue2171 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2171) = mixedMoment B node2171 node2171Labels := rfl
  simpa [nodeValue2171, Sparse.eval] using hc.symm

theorem sound2172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2172 node2172Labels = Sparse.eval nodeValue2172 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2172) = mixedMoment B node2172 node2172Labels := rfl
  simpa [nodeValue2172, Sparse.eval] using hc.symm

theorem sound2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2175 node2175Labels = Sparse.eval nodeValue2175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2175) = mixedMoment B node2175 node2175Labels := rfl
  simpa [nodeValue2175, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2176 node2176Labels = Sparse.eval nodeValue2176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2176) = mixedMoment B node2176 node2176Labels := rfl
  simpa [nodeValue2176, Sparse.eval] using hc.symm

theorem sound2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2178 node2178Labels = Sparse.eval nodeValue2178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2178) = mixedMoment B node2178 node2178Labels := rfl
  simpa [nodeValue2178, Sparse.eval] using hc.symm

theorem sound2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2179 node2179Labels = Sparse.eval nodeValue2179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2179) = mixedMoment B node2179 node2179Labels := rfl
  simpa [nodeValue2179, Sparse.eval] using hc.symm

theorem sound2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2180 node2180Labels = Sparse.eval nodeValue2180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2180) = mixedMoment B node2180 node2180Labels := rfl
  simpa [nodeValue2180, Sparse.eval] using hc.symm

theorem sound2181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2181 node2181Labels = Sparse.eval nodeValue2181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2181) = mixedMoment B node2181 node2181Labels := rfl
  simpa [nodeValue2181, Sparse.eval] using hc.symm

theorem sound2187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2187 node2187Labels = Sparse.eval nodeValue2187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2187) = mixedMoment B node2187 node2187Labels := rfl
  simpa [nodeValue2187, Sparse.eval] using hc.symm

theorem sound2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2189 node2189Labels = Sparse.eval nodeValue2189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2189) = mixedMoment B node2189 node2189Labels := rfl
  simpa [nodeValue2189, Sparse.eval] using hc.symm

theorem sound2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2192 node2192Labels = Sparse.eval nodeValue2192 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2192) = mixedMoment B node2192 node2192Labels := rfl
  simpa [nodeValue2192, Sparse.eval] using hc.symm

theorem sound2194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2194 node2194Labels = Sparse.eval nodeValue2194 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2194) = mixedMoment B node2194 node2194Labels := rfl
  simpa [nodeValue2194, Sparse.eval] using hc.symm

theorem sound2195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2195 node2195Labels = Sparse.eval nodeValue2195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2195) = mixedMoment B node2195 node2195Labels := rfl
  simpa [nodeValue2195, Sparse.eval] using hc.symm

theorem sound2196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2196 node2196Labels = Sparse.eval nodeValue2196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2196) = mixedMoment B node2196 node2196Labels := rfl
  simpa [nodeValue2196, Sparse.eval] using hc.symm

theorem sound2197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2197 node2197Labels = Sparse.eval nodeValue2197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2197) = mixedMoment B node2197 node2197Labels := rfl
  simpa [nodeValue2197, Sparse.eval] using hc.symm

theorem sound2198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2198 node2198Labels = Sparse.eval nodeValue2198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2198) = mixedMoment B node2198 node2198Labels := rfl
  simpa [nodeValue2198, Sparse.eval] using hc.symm

theorem sound2199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2199 node2199Labels = Sparse.eval nodeValue2199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2199) = mixedMoment B node2199 node2199Labels := rfl
  simpa [nodeValue2199, Sparse.eval] using hc.symm

theorem sound2200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2200 node2200Labels = Sparse.eval nodeValue2200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2200) = mixedMoment B node2200 node2200Labels := rfl
  simpa [nodeValue2200, Sparse.eval] using hc.symm

theorem sound2201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2201 node2201Labels = Sparse.eval nodeValue2201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2201) = mixedMoment B node2201 node2201Labels := rfl
  simpa [nodeValue2201, Sparse.eval] using hc.symm

theorem sound2207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2207 node2207Labels = Sparse.eval nodeValue2207 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2207) = mixedMoment B node2207 node2207Labels := rfl
  simpa [nodeValue2207, Sparse.eval] using hc.symm

theorem sound2211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2211 node2211Labels = Sparse.eval nodeValue2211 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2211) = mixedMoment B node2211 node2211Labels := rfl
  simpa [nodeValue2211, Sparse.eval] using hc.symm

theorem sound2212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2212 node2212Labels = Sparse.eval nodeValue2212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2212) = mixedMoment B node2212 node2212Labels := rfl
  simpa [nodeValue2212, Sparse.eval] using hc.symm

theorem sound2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2213 node2213Labels = Sparse.eval nodeValue2213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2213) = mixedMoment B node2213 node2213Labels := rfl
  simpa [nodeValue2213, Sparse.eval] using hc.symm

theorem sound2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2217 node2217Labels = Sparse.eval nodeValue2217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2217) = mixedMoment B node2217 node2217Labels := rfl
  simpa [nodeValue2217, Sparse.eval] using hc.symm

theorem sound2219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2219 node2219Labels = Sparse.eval nodeValue2219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2219) = mixedMoment B node2219 node2219Labels := rfl
  simpa [nodeValue2219, Sparse.eval] using hc.symm

theorem sound2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2220 node2220Labels = Sparse.eval nodeValue2220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2220) = mixedMoment B node2220 node2220Labels := rfl
  simpa [nodeValue2220, Sparse.eval] using hc.symm

theorem sound2221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2221 node2221Labels = Sparse.eval nodeValue2221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2221) = mixedMoment B node2221 node2221Labels := rfl
  simpa [nodeValue2221, Sparse.eval] using hc.symm

theorem sound2222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2222 node2222Labels = Sparse.eval nodeValue2222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2222) = mixedMoment B node2222 node2222Labels := rfl
  simpa [nodeValue2222, Sparse.eval] using hc.symm

theorem sound2223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2223 node2223Labels = Sparse.eval nodeValue2223 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2223) = mixedMoment B node2223 node2223Labels := rfl
  simpa [nodeValue2223, Sparse.eval] using hc.symm

theorem sound2231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2231 node2231Labels = Sparse.eval nodeValue2231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2231) = mixedMoment B node2231 node2231Labels := rfl
  simpa [nodeValue2231, Sparse.eval] using hc.symm

theorem sound2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2232 node2232Labels = Sparse.eval nodeValue2232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2232) = mixedMoment B node2232 node2232Labels := rfl
  simpa [nodeValue2232, Sparse.eval] using hc.symm

theorem sound2233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2233 node2233Labels = Sparse.eval nodeValue2233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2233) = mixedMoment B node2233 node2233Labels := rfl
  simpa [nodeValue2233, Sparse.eval] using hc.symm

theorem sound2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2234 node2234Labels = Sparse.eval nodeValue2234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2234) = mixedMoment B node2234 node2234Labels := rfl
  simpa [nodeValue2234, Sparse.eval] using hc.symm

theorem sound2235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2235 node2235Labels = Sparse.eval nodeValue2235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2235) = mixedMoment B node2235 node2235Labels := rfl
  simpa [nodeValue2235, Sparse.eval] using hc.symm

theorem sound2238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2238 node2238Labels = Sparse.eval nodeValue2238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2238) = mixedMoment B node2238 node2238Labels := rfl
  simpa [nodeValue2238, Sparse.eval] using hc.symm

theorem sound2239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2239 node2239Labels = Sparse.eval nodeValue2239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2239) = mixedMoment B node2239 node2239Labels := rfl
  simpa [nodeValue2239, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = 0 := by
  exact mixedMoment_order_one B hB node2263 node2263Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = 0 := by
  exact mixedMoment_order_one B hB node2265 node2265Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = 0 := by
  exact mixedMoment_order_one B hB node2268 node2268Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = 0 := by
  exact mixedMoment_order_one B hB node2293 node2293Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2240 node2240Labels = Sparse.eval nodeValue2240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2240) = mixedMoment B node2240 node2240Labels := rfl
  simpa [nodeValue2240, Sparse.eval] using hc.symm

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2246 node2246Labels = Sparse.eval nodeValue2246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2246) = mixedMoment B node2246 node2246Labels := rfl
  simpa [nodeValue2246, Sparse.eval] using hc.symm

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2248 node2248Labels = Sparse.eval nodeValue2248 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2248) = mixedMoment B node2248 node2248Labels := rfl
  simpa [nodeValue2248, Sparse.eval] using hc.symm

theorem sound2249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2249 node2249Labels = Sparse.eval nodeValue2249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2249) = mixedMoment B node2249 node2249Labels := rfl
  simpa [nodeValue2249, Sparse.eval] using hc.symm

theorem sound2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2250 node2250Labels = Sparse.eval nodeValue2250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2250) = mixedMoment B node2250 node2250Labels := rfl
  simpa [nodeValue2250, Sparse.eval] using hc.symm

theorem sound2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2251 node2251Labels = Sparse.eval nodeValue2251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2251) = mixedMoment B node2251 node2251Labels := rfl
  simpa [nodeValue2251, Sparse.eval] using hc.symm

theorem sound2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2252 node2252Labels = Sparse.eval nodeValue2252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2252) = mixedMoment B node2252 node2252Labels := rfl
  simpa [nodeValue2252, Sparse.eval] using hc.symm

theorem sound2253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2253 node2253Labels = Sparse.eval nodeValue2253 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2253) = mixedMoment B node2253 node2253Labels := rfl
  simpa [nodeValue2253, Sparse.eval] using hc.symm

theorem sound2254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2254 node2254Labels = Sparse.eval nodeValue2254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2254) = mixedMoment B node2254 node2254Labels := rfl
  simpa [nodeValue2254, Sparse.eval] using hc.symm

theorem sound2255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2255 node2255Labels = Sparse.eval nodeValue2255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2255) = mixedMoment B node2255 node2255Labels := rfl
  simpa [nodeValue2255, Sparse.eval] using hc.symm

theorem sound2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2256 node2256Labels = Sparse.eval nodeValue2256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2256) = mixedMoment B node2256 node2256Labels := rfl
  simpa [nodeValue2256, Sparse.eval] using hc.symm

theorem sound2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2257 node2257Labels = Sparse.eval nodeValue2257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2257) = mixedMoment B node2257 node2257Labels := rfl
  simpa [nodeValue2257, Sparse.eval] using hc.symm

theorem sound2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2258 node2258Labels = Sparse.eval nodeValue2258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2258) = mixedMoment B node2258 node2258Labels := rfl
  simpa [nodeValue2258, Sparse.eval] using hc.symm

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = Sparse.eval nodeValue2265 (mixedVector B) := by
  simpa only [nodeValue2265, Sparse.eval_nil] using zero2265 B _hB _hF

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2267 node2267Labels = Sparse.eval nodeValue2267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2267) = mixedMoment B node2267 node2267Labels := rfl
  simpa [nodeValue2267, Sparse.eval] using hc.symm

theorem sound2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = Sparse.eval nodeValue2268 (mixedVector B) := by
  simpa only [nodeValue2268, Sparse.eval_nil] using zero2268 B _hB _hF

theorem sound2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2272 node2272Labels = Sparse.eval nodeValue2272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2272) = mixedMoment B node2272 node2272Labels := rfl
  simpa [nodeValue2272, Sparse.eval] using hc.symm

theorem sound2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2273 node2273Labels = Sparse.eval nodeValue2273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2273) = mixedMoment B node2273 node2273Labels := rfl
  simpa [nodeValue2273, Sparse.eval] using hc.symm

theorem sound2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2274 node2274Labels = Sparse.eval nodeValue2274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2274) = mixedMoment B node2274 node2274Labels := rfl
  simpa [nodeValue2274, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2280 node2280Labels = Sparse.eval nodeValue2280 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2280) = mixedMoment B node2280 node2280Labels := rfl
  simpa [nodeValue2280, Sparse.eval] using hc.symm

theorem sound2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2282 node2282Labels = Sparse.eval nodeValue2282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2282) = mixedMoment B node2282 node2282Labels := rfl
  simpa [nodeValue2282, Sparse.eval] using hc.symm

theorem sound2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2283 node2283Labels = Sparse.eval nodeValue2283 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2283) = mixedMoment B node2283 node2283Labels := rfl
  simpa [nodeValue2283, Sparse.eval] using hc.symm

theorem sound2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2284 node2284Labels = Sparse.eval nodeValue2284 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2284) = mixedMoment B node2284 node2284Labels := rfl
  simpa [nodeValue2284, Sparse.eval] using hc.symm

theorem sound2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2285 node2285Labels = Sparse.eval nodeValue2285 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2285) = mixedMoment B node2285 node2285Labels := rfl
  simpa [nodeValue2285, Sparse.eval] using hc.symm

theorem sound2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2286 node2286Labels = Sparse.eval nodeValue2286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2286) = mixedMoment B node2286 node2286Labels := rfl
  simpa [nodeValue2286, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2323 node2323Labels = Sparse.eval nodeValue2323 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2323) = mixedMoment B node2323 node2323Labels := rfl
  simpa [nodeValue2323, Sparse.eval] using hc.symm

theorem sound2327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2327 node2327Labels = Sparse.eval nodeValue2327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2327) = mixedMoment B node2327 node2327Labels := rfl
  simpa [nodeValue2327, Sparse.eval] using hc.symm

theorem sound2330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2330 node2330Labels = Sparse.eval nodeValue2330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2330) = mixedMoment B node2330 node2330Labels := rfl
  simpa [nodeValue2330, Sparse.eval] using hc.symm

theorem sound2332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2332 node2332Labels = Sparse.eval nodeValue2332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2332) = mixedMoment B node2332 node2332Labels := rfl
  simpa [nodeValue2332, Sparse.eval] using hc.symm

theorem sound2334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2334 node2334Labels = Sparse.eval nodeValue2334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2334) = mixedMoment B node2334 node2334Labels := rfl
  simpa [nodeValue2334, Sparse.eval] using hc.symm

theorem sound2337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2337 node2337Labels = Sparse.eval nodeValue2337 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2337) = mixedMoment B node2337 node2337Labels := rfl
  simpa [nodeValue2337, Sparse.eval] using hc.symm

theorem sound2338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2338 node2338Labels = Sparse.eval nodeValue2338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2338) = mixedMoment B node2338 node2338Labels := rfl
  simpa [nodeValue2338, Sparse.eval] using hc.symm

theorem sound2339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2339 node2339Labels = Sparse.eval nodeValue2339 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2339) = mixedMoment B node2339 node2339Labels := rfl
  simpa [nodeValue2339, Sparse.eval] using hc.symm

theorem sound2340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2340 node2340Labels = Sparse.eval nodeValue2340 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2340) = mixedMoment B node2340 node2340Labels := rfl
  simpa [nodeValue2340, Sparse.eval] using hc.symm

theorem sound2341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2341 node2341Labels = Sparse.eval nodeValue2341 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2341) = mixedMoment B node2341 node2341Labels := rfl
  simpa [nodeValue2341, Sparse.eval] using hc.symm

theorem sound2342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2342 node2342Labels = Sparse.eval nodeValue2342 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2342) = mixedMoment B node2342 node2342Labels := rfl
  simpa [nodeValue2342, Sparse.eval] using hc.symm

theorem sound2344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2344 node2344Labels = Sparse.eval nodeValue2344 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2344) = mixedMoment B node2344 node2344Labels := rfl
  simpa [nodeValue2344, Sparse.eval] using hc.symm

theorem sound2345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2345 node2345Labels = Sparse.eval nodeValue2345 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2345) = mixedMoment B node2345 node2345Labels := rfl
  simpa [nodeValue2345, Sparse.eval] using hc.symm

theorem sound2346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2346 node2346Labels = Sparse.eval nodeValue2346 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2346) = mixedMoment B node2346 node2346Labels := rfl
  simpa [nodeValue2346, Sparse.eval] using hc.symm

theorem sound2347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2347 node2347Labels = Sparse.eval nodeValue2347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2347) = mixedMoment B node2347 node2347Labels := rfl
  simpa [nodeValue2347, Sparse.eval] using hc.symm

theorem sound2348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2348 node2348Labels = Sparse.eval nodeValue2348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2348) = mixedMoment B node2348 node2348Labels := rfl
  simpa [nodeValue2348, Sparse.eval] using hc.symm

theorem sound2349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2349 node2349Labels = Sparse.eval nodeValue2349 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2349) = mixedMoment B node2349 node2349Labels := rfl
  simpa [nodeValue2349, Sparse.eval] using hc.symm

theorem sound2350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2350 node2350Labels = Sparse.eval nodeValue2350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2350) = mixedMoment B node2350 node2350Labels := rfl
  simpa [nodeValue2350, Sparse.eval] using hc.symm

theorem sound2352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2352 node2352Labels = Sparse.eval nodeValue2352 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2352) = mixedMoment B node2352 node2352Labels := rfl
  simpa [nodeValue2352, Sparse.eval] using hc.symm

theorem sound2353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2353 node2353Labels = Sparse.eval nodeValue2353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2353) = mixedMoment B node2353 node2353Labels := rfl
  simpa [nodeValue2353, Sparse.eval] using hc.symm

theorem sound2355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2355 node2355Labels = Sparse.eval nodeValue2355 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2355) = mixedMoment B node2355 node2355Labels := rfl
  simpa [nodeValue2355, Sparse.eval] using hc.symm

theorem sound2356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2356 node2356Labels = Sparse.eval nodeValue2356 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2356) = mixedMoment B node2356 node2356Labels := rfl
  simpa [nodeValue2356, Sparse.eval] using hc.symm

theorem sound2361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2361 node2361Labels = Sparse.eval nodeValue2361 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2361) = mixedMoment B node2361 node2361Labels := rfl
  simpa [nodeValue2361, Sparse.eval] using hc.symm

theorem sound2362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2362 node2362Labels = Sparse.eval nodeValue2362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2362) = mixedMoment B node2362 node2362Labels := rfl
  simpa [nodeValue2362, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2423 node2423Labels = Sparse.eval nodeValue2423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2423) = mixedMoment B node2423 node2423Labels := rfl
  simpa [nodeValue2423, Sparse.eval] using hc.symm

theorem sound2425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2425 node2425Labels = Sparse.eval nodeValue2425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2425) = mixedMoment B node2425 node2425Labels := rfl
  simpa [nodeValue2425, Sparse.eval] using hc.symm

theorem sound2426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2426 node2426Labels = Sparse.eval nodeValue2426 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2426) = mixedMoment B node2426 node2426Labels := rfl
  simpa [nodeValue2426, Sparse.eval] using hc.symm

theorem sound2428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2428 node2428Labels = Sparse.eval nodeValue2428 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2428) = mixedMoment B node2428 node2428Labels := rfl
  simpa [nodeValue2428, Sparse.eval] using hc.symm

theorem sound2429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2429 node2429Labels = Sparse.eval nodeValue2429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2429) = mixedMoment B node2429 node2429Labels := rfl
  simpa [nodeValue2429, Sparse.eval] using hc.symm

theorem sound2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2430 node2430Labels = Sparse.eval nodeValue2430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2430) = mixedMoment B node2430 node2430Labels := rfl
  simpa [nodeValue2430, Sparse.eval] using hc.symm

theorem sound2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2431 node2431Labels = Sparse.eval nodeValue2431 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2431) = mixedMoment B node2431 node2431Labels := rfl
  simpa [nodeValue2431, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2432 node2432Labels = Sparse.eval nodeValue2432 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2432) = mixedMoment B node2432 node2432Labels := rfl
  simpa [nodeValue2432, Sparse.eval] using hc.symm

theorem sound2433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2433 node2433Labels = Sparse.eval nodeValue2433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2433) = mixedMoment B node2433 node2433Labels := rfl
  simpa [nodeValue2433, Sparse.eval] using hc.symm

theorem sound2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2434 node2434Labels = Sparse.eval nodeValue2434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2434) = mixedMoment B node2434 node2434Labels := rfl
  simpa [nodeValue2434, Sparse.eval] using hc.symm

theorem sound2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2435 node2435Labels = Sparse.eval nodeValue2435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2435) = mixedMoment B node2435 node2435Labels := rfl
  simpa [nodeValue2435, Sparse.eval] using hc.symm

theorem sound2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2437 node2437Labels = Sparse.eval nodeValue2437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2437) = mixedMoment B node2437 node2437Labels := rfl
  simpa [nodeValue2437, Sparse.eval] using hc.symm

theorem sound2438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2438 node2438Labels = Sparse.eval nodeValue2438 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2438) = mixedMoment B node2438 node2438Labels := rfl
  simpa [nodeValue2438, Sparse.eval] using hc.symm

theorem sound2440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2440 node2440Labels = Sparse.eval nodeValue2440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2440) = mixedMoment B node2440 node2440Labels := rfl
  simpa [nodeValue2440, Sparse.eval] using hc.symm

theorem sound2441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2441 node2441Labels = Sparse.eval nodeValue2441 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2441) = mixedMoment B node2441 node2441Labels := rfl
  simpa [nodeValue2441, Sparse.eval] using hc.symm

theorem sound2442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2442 node2442Labels = Sparse.eval nodeValue2442 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2442) = mixedMoment B node2442 node2442Labels := rfl
  simpa [nodeValue2442, Sparse.eval] using hc.symm

theorem sound2443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2443 node2443Labels = Sparse.eval nodeValue2443 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2443) = mixedMoment B node2443 node2443Labels := rfl
  simpa [nodeValue2443, Sparse.eval] using hc.symm

theorem sound2470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2470 node2470Labels = Sparse.eval nodeValue2470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2470) = mixedMoment B node2470 node2470Labels := rfl
  simpa [nodeValue2470, Sparse.eval] using hc.symm

theorem sound2471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2471 node2471Labels = Sparse.eval nodeValue2471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2471) = mixedMoment B node2471 node2471Labels := rfl
  simpa [nodeValue2471, Sparse.eval] using hc.symm

theorem sound2473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2473 node2473Labels = Sparse.eval nodeValue2473 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2473) = mixedMoment B node2473 node2473Labels := rfl
  simpa [nodeValue2473, Sparse.eval] using hc.symm

theorem sound2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2479 node2479Labels = Sparse.eval nodeValue2479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2479) = mixedMoment B node2479 node2479Labels := rfl
  simpa [nodeValue2479, Sparse.eval] using hc.symm

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

theorem sound2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2483 node2483Labels = Sparse.eval nodeValue2483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2483) = mixedMoment B node2483 node2483Labels := rfl
  simpa [nodeValue2483, Sparse.eval] using hc.symm

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

theorem sound2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2486 node2486Labels = Sparse.eval nodeValue2486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2486) = mixedMoment B node2486 node2486Labels := rfl
  simpa [nodeValue2486, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

theorem sound2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2489 node2489Labels = Sparse.eval nodeValue2489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2489) = mixedMoment B node2489 node2489Labels := rfl
  simpa [nodeValue2489, Sparse.eval] using hc.symm

theorem sound2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2494 node2494Labels = Sparse.eval nodeValue2494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2494) = mixedMoment B node2494 node2494Labels := rfl
  simpa [nodeValue2494, Sparse.eval] using hc.symm

theorem sound2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2495 node2495Labels = Sparse.eval nodeValue2495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2495) = mixedMoment B node2495 node2495Labels := rfl
  simpa [nodeValue2495, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2497 node2497Labels = Sparse.eval nodeValue2497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2497) = mixedMoment B node2497 node2497Labels := rfl
  simpa [nodeValue2497, Sparse.eval] using hc.symm

theorem sound2499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2499 node2499Labels = Sparse.eval nodeValue2499 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2499) = mixedMoment B node2499 node2499Labels := rfl
  simpa [nodeValue2499, Sparse.eval] using hc.symm

theorem sound2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2508 node2508Labels = Sparse.eval nodeValue2508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2508) = mixedMoment B node2508 node2508Labels := rfl
  simpa [nodeValue2508, Sparse.eval] using hc.symm

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

theorem sound2513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2513 node2513Labels = Sparse.eval nodeValue2513 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2513) = mixedMoment B node2513 node2513Labels := rfl
  simpa [nodeValue2513, Sparse.eval] using hc.symm

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

theorem sound2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2519 node2519Labels = Sparse.eval nodeValue2519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2519) = mixedMoment B node2519 node2519Labels := rfl
  simpa [nodeValue2519, Sparse.eval] using hc.symm

theorem sound2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2520 node2520Labels = Sparse.eval nodeValue2520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2520) = mixedMoment B node2520 node2520Labels := rfl
  simpa [nodeValue2520, Sparse.eval] using hc.symm

theorem sound2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2522 node2522Labels = Sparse.eval nodeValue2522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2522) = mixedMoment B node2522 node2522Labels := rfl
  simpa [nodeValue2522, Sparse.eval] using hc.symm

theorem sound2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2524 node2524Labels = Sparse.eval nodeValue2524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2524) = mixedMoment B node2524 node2524Labels := rfl
  simpa [nodeValue2524, Sparse.eval] using hc.symm

theorem sound2529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2529 node2529Labels = Sparse.eval nodeValue2529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2529) = mixedMoment B node2529 node2529Labels := rfl
  simpa [nodeValue2529, Sparse.eval] using hc.symm

theorem sound2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2545 node2545Labels = Sparse.eval nodeValue2545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2545) = mixedMoment B node2545 node2545Labels := rfl
  simpa [nodeValue2545, Sparse.eval] using hc.symm

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic719 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm719 x = (2797448960684851200000 : ℝ) * Sparse.eval nodeValue1804 x := by
  norm_num [reducedTerm719, nodeValue1804, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic720 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm720 x = (3885170543988572160000 : ℝ) * Sparse.eval nodeValue1805 x := by
  norm_num [reducedTerm720, nodeValue1805, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic721 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm721 x = (-9608222007357603840000 : ℝ) * Sparse.eval nodeValue1806 x := by
  norm_num [reducedTerm721, nodeValue1806, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic722 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm722 x = (9318508415649054720000 : ℝ) * Sparse.eval nodeValue1807 x := by
  norm_num [reducedTerm722, nodeValue1807, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic723 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm723 x = (-4955053941050572800000 : ℝ) * Sparse.eval nodeValue1808 x := by
  norm_num [reducedTerm723, nodeValue1808, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic724 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm724 x = (-3537875996458352640000 : ℝ) * Sparse.eval nodeValue1809 x := by
  norm_num [reducedTerm724, nodeValue1809, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic725 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm725 x = (-3345967769848381440000 : ℝ) * Sparse.eval nodeValue1810 x := by
  norm_num [reducedTerm725, nodeValue1810, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic726 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm726 x = (4908991524093296640000 : ℝ) * Sparse.eval nodeValue1811 x := by
  norm_num [reducedTerm726, nodeValue1811, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic727 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm727 x = (-11721265473473740800000 : ℝ) * Sparse.eval nodeValue1812 x := by
  norm_num [reducedTerm727, nodeValue1812, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic728 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm728 x = (6324490501957877760000 : ℝ) * Sparse.eval nodeValue1813 x := by
  norm_num [reducedTerm728, nodeValue1813, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic729 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm729 x = (2579448756790886400000 : ℝ) * Sparse.eval nodeValue1814 x := by
  norm_num [reducedTerm729, nodeValue1814, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic730 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm730 x = (-8001262491225292800000 : ℝ) * Sparse.eval nodeValue1815 x := by
  norm_num [reducedTerm730, nodeValue1815, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic731 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm731 x = (8788236653722337280000 : ℝ) * Sparse.eval nodeValue1816 x := by
  norm_num [reducedTerm731, nodeValue1816, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic732 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm732 x = (-1747607698444124160000 : ℝ) * Sparse.eval nodeValue1817 x := by
  norm_num [reducedTerm732, nodeValue1817, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic733 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm733 x = (-7591910646227927040000 : ℝ) * Sparse.eval nodeValue1818 x := by
  norm_num [reducedTerm733, nodeValue1818, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic734 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm734 x = (-10541826291919749120000 : ℝ) * Sparse.eval nodeValue1819 x := by
  norm_num [reducedTerm734, nodeValue1819, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic735 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm735 x = (-629645571257794560000 : ℝ) * Sparse.eval nodeValue1820 x := by
  norm_num [reducedTerm735, nodeValue1820, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic736 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm736 x = (1301309194638458880000 : ℝ) * Sparse.eval nodeValue1821 x := by
  norm_num [reducedTerm736, nodeValue1821, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic737 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm737 x = (1098658614922444800000 : ℝ) * Sparse.eval nodeValue1822 x := by
  norm_num [reducedTerm737, nodeValue1822, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic738 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm738 x = (-1301309194638458880000 : ℝ) * Sparse.eval nodeValue1823 x := by
  norm_num [reducedTerm738, nodeValue1823, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic739 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm739 x = (819808734353817600000 : ℝ) * Sparse.eval nodeValue1824 x := by
  norm_num [reducedTerm739, nodeValue1824, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic740 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm740 x = (3329639154745344000000 : ℝ) * Sparse.eval nodeValue1825 x := by
  norm_num [reducedTerm740, nodeValue1825, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic741 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm741 x = (2357878242882355200000 : ℝ) * Sparse.eval nodeValue1826 x := by
  norm_num [reducedTerm741, nodeValue1826, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic742 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm742 x = (-1098658614922444800000 : ℝ) * Sparse.eval nodeValue1827 x := by
  norm_num [reducedTerm742, nodeValue1827, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic743 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm743 x = (-750480790392668160000 : ℝ) * Sparse.eval nodeValue1828 x := by
  norm_num [reducedTerm743, nodeValue1828, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic744 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm744 x = (6755524079380070400000 : ℝ) * Sparse.eval nodeValue1829 x := by
  norm_num [reducedTerm744, nodeValue1829, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic745 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm745 x = (2387485449525657600000 : ℝ) * Sparse.eval nodeValue1830 x := by
  norm_num [reducedTerm745, nodeValue1830, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic746 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm746 x = (4222772882708889600000 : ℝ) * Sparse.eval nodeValue1831 x := by
  norm_num [reducedTerm746, nodeValue1831, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic747 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm747 x = (-971893105435607040000 : ℝ) * Sparse.eval nodeValue1832 x := by
  norm_num [reducedTerm747, nodeValue1832, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic748 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm748 x = (-478232461800898560000 : ℝ) * Sparse.eval nodeValue1957 x := by
  norm_num [reducedTerm748, nodeValue1957, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic749 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm749 x = (-23934621521018880000 : ℝ) * Sparse.eval nodeValue1964 x := by
  norm_num [reducedTerm749, nodeValue1964, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic750 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm750 x = (2241235474277990400000 : ℝ) * Sparse.eval nodeValue1965 x := by
  norm_num [reducedTerm750, nodeValue1965, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic751 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm751 x = (5347929085248798720000 : ℝ) * Sparse.eval nodeValue1966 x := by
  norm_num [reducedTerm751, nodeValue1966, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic752 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm752 x = (842806262366208000000 : ℝ) * Sparse.eval nodeValue1967 x := by
  norm_num [reducedTerm752, nodeValue1967, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic753 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm753 x = (2206413845208760320000 : ℝ) * Sparse.eval nodeValue1970 x := by
  norm_num [reducedTerm753, nodeValue1970, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic754 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm754 x = (3110224913045913600000 : ℝ) * Sparse.eval nodeValue1971 x := by
  norm_num [reducedTerm754, nodeValue1971, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic755 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm755 x = (6990515310978662400000 : ℝ) * Sparse.eval nodeValue1973 x := by
  norm_num [reducedTerm755, nodeValue1973, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic756 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm756 x = (2052530594103951360000 : ℝ) * Sparse.eval nodeValue1976 x := by
  norm_num [reducedTerm756, nodeValue1976, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic757 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm757 x = (-1235015743301222400000 : ℝ) * Sparse.eval nodeValue1977 x := by
  norm_num [reducedTerm757, nodeValue1977, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic758 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm758 x = (4959624732475392000000 : ℝ) * Sparse.eval nodeValue1978 x := by
  norm_num [reducedTerm758, nodeValue1978, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic759 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm759 x = (5755499567677440000000 : ℝ) * Sparse.eval nodeValue1979 x := by
  norm_num [reducedTerm759, nodeValue1979, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic760 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm760 x = (5338073982173184000000 : ℝ) * Sparse.eval nodeValue1980 x := by
  norm_num [reducedTerm760, nodeValue1980, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic761 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm761 x = (-3936013149156802560000 : ℝ) * Sparse.eval nodeValue2010 x := by
  norm_num [reducedTerm761, nodeValue2010, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic762 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm762 x = (-2983567758946467840000 : ℝ) * Sparse.eval nodeValue2019 x := by
  norm_num [reducedTerm762, nodeValue2019, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic763 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm763 x = (755963843883171840000 : ℝ) * Sparse.eval nodeValue2020 x := by
  norm_num [reducedTerm763, nodeValue2020, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic764 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm764 x = (2983567758946467840000 : ℝ) * Sparse.eval nodeValue2022 x := by
  norm_num [reducedTerm764, nodeValue2022, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic765 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm765 x = (88617370024673280000 : ℝ) * Sparse.eval nodeValue2023 x := by
  norm_num [reducedTerm765, nodeValue2023, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic766 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm766 x = (-4644957617419714560000 : ℝ) * Sparse.eval nodeValue2025 x := by
  norm_num [reducedTerm766, nodeValue2025, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic767 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm767 x = (3018336835652812800000 : ℝ) * Sparse.eval nodeValue2026 x := by
  norm_num [reducedTerm767, nodeValue2026, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic768 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm768 x = (590858676786954240000 : ℝ) * Sparse.eval nodeValue2028 x := by
  norm_num [reducedTerm768, nodeValue2028, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic769 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm769 x = (-2441576368615587840000 : ℝ) * Sparse.eval nodeValue2029 x := by
  norm_num [reducedTerm769, nodeValue2029, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic770 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm770 x = (4121680737526087680000 : ℝ) * Sparse.eval nodeValue2037 x := by
  norm_num [reducedTerm770, nodeValue2037, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic771 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm771 x = (6300739362226176000000 : ℝ) * Sparse.eval nodeValue2039 x := by
  norm_num [reducedTerm771, nodeValue2039, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic772 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm772 x = (-2470341383010385920000 : ℝ) * Sparse.eval nodeValue2051 x := by
  norm_num [reducedTerm772, nodeValue2051, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic773 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm773 x = (2470341383010385920000 : ℝ) * Sparse.eval nodeValue2054 x := by
  norm_num [reducedTerm773, nodeValue2054, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic774 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm774 x = (-2837840598442967040000 : ℝ) * Sparse.eval nodeValue2058 x := by
  norm_num [reducedTerm774, nodeValue2058, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic775 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm775 x = (-3893099630053294080000 : ℝ) * Sparse.eval nodeValue2062 x := by
  norm_num [reducedTerm775, nodeValue2062, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic776 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm776 x = (-2282493232765992960000 : ℝ) * Sparse.eval nodeValue2088 x := by
  norm_num [reducedTerm776, nodeValue2088, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic777 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm777 x = (-18920168420746199040000 : ℝ) * Sparse.eval nodeValue2089 x := by
  norm_num [reducedTerm777, nodeValue2089, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic778 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm778 x = (-27244411052347883520000 : ℝ) * Sparse.eval nodeValue2090 x := by
  norm_num [reducedTerm778, nodeValue2090, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic779 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm779 x = (14205848185641369600000 : ℝ) * Sparse.eval nodeValue2092 x := by
  norm_num [reducedTerm779, nodeValue2092, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic780 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm780 x = (15839955060530872320000 : ℝ) * Sparse.eval nodeValue2094 x := by
  norm_num [reducedTerm780, nodeValue2094, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic781 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm781 x = (-28541892592926720000 : ℝ) * Sparse.eval nodeValue2104 x := by
  norm_num [reducedTerm781, nodeValue2104, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic782 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm782 x = (-338218339097640960000 : ℝ) * Sparse.eval nodeValue2105 x := by
  norm_num [reducedTerm782, nodeValue2105, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic783 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm783 x = (283347893291581440000 : ℝ) * Sparse.eval nodeValue2106 x := by
  norm_num [reducedTerm783, nodeValue2106, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic784 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm784 x = (5704108413360537600000 : ℝ) * Sparse.eval nodeValue2107 x := by
  norm_num [reducedTerm784, nodeValue2107, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic785 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm785 x = (-18375094409940172800000 : ℝ) * Sparse.eval nodeValue2108 x := by
  norm_num [reducedTerm785, nodeValue2108, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic786 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm786 x = (5542318650230046720000 : ℝ) * Sparse.eval nodeValue2109 x := by
  norm_num [reducedTerm786, nodeValue2109, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic787 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm787 x = (-14180570318501314560000 : ℝ) * Sparse.eval nodeValue2110 x := by
  norm_num [reducedTerm787, nodeValue2110, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic788 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm788 x = (-3684095090420613120000 : ℝ) * Sparse.eval nodeValue2112 x := by
  norm_num [reducedTerm788, nodeValue2112, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic789 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm789 x = (-757176972741181440000 : ℝ) * Sparse.eval nodeValue2113 x := by
  norm_num [reducedTerm789, nodeValue2113, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic790 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm790 x = (-12013936625481154560000 : ℝ) * Sparse.eval nodeValue2115 x := by
  norm_num [reducedTerm790, nodeValue2115, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic791 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm791 x = (-1563346111522406400000 : ℝ) * Sparse.eval nodeValue2116 x := by
  norm_num [reducedTerm791, nodeValue2116, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic792 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm792 x = (1418945220960583680000 : ℝ) * Sparse.eval nodeValue2131 x := by
  norm_num [reducedTerm792, nodeValue2131, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic793 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm793 x = (-1418945220960583680000 : ℝ) * Sparse.eval nodeValue2132 x := by
  norm_num [reducedTerm793, nodeValue2132, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic794 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm794 x = (11767743613933977600000 : ℝ) * Sparse.eval nodeValue2133 x := by
  norm_num [reducedTerm794, nodeValue2133, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic795 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm795 x = (4056479869678387200000 : ℝ) * Sparse.eval nodeValue2134 x := by
  norm_num [reducedTerm795, nodeValue2134, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic796 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm796 x = (-40767630952366080000 : ℝ) * Sparse.eval nodeValue2136 x := by
  norm_num [reducedTerm796, nodeValue2136, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic797 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm797 x = (8053752549762662400000 : ℝ) * Sparse.eval nodeValue2138 x := by
  norm_num [reducedTerm797, nodeValue2138, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic798 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm798 x = (-1056230257065984000000 : ℝ) * Sparse.eval nodeValue2140 x := by
  norm_num [reducedTerm798, nodeValue2140, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic799 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm799 x = (-1423280520010137600000 : ℝ) * Sparse.eval nodeValue2142 x := by
  norm_num [reducedTerm799, nodeValue2142, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic800 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm800 x = (1234719933093642240000 : ℝ) * Sparse.eval nodeValue2144 x := by
  norm_num [reducedTerm800, nodeValue2144, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic801 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm801 x = (747433945254592512000 : ℝ) * Sparse.eval nodeValue2145 x := by
  norm_num [reducedTerm801, nodeValue2145, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic802 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm802 x = (-1041522169018318848000 : ℝ) * Sparse.eval nodeValue2146 x := by
  norm_num [reducedTerm802, nodeValue2146, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic803 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm803 x = (-1400262241941061632000 : ℝ) * Sparse.eval nodeValue2147 x := by
  norm_num [reducedTerm803, nodeValue2147, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic804 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm804 x = (-1951341470849433600000 : ℝ) * Sparse.eval nodeValue2148 x := by
  norm_num [reducedTerm804, nodeValue2148, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic805 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm805 x = (-3528479019960631296000 : ℝ) * Sparse.eval nodeValue2149 x := by
  norm_num [reducedTerm805, nodeValue2149, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic806 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm806 x = (-5084299705354813440000 : ℝ) * Sparse.eval nodeValue2153 x := by
  norm_num [reducedTerm806, nodeValue2153, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic807 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm807 x = (415726753622261760000 : ℝ) * Sparse.eval nodeValue2154 x := by
  norm_num [reducedTerm807, nodeValue2154, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic808 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm808 x = (-199802494476877824000 : ℝ) * Sparse.eval nodeValue2155 x := by
  norm_num [reducedTerm808, nodeValue2155, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic809 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm809 x = (-1958086160293036032000 : ℝ) * Sparse.eval nodeValue2158 x := by
  norm_num [reducedTerm809, nodeValue2158, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic810 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm810 x = (350247195718189056000 : ℝ) * Sparse.eval nodeValue2160 x := by
  norm_num [reducedTerm810, nodeValue2160, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic811 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm811 x = (460809475344433152000 : ℝ) * Sparse.eval nodeValue2161 x := by
  norm_num [reducedTerm811, nodeValue2161, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic812 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm812 x = (1082771078483017728000 : ℝ) * Sparse.eval nodeValue2162 x := by
  norm_num [reducedTerm812, nodeValue2162, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic813 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm813 x = (104801980817866752000 : ℝ) * Sparse.eval nodeValue2163 x := by
  norm_num [reducedTerm813, nodeValue2163, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic814 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm814 x = (-4082980870490554368000 : ℝ) * Sparse.eval nodeValue2164 x := by
  norm_num [reducedTerm814, nodeValue2164, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic815 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm815 x = (-888215115745198080000 : ℝ) * Sparse.eval nodeValue2171 x := by
  norm_num [reducedTerm815, nodeValue2171, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic816 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm816 x = (-1086333153488142336000 : ℝ) * Sparse.eval nodeValue2172 x := by
  norm_num [reducedTerm816, nodeValue2172, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic817 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm817 x = (-2488877088999211008000 : ℝ) * Sparse.eval nodeValue2175 x := by
  norm_num [reducedTerm817, nodeValue2175, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic818 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm818 x = (-1039334509865336832000 : ℝ) * Sparse.eval nodeValue2176 x := by
  norm_num [reducedTerm818, nodeValue2176, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic819 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm819 x = (-2644281324676841472000 : ℝ) * Sparse.eval nodeValue2178 x := by
  norm_num [reducedTerm819, nodeValue2178, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic820 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm820 x = (382802499623190528000 : ℝ) * Sparse.eval nodeValue2179 x := by
  norm_num [reducedTerm820, nodeValue2179, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic821 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm821 x = (80987525421465600000 : ℝ) * Sparse.eval nodeValue2180 x := by
  norm_num [reducedTerm821, nodeValue2180, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic822 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm822 x = (-2480383209507323904000 : ℝ) * Sparse.eval nodeValue2181 x := by
  norm_num [reducedTerm822, nodeValue2181, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic823 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm823 x = (1069052130648391680000 : ℝ) * Sparse.eval nodeValue2187 x := by
  norm_num [reducedTerm823, nodeValue2187, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic824 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm824 x = (-535625493262368768000 : ℝ) * Sparse.eval nodeValue2189 x := by
  norm_num [reducedTerm824, nodeValue2189, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic825 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm825 x = (2550756900341809152000 : ℝ) * Sparse.eval nodeValue2192 x := by
  norm_num [reducedTerm825, nodeValue2192, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic826 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm826 x = (506714469983059968000 : ℝ) * Sparse.eval nodeValue2194 x := by
  norm_num [reducedTerm826, nodeValue2194, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic827 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm827 x = (2281683348482162688000 : ℝ) * Sparse.eval nodeValue2195 x := by
  norm_num [reducedTerm827, nodeValue2195, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic828 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm828 x = (4171042250963288064000 : ℝ) * Sparse.eval nodeValue2196 x := by
  norm_num [reducedTerm828, nodeValue2196, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic829 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm829 x = (3716334068831354880000 : ℝ) * Sparse.eval nodeValue2197 x := by
  norm_num [reducedTerm829, nodeValue2197, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic830 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm830 x = (-1758049717505163264000 : ℝ) * Sparse.eval nodeValue2198 x := by
  norm_num [reducedTerm830, nodeValue2198, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic831 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm831 x = (-529608735311265792000 : ℝ) * Sparse.eval nodeValue2199 x := by
  norm_num [reducedTerm831, nodeValue2199, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic832 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm832 x = (-2923000637003661312000 : ℝ) * Sparse.eval nodeValue2200 x := by
  norm_num [reducedTerm832, nodeValue2200, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic833 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm833 x = (-968581412641898496000 : ℝ) * Sparse.eval nodeValue2201 x := by
  norm_num [reducedTerm833, nodeValue2201, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic834 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm834 x = (-1075562447389065216000 : ℝ) * Sparse.eval nodeValue2207 x := by
  norm_num [reducedTerm834, nodeValue2207, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic835 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm835 x = (3118020017674125312000 : ℝ) * Sparse.eval nodeValue2211 x := by
  norm_num [reducedTerm835, nodeValue2211, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic836 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm836 x = (3417517613264928768000 : ℝ) * Sparse.eval nodeValue2212 x := by
  norm_num [reducedTerm836, nodeValue2212, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic837 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm837 x = (-164392035143712768000 : ℝ) * Sparse.eval nodeValue2213 x := by
  norm_num [reducedTerm837, nodeValue2213, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic838 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm838 x = (6106405275203272704000 : ℝ) * Sparse.eval nodeValue2217 x := by
  norm_num [reducedTerm838, nodeValue2217, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic839 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm839 x = (543996082382635008000 : ℝ) * Sparse.eval nodeValue2219 x := by
  norm_num [reducedTerm839, nodeValue2219, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic840 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm840 x = (1698881328169353216000 : ℝ) * Sparse.eval nodeValue2220 x := by
  norm_num [reducedTerm840, nodeValue2220, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic841 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm841 x = (-2422443967567626240000 : ℝ) * Sparse.eval nodeValue2221 x := by
  norm_num [reducedTerm841, nodeValue2221, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic842 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm842 x = (-2652931479726194688000 : ℝ) * Sparse.eval nodeValue2222 x := by
  norm_num [reducedTerm842, nodeValue2222, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic843 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm843 x = (454996272018161664000 : ℝ) * Sparse.eval nodeValue2223 x := by
  norm_num [reducedTerm843, nodeValue2223, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic844 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm844 x = (522094469787942912000 : ℝ) * Sparse.eval nodeValue2231 x := by
  norm_num [reducedTerm844, nodeValue2231, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic845 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm845 x = (825412766634344448000 : ℝ) * Sparse.eval nodeValue2232 x := by
  norm_num [reducedTerm845, nodeValue2232, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic846 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm846 x = (-7143996310767009792000 : ℝ) * Sparse.eval nodeValue2233 x := by
  norm_num [reducedTerm846, nodeValue2233, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic847 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm847 x = (5281412168984297472000 : ℝ) * Sparse.eval nodeValue2234 x := by
  norm_num [reducedTerm847, nodeValue2234, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic848 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm848 x = (8991466736109355008000 : ℝ) * Sparse.eval nodeValue2235 x := by
  norm_num [reducedTerm848, nodeValue2235, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic849 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm849 x = (1167171979199643648000 : ℝ) * Sparse.eval nodeValue2238 x := by
  norm_num [reducedTerm849, nodeValue2238, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic850 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm850 x = (-11939427307487232000 : ℝ) * Sparse.eval nodeValue2239 x := by
  norm_num [reducedTerm850, nodeValue2239, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic851 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm851 x = (-912884097845035008000 : ℝ) * Sparse.eval nodeValue2240 x := by
  norm_num [reducedTerm851, nodeValue2240, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic852 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm852 x = (-3530220507746795520000 : ℝ) * Sparse.eval nodeValue2243 x := by
  norm_num [reducedTerm852, nodeValue2243, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic853 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm853 x = (-13288538835716014080000 : ℝ) * Sparse.eval nodeValue2244 x := by
  norm_num [reducedTerm853, nodeValue2244, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic854 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm854 x = (5084282729677455360000 : ℝ) * Sparse.eval nodeValue2245 x := by
  norm_num [reducedTerm854, nodeValue2245, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic855 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm855 x = (14561556817950277632000 : ℝ) * Sparse.eval nodeValue2246 x := by
  norm_num [reducedTerm855, nodeValue2246, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic856 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm856 x = (-12514908548880138240000 : ℝ) * Sparse.eval nodeValue2247 x := by
  norm_num [reducedTerm856, nodeValue2247, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic857 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm857 x = (-2840232254671945728000 : ℝ) * Sparse.eval nodeValue2248 x := by
  norm_num [reducedTerm857, nodeValue2248, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic858 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm858 x = (-2254308298937597952000 : ℝ) * Sparse.eval nodeValue2249 x := by
  norm_num [reducedTerm858, nodeValue2249, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic859 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm859 x = (6385220328544468992000 : ℝ) * Sparse.eval nodeValue2250 x := by
  norm_num [reducedTerm859, nodeValue2250, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic860 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm860 x = (6295106507412602880000 : ℝ) * Sparse.eval nodeValue2251 x := by
  norm_num [reducedTerm860, nodeValue2251, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic861 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm861 x = (-1717100482923528192000 : ℝ) * Sparse.eval nodeValue2252 x := by
  norm_num [reducedTerm861, nodeValue2252, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic862 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm862 x = (-11806284324964663296000 : ℝ) * Sparse.eval nodeValue2253 x := by
  norm_num [reducedTerm862, nodeValue2253, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic863 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm863 x = (3977835312798498816000 : ℝ) * Sparse.eval nodeValue2254 x := by
  norm_num [reducedTerm863, nodeValue2254, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic864 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm864 x = (13423761248418791424000 : ℝ) * Sparse.eval nodeValue2255 x := by
  norm_num [reducedTerm864, nodeValue2255, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic865 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm865 x = (-3060986888631877632000 : ℝ) * Sparse.eval nodeValue2256 x := by
  norm_num [reducedTerm865, nodeValue2256, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic866 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm866 x = (356540332144066560000 : ℝ) * Sparse.eval nodeValue2257 x := by
  norm_num [reducedTerm866, nodeValue2257, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic867 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm867 x = (-285682392053710848000 : ℝ) * Sparse.eval nodeValue2258 x := by
  norm_num [reducedTerm867, nodeValue2258, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic868 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm868 x = (-2232992392359837696000 : ℝ) * Sparse.eval nodeValue2259 x := by
  norm_num [reducedTerm868, nodeValue2259, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic869 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm869 x = (4747445379992125440000 : ℝ) * Sparse.eval nodeValue2262 x := by
  norm_num [reducedTerm869, nodeValue2262, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic870 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm870 x = (-4937762046553620480000 : ℝ) * Sparse.eval nodeValue2263 x := by
  norm_num [reducedTerm870, nodeValue2263, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic871 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm871 x = (-6331906344670986240000 : ℝ) * Sparse.eval nodeValue2264 x := by
  norm_num [reducedTerm871, nodeValue2264, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic872 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm872 x = (25915389786791608320000 : ℝ) * Sparse.eval nodeValue2265 x := by
  norm_num [reducedTerm872, nodeValue2265, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic873 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm873 x = (-17198383075263774720000 : ℝ) * Sparse.eval nodeValue2266 x := by
  norm_num [reducedTerm873, nodeValue2266, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic874 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm874 x = (2456191162674708480000 : ℝ) * Sparse.eval nodeValue2267 x := by
  norm_num [reducedTerm874, nodeValue2267, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic875 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm875 x = (-6892394631702773760000 : ℝ) * Sparse.eval nodeValue2268 x := by
  norm_num [reducedTerm875, nodeValue2268, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic876 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm876 x = (620385158666649600000 : ℝ) * Sparse.eval nodeValue2272 x := by
  norm_num [reducedTerm876, nodeValue2272, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic877 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm877 x = (1530801552859987968000 : ℝ) * Sparse.eval nodeValue2273 x := by
  norm_num [reducedTerm877, nodeValue2273, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic878 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm878 x = (11930424302148452352000 : ℝ) * Sparse.eval nodeValue2274 x := by
  norm_num [reducedTerm878, nodeValue2274, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic879 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm879 x = (7044709980352020480000 : ℝ) * Sparse.eval nodeValue2277 x := by
  norm_num [reducedTerm879, nodeValue2277, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic880 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm880 x = (613475877389598720000 : ℝ) * Sparse.eval nodeValue2278 x := by
  norm_num [reducedTerm880, nodeValue2278, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic881 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm881 x = (4948572573257564160000 : ℝ) * Sparse.eval nodeValue2279 x := by
  norm_num [reducedTerm881, nodeValue2279, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic882 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm882 x = (4794515628466765824000 : ℝ) * Sparse.eval nodeValue2280 x := by
  norm_num [reducedTerm882, nodeValue2280, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic883 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm883 x = (9591223123887390720000 : ℝ) * Sparse.eval nodeValue2281 x := by
  norm_num [reducedTerm883, nodeValue2281, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic884 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm884 x = (-328449504969621504000 : ℝ) * Sparse.eval nodeValue2282 x := by
  norm_num [reducedTerm884, nodeValue2282, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic885 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm885 x = (1069657792115834880000 : ℝ) * Sparse.eval nodeValue2283 x := by
  norm_num [reducedTerm885, nodeValue2283, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic886 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm886 x = (3942379037195698176000 : ℝ) * Sparse.eval nodeValue2284 x := by
  norm_num [reducedTerm886, nodeValue2284, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic887 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm887 x = (88491352709136384000 : ℝ) * Sparse.eval nodeValue2285 x := by
  norm_num [reducedTerm887, nodeValue2285, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic888 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm888 x = (1402778741635547136000 : ℝ) * Sparse.eval nodeValue2286 x := by
  norm_num [reducedTerm888, nodeValue2286, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic889 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm889 x = (-7179555731668992000000 : ℝ) * Sparse.eval nodeValue2291 x := by
  norm_num [reducedTerm889, nodeValue2291, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic890 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm890 x = (-1904143670024601600000 : ℝ) * Sparse.eval nodeValue2293 x := by
  norm_num [reducedTerm890, nodeValue2293, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic891 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm891 x = (-9942532690001264640000 : ℝ) * Sparse.eval nodeValue2294 x := by
  norm_num [reducedTerm891, nodeValue2294, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic892 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm892 x = (-5775400208422010880000 : ℝ) * Sparse.eval nodeValue2323 x := by
  norm_num [reducedTerm892, nodeValue2323, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic893 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm893 x = (1409374911961497600000 : ℝ) * Sparse.eval nodeValue2327 x := by
  norm_num [reducedTerm893, nodeValue2327, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic894 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm894 x = (-1021462625098137600000 : ℝ) * Sparse.eval nodeValue2330 x := by
  norm_num [reducedTerm894, nodeValue2330, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic895 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm895 x = (8792971061782118400000 : ℝ) * Sparse.eval nodeValue2332 x := by
  norm_num [reducedTerm895, nodeValue2332, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic896 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm896 x = (1021462625098137600000 : ℝ) * Sparse.eval nodeValue2334 x := by
  norm_num [reducedTerm896, nodeValue2334, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic897 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm897 x = (2042925250196275200000 : ℝ) * Sparse.eval nodeValue2337 x := by
  norm_num [reducedTerm897, nodeValue2337, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic898 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm898 x = (6349509219129753600000 : ℝ) * Sparse.eval nodeValue2338 x := by
  norm_num [reducedTerm898, nodeValue2338, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic899 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm899 x = (-1957928575441305600000 : ℝ) * Sparse.eval nodeValue2339 x := by
  norm_num [reducedTerm899, nodeValue2339, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic900 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm900 x = (-5831241247610634240000 : ℝ) * Sparse.eval nodeValue2340 x := by
  norm_num [reducedTerm900, nodeValue2340, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic901 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm901 x = (-4592195406267678720000 : ℝ) * Sparse.eval nodeValue2341 x := by
  norm_num [reducedTerm901, nodeValue2341, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic902 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm902 x = (-8792971061782118400000 : ℝ) * Sparse.eval nodeValue2342 x := by
  norm_num [reducedTerm902, nodeValue2342, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic903 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm903 x = (-1021462625098137600000 : ℝ) * Sparse.eval nodeValue2344 x := by
  norm_num [reducedTerm903, nodeValue2344, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic904 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm904 x = (-15267702809682247680000 : ℝ) * Sparse.eval nodeValue2345 x := by
  norm_num [reducedTerm904, nodeValue2345, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic905 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm905 x = (3811111984406200320000 : ℝ) * Sparse.eval nodeValue2346 x := by
  norm_num [reducedTerm905, nodeValue2346, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic906 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm906 x = (54778388874854400000 : ℝ) * Sparse.eval nodeValue2347 x := by
  norm_num [reducedTerm906, nodeValue2347, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic907 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm907 x = (-54778388874854400000 : ℝ) * Sparse.eval nodeValue2348 x := by
  norm_num [reducedTerm907, nodeValue2348, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic908 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm908 x = (-598839592845312000000 : ℝ) * Sparse.eval nodeValue2349 x := by
  norm_num [reducedTerm908, nodeValue2349, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic909 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm909 x = (-2122040394523607040000 : ℝ) * Sparse.eval nodeValue2350 x := by
  norm_num [reducedTerm909, nodeValue2350, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic910 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm910 x = (14499441893476270080000 : ℝ) * Sparse.eval nodeValue2352 x := by
  norm_num [reducedTerm910, nodeValue2352, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic911 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm911 x = (-4008567374777548800000 : ℝ) * Sparse.eval nodeValue2353 x := by
  norm_num [reducedTerm911, nodeValue2353, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic912 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm912 x = (-3201531558440140800000 : ℝ) * Sparse.eval nodeValue2355 x := by
  norm_num [reducedTerm912, nodeValue2355, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic913 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm913 x = (7210098933217689600000 : ℝ) * Sparse.eval nodeValue2356 x := by
  norm_num [reducedTerm913, nodeValue2356, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic914 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm914 x = (-4433171053215744000000 : ℝ) * Sparse.eval nodeValue2361 x := by
  norm_num [reducedTerm914, nodeValue2361, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic915 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm915 x = (-9916201969680384000000 : ℝ) * Sparse.eval nodeValue2362 x := by
  norm_num [reducedTerm915, nodeValue2362, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic916 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm916 x = (5684917680995696640000 : ℝ) * Sparse.eval nodeValue2423 x := by
  norm_num [reducedTerm916, nodeValue2423, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic917 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm917 x = (-3022934715924480000000 : ℝ) * Sparse.eval nodeValue2425 x := by
  norm_num [reducedTerm917, nodeValue2425, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic918 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm918 x = (-2089015568665804800000 : ℝ) * Sparse.eval nodeValue2426 x := by
  norm_num [reducedTerm918, nodeValue2426, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic919 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm919 x = (5559732986314752000000 : ℝ) * Sparse.eval nodeValue2428 x := by
  norm_num [reducedTerm919, nodeValue2428, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic920 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm920 x = (-3513264514950758400000 : ℝ) * Sparse.eval nodeValue2429 x := by
  norm_num [reducedTerm920, nodeValue2429, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic921 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm921 x = (19962365120110264320000 : ℝ) * Sparse.eval nodeValue2430 x := by
  norm_num [reducedTerm921, nodeValue2430, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic922 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm922 x = (14124724583912570880000 : ℝ) * Sparse.eval nodeValue2431 x := by
  norm_num [reducedTerm922, nodeValue2431, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic923 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm923 x = (762973624782028800000 : ℝ) * Sparse.eval nodeValue2432 x := by
  norm_num [reducedTerm923, nodeValue2432, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic924 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm924 x = (2089015568665804800000 : ℝ) * Sparse.eval nodeValue2433 x := by
  norm_num [reducedTerm924, nodeValue2433, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic925 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm925 x = (-4285922492777103360000 : ℝ) * Sparse.eval nodeValue2434 x := by
  norm_num [reducedTerm925, nodeValue2434, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic926 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm926 x = (5339288646065848320000 : ℝ) * Sparse.eval nodeValue2435 x := by
  norm_num [reducedTerm926, nodeValue2435, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic927 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm927 x = (-29125569354242457600000 : ℝ) * Sparse.eval nodeValue2437 x := by
  norm_num [reducedTerm927, nodeValue2437, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic928 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm928 x = (-4666690457468928000000 : ℝ) * Sparse.eval nodeValue2438 x := by
  norm_num [reducedTerm928, nodeValue2438, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic929 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm929 x = (-1089057424637952000000 : ℝ) * Sparse.eval nodeValue2440 x := by
  norm_num [reducedTerm929, nodeValue2440, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic930 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm930 x = (-27156418471526400000 : ℝ) * Sparse.eval nodeValue2441 x := by
  norm_num [reducedTerm930, nodeValue2441, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic931 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm931 x = (4167404634193920000000 : ℝ) * Sparse.eval nodeValue2442 x := by
  norm_num [reducedTerm931, nodeValue2442, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic932 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm932 x = (-6201565287992524800000 : ℝ) * Sparse.eval nodeValue2443 x := by
  norm_num [reducedTerm932, nodeValue2443, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic933 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm933 x = (-669848715789926400000 : ℝ) * Sparse.eval nodeValue2470 x := by
  norm_num [reducedTerm933, nodeValue2470, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic934 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm934 x = (5402275542460661760000 : ℝ) * Sparse.eval nodeValue2471 x := by
  norm_num [reducedTerm934, nodeValue2471, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic935 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm935 x = (669848715789926400000 : ℝ) * Sparse.eval nodeValue2473 x := by
  norm_num [reducedTerm935, nodeValue2473, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic936 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm936 x = (-21951447043276800000 : ℝ) * Sparse.eval nodeValue2479 x := by
  norm_num [reducedTerm936, nodeValue2479, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic937 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm937 x = (-12811011857783193600000 : ℝ) * Sparse.eval nodeValue2480 x := by
  norm_num [reducedTerm937, nodeValue2480, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic938 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm938 x = (3044886162967756800000 : ℝ) * Sparse.eval nodeValue2482 x := by
  norm_num [reducedTerm938, nodeValue2482, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic939 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm939 x = (10730200326977617920000 : ℝ) * Sparse.eval nodeValue2483 x := by
  norm_num [reducedTerm939, nodeValue2483, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic940 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm940 x = (-7075268186112000000000 : ℝ) * Sparse.eval nodeValue2485 x := by
  norm_num [reducedTerm940, nodeValue2485, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic941 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm941 x = (-10132091952404889600000 : ℝ) * Sparse.eval nodeValue2486 x := by
  norm_num [reducedTerm941, nodeValue2486, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic942 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm942 x = (3036144140609126400000 : ℝ) * Sparse.eval nodeValue2488 x := by
  norm_num [reducedTerm942, nodeValue2488, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic943 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm943 x = (12048038233001164800000 : ℝ) * Sparse.eval nodeValue2489 x := by
  norm_num [reducedTerm943, nodeValue2489, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic944 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm944 x = (882109921738752000000 : ℝ) * Sparse.eval nodeValue2494 x := by
  norm_num [reducedTerm944, nodeValue2494, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic945 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm945 x = (421979070165811200000 : ℝ) * Sparse.eval nodeValue2495 x := by
  norm_num [reducedTerm945, nodeValue2495, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic946 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm946 x = (2247947368157675520000 : ℝ) * Sparse.eval nodeValue2497 x := by
  norm_num [reducedTerm946, nodeValue2497, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic947 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm947 x = (-7786684812636979200000 : ℝ) * Sparse.eval nodeValue2499 x := by
  norm_num [reducedTerm947, nodeValue2499, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic948 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm948 x = (4693700295180288000000 : ℝ) * Sparse.eval nodeValue2508 x := by
  norm_num [reducedTerm948, nodeValue2508, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic949 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm949 x = (-8251961190668697600000 : ℝ) * Sparse.eval nodeValue2512 x := by
  norm_num [reducedTerm949, nodeValue2512, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic950 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm950 x = (-4629005356695552000000 : ℝ) * Sparse.eval nodeValue2513 x := by
  norm_num [reducedTerm950, nodeValue2513, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic951 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm951 x = (20072224660871577600000 : ℝ) * Sparse.eval nodeValue2515 x := by
  norm_num [reducedTerm951, nodeValue2515, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic952 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm952 x = (4382870405576785920000 : ℝ) * Sparse.eval nodeValue2519 x := by
  norm_num [reducedTerm952, nodeValue2519, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic953 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm953 x = (3829273250294661120000 : ℝ) * Sparse.eval nodeValue2520 x := by
  norm_num [reducedTerm953, nodeValue2520, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic954 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm954 x = (-46570423131832320000 : ℝ) * Sparse.eval nodeValue2522 x := by
  norm_num [reducedTerm954, nodeValue2522, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic955 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm955 x = (94866766992506880000 : ℝ) * Sparse.eval nodeValue2524 x := by
  norm_num [reducedTerm955, nodeValue2524, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic956 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm956 x = (-1138001372530606080000 : ℝ) * Sparse.eval nodeValue2529 x := by
  norm_num [reducedTerm956, nodeValue2529, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic957 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm957 x = (-1139201814778675200000 : ℝ) * Sparse.eval nodeValue2545 x := by
  norm_num [reducedTerm957, nodeValue2545, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic958 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm958 x = (-5874441005529169920000 : ℝ) * Sparse.eval nodeValue2553 x := by
  norm_num [reducedTerm958, nodeValue2553, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge717Check : reducedMerge717 = Integer.Sparse.mergeBy masterLess reducedTerm720 reducedTerm721 := by decide +kernel

theorem reducedMerge718Check : reducedMerge718 = Integer.Sparse.mergeBy masterLess reducedTerm719 reducedMerge717 := by decide +kernel

theorem reducedMerge719Check : reducedMerge719 = Integer.Sparse.mergeBy masterLess reducedTerm722 reducedTerm723 := by decide +kernel

theorem reducedMerge720Check : reducedMerge720 = Integer.Sparse.mergeBy masterLess reducedTerm724 reducedTerm725 := by decide +kernel

theorem reducedMerge721Check : reducedMerge721 = Integer.Sparse.mergeBy masterLess reducedMerge719 reducedMerge720 := by decide +kernel

theorem reducedMerge722Check : reducedMerge722 = Integer.Sparse.mergeBy masterLess reducedMerge718 reducedMerge721 := by decide +kernel

theorem reducedMerge723Check : reducedMerge723 = Integer.Sparse.mergeBy masterLess reducedTerm726 reducedTerm727 := by decide +kernel

theorem reducedMerge724Check : reducedMerge724 = Integer.Sparse.mergeBy masterLess reducedTerm728 reducedTerm729 := by decide +kernel

theorem reducedMerge725Check : reducedMerge725 = Integer.Sparse.mergeBy masterLess reducedMerge723 reducedMerge724 := by decide +kernel

theorem reducedMerge726Check : reducedMerge726 = Integer.Sparse.mergeBy masterLess reducedTerm730 reducedTerm731 := by decide +kernel

theorem reducedMerge727Check : reducedMerge727 = Integer.Sparse.mergeBy masterLess reducedTerm732 reducedTerm733 := by decide +kernel

theorem reducedMerge728Check : reducedMerge728 = Integer.Sparse.mergeBy masterLess reducedMerge726 reducedMerge727 := by decide +kernel

theorem reducedMerge729Check : reducedMerge729 = Integer.Sparse.mergeBy masterLess reducedMerge725 reducedMerge728 := by decide +kernel

theorem reducedMerge730Check : reducedMerge730 = Integer.Sparse.mergeBy masterLess reducedMerge722 reducedMerge729 := by decide +kernel

theorem reducedMerge731Check : reducedMerge731 = Integer.Sparse.mergeBy masterLess reducedTerm735 reducedTerm736 := by decide +kernel

theorem reducedMerge732Check : reducedMerge732 = Integer.Sparse.mergeBy masterLess reducedTerm734 reducedMerge731 := by decide +kernel

theorem reducedMerge733Check : reducedMerge733 = Integer.Sparse.mergeBy masterLess reducedTerm737 reducedTerm738 := by decide +kernel

theorem reducedMerge734Check : reducedMerge734 = Integer.Sparse.mergeBy masterLess reducedTerm739 reducedTerm740 := by decide +kernel

theorem reducedMerge735Check : reducedMerge735 = Integer.Sparse.mergeBy masterLess reducedMerge733 reducedMerge734 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge736Check : reducedMerge736 = Integer.Sparse.mergeBy masterLess reducedMerge732 reducedMerge735 := by decide +kernel

theorem reducedMerge737Check : reducedMerge737 = Integer.Sparse.mergeBy masterLess reducedTerm741 reducedTerm742 := by decide +kernel

theorem reducedMerge738Check : reducedMerge738 = Integer.Sparse.mergeBy masterLess reducedTerm743 reducedTerm744 := by decide +kernel

theorem reducedMerge739Check : reducedMerge739 = Integer.Sparse.mergeBy masterLess reducedMerge737 reducedMerge738 := by decide +kernel

theorem reducedMerge740Check : reducedMerge740 = Integer.Sparse.mergeBy masterLess reducedTerm745 reducedTerm746 := by decide +kernel

theorem reducedMerge741Check : reducedMerge741 = Integer.Sparse.mergeBy masterLess reducedTerm747 reducedTerm748 := by decide +kernel

theorem reducedMerge742Check : reducedMerge742 = Integer.Sparse.mergeBy masterLess reducedMerge740 reducedMerge741 := by decide +kernel

theorem reducedMerge743Check : reducedMerge743 = Integer.Sparse.mergeBy masterLess reducedMerge739 reducedMerge742 := by decide +kernel

theorem reducedMerge744Check : reducedMerge744 = Integer.Sparse.mergeBy masterLess reducedMerge736 reducedMerge743 := by decide +kernel

theorem reducedMerge745Check : reducedMerge745 = Integer.Sparse.mergeBy masterLess reducedMerge730 reducedMerge744 := by decide +kernel

theorem reducedMerge746Check : reducedMerge746 = Integer.Sparse.mergeBy masterLess reducedTerm750 reducedTerm751 := by decide +kernel

theorem reducedMerge747Check : reducedMerge747 = Integer.Sparse.mergeBy masterLess reducedTerm749 reducedMerge746 := by decide +kernel

theorem reducedMerge748Check : reducedMerge748 = Integer.Sparse.mergeBy masterLess reducedTerm752 reducedTerm753 := by decide +kernel

theorem reducedMerge749Check : reducedMerge749 = Integer.Sparse.mergeBy masterLess reducedTerm754 reducedTerm755 := by decide +kernel

theorem reducedMerge750Check : reducedMerge750 = Integer.Sparse.mergeBy masterLess reducedMerge748 reducedMerge749 := by decide +kernel

theorem reducedMerge751Check : reducedMerge751 = Integer.Sparse.mergeBy masterLess reducedMerge747 reducedMerge750 := by decide +kernel

theorem reducedMerge752Check : reducedMerge752 = Integer.Sparse.mergeBy masterLess reducedTerm756 reducedTerm757 := by decide +kernel

theorem reducedMerge753Check : reducedMerge753 = Integer.Sparse.mergeBy masterLess reducedTerm758 reducedTerm759 := by decide +kernel

theorem reducedMerge754Check : reducedMerge754 = Integer.Sparse.mergeBy masterLess reducedMerge752 reducedMerge753 := by decide +kernel

theorem reducedMerge755Check : reducedMerge755 = Integer.Sparse.mergeBy masterLess reducedTerm760 reducedTerm761 := by decide +kernel

theorem reducedMerge756Check : reducedMerge756 = Integer.Sparse.mergeBy masterLess reducedTerm762 reducedTerm763 := by decide +kernel

theorem reducedMerge757Check : reducedMerge757 = Integer.Sparse.mergeBy masterLess reducedMerge755 reducedMerge756 := by decide +kernel

theorem reducedMerge758Check : reducedMerge758 = Integer.Sparse.mergeBy masterLess reducedMerge754 reducedMerge757 := by decide +kernel

theorem reducedMerge759Check : reducedMerge759 = Integer.Sparse.mergeBy masterLess reducedMerge751 reducedMerge758 := by decide +kernel

theorem reducedMerge760Check : reducedMerge760 = Integer.Sparse.mergeBy masterLess reducedTerm765 reducedTerm766 := by decide +kernel

theorem reducedMerge761Check : reducedMerge761 = Integer.Sparse.mergeBy masterLess reducedTerm764 reducedMerge760 := by decide +kernel

theorem reducedMerge762Check : reducedMerge762 = Integer.Sparse.mergeBy masterLess reducedTerm767 reducedTerm768 := by decide +kernel

theorem reducedMerge763Check : reducedMerge763 = Integer.Sparse.mergeBy masterLess reducedTerm769 reducedTerm770 := by decide +kernel

theorem reducedMerge764Check : reducedMerge764 = Integer.Sparse.mergeBy masterLess reducedMerge762 reducedMerge763 := by decide +kernel

theorem reducedMerge765Check : reducedMerge765 = Integer.Sparse.mergeBy masterLess reducedMerge761 reducedMerge764 := by decide +kernel

theorem reducedMerge766Check : reducedMerge766 = Integer.Sparse.mergeBy masterLess reducedTerm771 reducedTerm772 := by decide +kernel

theorem reducedMerge767Check : reducedMerge767 = Integer.Sparse.mergeBy masterLess reducedTerm773 reducedTerm774 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge768Check : reducedMerge768 = Integer.Sparse.mergeBy masterLess reducedMerge766 reducedMerge767 := by decide +kernel

theorem reducedMerge769Check : reducedMerge769 = Integer.Sparse.mergeBy masterLess reducedTerm775 reducedTerm776 := by decide +kernel

theorem reducedMerge770Check : reducedMerge770 = Integer.Sparse.mergeBy masterLess reducedTerm777 reducedTerm778 := by decide +kernel

theorem reducedMerge771Check : reducedMerge771 = Integer.Sparse.mergeBy masterLess reducedMerge769 reducedMerge770 := by decide +kernel

theorem reducedMerge772Check : reducedMerge772 = Integer.Sparse.mergeBy masterLess reducedMerge768 reducedMerge771 := by decide +kernel

theorem reducedMerge773Check : reducedMerge773 = Integer.Sparse.mergeBy masterLess reducedMerge765 reducedMerge772 := by decide +kernel

theorem reducedMerge774Check : reducedMerge774 = Integer.Sparse.mergeBy masterLess reducedMerge759 reducedMerge773 := by decide +kernel

theorem reducedMerge775Check : reducedMerge775 = Integer.Sparse.mergeBy masterLess reducedMerge745 reducedMerge774 := by decide +kernel

theorem reducedMerge776Check : reducedMerge776 = Integer.Sparse.mergeBy masterLess reducedTerm780 reducedTerm781 := by decide +kernel

theorem reducedMerge777Check : reducedMerge777 = Integer.Sparse.mergeBy masterLess reducedTerm779 reducedMerge776 := by decide +kernel

theorem reducedMerge778Check : reducedMerge778 = Integer.Sparse.mergeBy masterLess reducedTerm782 reducedTerm783 := by decide +kernel

theorem reducedMerge779Check : reducedMerge779 = Integer.Sparse.mergeBy masterLess reducedTerm784 reducedTerm785 := by decide +kernel

theorem reducedMerge780Check : reducedMerge780 = Integer.Sparse.mergeBy masterLess reducedMerge778 reducedMerge779 := by decide +kernel

theorem reducedMerge781Check : reducedMerge781 = Integer.Sparse.mergeBy masterLess reducedMerge777 reducedMerge780 := by decide +kernel

theorem reducedMerge782Check : reducedMerge782 = Integer.Sparse.mergeBy masterLess reducedTerm786 reducedTerm787 := by decide +kernel

theorem reducedMerge783Check : reducedMerge783 = Integer.Sparse.mergeBy masterLess reducedTerm788 reducedTerm789 := by decide +kernel

theorem reducedMerge784Check : reducedMerge784 = Integer.Sparse.mergeBy masterLess reducedMerge782 reducedMerge783 := by decide +kernel

theorem reducedMerge785Check : reducedMerge785 = Integer.Sparse.mergeBy masterLess reducedTerm790 reducedTerm791 := by decide +kernel

theorem reducedMerge786Check : reducedMerge786 = Integer.Sparse.mergeBy masterLess reducedTerm792 reducedTerm793 := by decide +kernel

theorem reducedMerge787Check : reducedMerge787 = Integer.Sparse.mergeBy masterLess reducedMerge785 reducedMerge786 := by decide +kernel

theorem reducedMerge788Check : reducedMerge788 = Integer.Sparse.mergeBy masterLess reducedMerge784 reducedMerge787 := by decide +kernel

theorem reducedMerge789Check : reducedMerge789 = Integer.Sparse.mergeBy masterLess reducedMerge781 reducedMerge788 := by decide +kernel

theorem reducedMerge790Check : reducedMerge790 = Integer.Sparse.mergeBy masterLess reducedTerm795 reducedTerm796 := by decide +kernel

theorem reducedMerge791Check : reducedMerge791 = Integer.Sparse.mergeBy masterLess reducedTerm794 reducedMerge790 := by decide +kernel

theorem reducedMerge792Check : reducedMerge792 = Integer.Sparse.mergeBy masterLess reducedTerm797 reducedTerm798 := by decide +kernel

theorem reducedMerge793Check : reducedMerge793 = Integer.Sparse.mergeBy masterLess reducedTerm799 reducedTerm800 := by decide +kernel

theorem reducedMerge794Check : reducedMerge794 = Integer.Sparse.mergeBy masterLess reducedMerge792 reducedMerge793 := by decide +kernel

theorem reducedMerge795Check : reducedMerge795 = Integer.Sparse.mergeBy masterLess reducedMerge791 reducedMerge794 := by decide +kernel

theorem reducedMerge796Check : reducedMerge796 = Integer.Sparse.mergeBy masterLess reducedTerm801 reducedTerm802 := by decide +kernel

theorem reducedMerge797Check : reducedMerge797 = Integer.Sparse.mergeBy masterLess reducedTerm803 reducedTerm804 := by decide +kernel

theorem reducedMerge798Check : reducedMerge798 = Integer.Sparse.mergeBy masterLess reducedMerge796 reducedMerge797 := by decide +kernel

theorem reducedMerge799Check : reducedMerge799 = Integer.Sparse.mergeBy masterLess reducedTerm805 reducedTerm806 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge800Check : reducedMerge800 = Integer.Sparse.mergeBy masterLess reducedTerm807 reducedTerm808 := by decide +kernel

theorem reducedMerge801Check : reducedMerge801 = Integer.Sparse.mergeBy masterLess reducedMerge799 reducedMerge800 := by decide +kernel

theorem reducedMerge802Check : reducedMerge802 = Integer.Sparse.mergeBy masterLess reducedMerge798 reducedMerge801 := by decide +kernel

theorem reducedMerge803Check : reducedMerge803 = Integer.Sparse.mergeBy masterLess reducedMerge795 reducedMerge802 := by decide +kernel

theorem reducedMerge804Check : reducedMerge804 = Integer.Sparse.mergeBy masterLess reducedMerge789 reducedMerge803 := by decide +kernel

theorem reducedMerge805Check : reducedMerge805 = Integer.Sparse.mergeBy masterLess reducedTerm810 reducedTerm811 := by decide +kernel

theorem reducedMerge806Check : reducedMerge806 = Integer.Sparse.mergeBy masterLess reducedTerm809 reducedMerge805 := by decide +kernel

theorem reducedMerge807Check : reducedMerge807 = Integer.Sparse.mergeBy masterLess reducedTerm812 reducedTerm813 := by decide +kernel

theorem reducedMerge808Check : reducedMerge808 = Integer.Sparse.mergeBy masterLess reducedTerm814 reducedTerm815 := by decide +kernel

theorem reducedMerge809Check : reducedMerge809 = Integer.Sparse.mergeBy masterLess reducedMerge807 reducedMerge808 := by decide +kernel

theorem reducedMerge810Check : reducedMerge810 = Integer.Sparse.mergeBy masterLess reducedMerge806 reducedMerge809 := by decide +kernel

theorem reducedMerge811Check : reducedMerge811 = Integer.Sparse.mergeBy masterLess reducedTerm816 reducedTerm817 := by decide +kernel

theorem reducedMerge812Check : reducedMerge812 = Integer.Sparse.mergeBy masterLess reducedTerm818 reducedTerm819 := by decide +kernel

theorem reducedMerge813Check : reducedMerge813 = Integer.Sparse.mergeBy masterLess reducedMerge811 reducedMerge812 := by decide +kernel

theorem reducedMerge814Check : reducedMerge814 = Integer.Sparse.mergeBy masterLess reducedTerm820 reducedTerm821 := by decide +kernel

theorem reducedMerge815Check : reducedMerge815 = Integer.Sparse.mergeBy masterLess reducedTerm822 reducedTerm823 := by decide +kernel

theorem reducedMerge816Check : reducedMerge816 = Integer.Sparse.mergeBy masterLess reducedMerge814 reducedMerge815 := by decide +kernel

theorem reducedMerge817Check : reducedMerge817 = Integer.Sparse.mergeBy masterLess reducedMerge813 reducedMerge816 := by decide +kernel

theorem reducedMerge818Check : reducedMerge818 = Integer.Sparse.mergeBy masterLess reducedMerge810 reducedMerge817 := by decide +kernel

theorem reducedMerge819Check : reducedMerge819 = Integer.Sparse.mergeBy masterLess reducedTerm825 reducedTerm826 := by decide +kernel

theorem reducedMerge820Check : reducedMerge820 = Integer.Sparse.mergeBy masterLess reducedTerm824 reducedMerge819 := by decide +kernel

theorem reducedMerge821Check : reducedMerge821 = Integer.Sparse.mergeBy masterLess reducedTerm827 reducedTerm828 := by decide +kernel

theorem reducedMerge822Check : reducedMerge822 = Integer.Sparse.mergeBy masterLess reducedTerm829 reducedTerm830 := by decide +kernel

theorem reducedMerge823Check : reducedMerge823 = Integer.Sparse.mergeBy masterLess reducedMerge821 reducedMerge822 := by decide +kernel

theorem reducedMerge824Check : reducedMerge824 = Integer.Sparse.mergeBy masterLess reducedMerge820 reducedMerge823 := by decide +kernel

theorem reducedMerge825Check : reducedMerge825 = Integer.Sparse.mergeBy masterLess reducedTerm831 reducedTerm832 := by decide +kernel

theorem reducedMerge826Check : reducedMerge826 = Integer.Sparse.mergeBy masterLess reducedTerm833 reducedTerm834 := by decide +kernel

theorem reducedMerge827Check : reducedMerge827 = Integer.Sparse.mergeBy masterLess reducedMerge825 reducedMerge826 := by decide +kernel

theorem reducedMerge828Check : reducedMerge828 = Integer.Sparse.mergeBy masterLess reducedTerm835 reducedTerm836 := by decide +kernel

theorem reducedMerge829Check : reducedMerge829 = Integer.Sparse.mergeBy masterLess reducedTerm837 reducedTerm838 := by decide +kernel

theorem reducedMerge830Check : reducedMerge830 = Integer.Sparse.mergeBy masterLess reducedMerge828 reducedMerge829 := by decide +kernel

theorem reducedMerge831Check : reducedMerge831 = Integer.Sparse.mergeBy masterLess reducedMerge827 reducedMerge830 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge832Check : reducedMerge832 = Integer.Sparse.mergeBy masterLess reducedMerge824 reducedMerge831 := by decide +kernel

theorem reducedMerge833Check : reducedMerge833 = Integer.Sparse.mergeBy masterLess reducedMerge818 reducedMerge832 := by decide +kernel

theorem reducedMerge834Check : reducedMerge834 = Integer.Sparse.mergeBy masterLess reducedMerge804 reducedMerge833 := by decide +kernel

theorem reducedMerge835Check : reducedMerge835 = Integer.Sparse.mergeBy masterLess reducedMerge775 reducedMerge834 := by decide +kernel

theorem reducedMerge836Check : reducedMerge836 = Integer.Sparse.mergeBy masterLess reducedTerm840 reducedTerm841 := by decide +kernel

theorem reducedMerge837Check : reducedMerge837 = Integer.Sparse.mergeBy masterLess reducedTerm839 reducedMerge836 := by decide +kernel

theorem reducedMerge838Check : reducedMerge838 = Integer.Sparse.mergeBy masterLess reducedTerm842 reducedTerm843 := by decide +kernel

theorem reducedMerge839Check : reducedMerge839 = Integer.Sparse.mergeBy masterLess reducedTerm844 reducedTerm845 := by decide +kernel

theorem reducedMerge840Check : reducedMerge840 = Integer.Sparse.mergeBy masterLess reducedMerge838 reducedMerge839 := by decide +kernel

theorem reducedMerge841Check : reducedMerge841 = Integer.Sparse.mergeBy masterLess reducedMerge837 reducedMerge840 := by decide +kernel

theorem reducedMerge842Check : reducedMerge842 = Integer.Sparse.mergeBy masterLess reducedTerm846 reducedTerm847 := by decide +kernel

theorem reducedMerge843Check : reducedMerge843 = Integer.Sparse.mergeBy masterLess reducedTerm848 reducedTerm849 := by decide +kernel

theorem reducedMerge844Check : reducedMerge844 = Integer.Sparse.mergeBy masterLess reducedMerge842 reducedMerge843 := by decide +kernel

theorem reducedMerge845Check : reducedMerge845 = Integer.Sparse.mergeBy masterLess reducedTerm850 reducedTerm851 := by decide +kernel

theorem reducedMerge846Check : reducedMerge846 = Integer.Sparse.mergeBy masterLess reducedTerm852 reducedTerm853 := by decide +kernel

theorem reducedMerge847Check : reducedMerge847 = Integer.Sparse.mergeBy masterLess reducedMerge845 reducedMerge846 := by decide +kernel

theorem reducedMerge848Check : reducedMerge848 = Integer.Sparse.mergeBy masterLess reducedMerge844 reducedMerge847 := by decide +kernel

theorem reducedMerge849Check : reducedMerge849 = Integer.Sparse.mergeBy masterLess reducedMerge841 reducedMerge848 := by decide +kernel

theorem reducedMerge850Check : reducedMerge850 = Integer.Sparse.mergeBy masterLess reducedTerm855 reducedTerm856 := by decide +kernel

theorem reducedMerge851Check : reducedMerge851 = Integer.Sparse.mergeBy masterLess reducedTerm854 reducedMerge850 := by decide +kernel

theorem reducedMerge852Check : reducedMerge852 = Integer.Sparse.mergeBy masterLess reducedTerm857 reducedTerm858 := by decide +kernel

theorem reducedMerge853Check : reducedMerge853 = Integer.Sparse.mergeBy masterLess reducedTerm859 reducedTerm860 := by decide +kernel

theorem reducedMerge854Check : reducedMerge854 = Integer.Sparse.mergeBy masterLess reducedMerge852 reducedMerge853 := by decide +kernel

theorem reducedMerge855Check : reducedMerge855 = Integer.Sparse.mergeBy masterLess reducedMerge851 reducedMerge854 := by decide +kernel

theorem reducedMerge856Check : reducedMerge856 = Integer.Sparse.mergeBy masterLess reducedTerm861 reducedTerm862 := by decide +kernel

theorem reducedMerge857Check : reducedMerge857 = Integer.Sparse.mergeBy masterLess reducedTerm863 reducedTerm864 := by decide +kernel

theorem reducedMerge858Check : reducedMerge858 = Integer.Sparse.mergeBy masterLess reducedMerge856 reducedMerge857 := by decide +kernel

theorem reducedMerge859Check : reducedMerge859 = Integer.Sparse.mergeBy masterLess reducedTerm865 reducedTerm866 := by decide +kernel

theorem reducedMerge860Check : reducedMerge860 = Integer.Sparse.mergeBy masterLess reducedTerm867 reducedTerm868 := by decide +kernel

theorem reducedMerge861Check : reducedMerge861 = Integer.Sparse.mergeBy masterLess reducedMerge859 reducedMerge860 := by decide +kernel

theorem reducedMerge862Check : reducedMerge862 = Integer.Sparse.mergeBy masterLess reducedMerge858 reducedMerge861 := by decide +kernel

theorem reducedMerge863Check : reducedMerge863 = Integer.Sparse.mergeBy masterLess reducedMerge855 reducedMerge862 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge864Check : reducedMerge864 = Integer.Sparse.mergeBy masterLess reducedMerge849 reducedMerge863 := by decide +kernel

theorem reducedMerge865Check : reducedMerge865 = Integer.Sparse.mergeBy masterLess reducedTerm870 reducedTerm871 := by decide +kernel

theorem reducedMerge866Check : reducedMerge866 = Integer.Sparse.mergeBy masterLess reducedTerm869 reducedMerge865 := by decide +kernel

theorem reducedMerge867Check : reducedMerge867 = Integer.Sparse.mergeBy masterLess reducedTerm872 reducedTerm873 := by decide +kernel

theorem reducedMerge868Check : reducedMerge868 = Integer.Sparse.mergeBy masterLess reducedTerm874 reducedTerm875 := by decide +kernel

theorem reducedMerge869Check : reducedMerge869 = Integer.Sparse.mergeBy masterLess reducedMerge867 reducedMerge868 := by decide +kernel

theorem reducedMerge870Check : reducedMerge870 = Integer.Sparse.mergeBy masterLess reducedMerge866 reducedMerge869 := by decide +kernel

theorem reducedMerge871Check : reducedMerge871 = Integer.Sparse.mergeBy masterLess reducedTerm876 reducedTerm877 := by decide +kernel

theorem reducedMerge872Check : reducedMerge872 = Integer.Sparse.mergeBy masterLess reducedTerm878 reducedTerm879 := by decide +kernel

theorem reducedMerge873Check : reducedMerge873 = Integer.Sparse.mergeBy masterLess reducedMerge871 reducedMerge872 := by decide +kernel

theorem reducedMerge874Check : reducedMerge874 = Integer.Sparse.mergeBy masterLess reducedTerm880 reducedTerm881 := by decide +kernel

theorem reducedMerge875Check : reducedMerge875 = Integer.Sparse.mergeBy masterLess reducedTerm882 reducedTerm883 := by decide +kernel

theorem reducedMerge876Check : reducedMerge876 = Integer.Sparse.mergeBy masterLess reducedMerge874 reducedMerge875 := by decide +kernel

theorem reducedMerge877Check : reducedMerge877 = Integer.Sparse.mergeBy masterLess reducedMerge873 reducedMerge876 := by decide +kernel

theorem reducedMerge878Check : reducedMerge878 = Integer.Sparse.mergeBy masterLess reducedMerge870 reducedMerge877 := by decide +kernel

theorem reducedMerge879Check : reducedMerge879 = Integer.Sparse.mergeBy masterLess reducedTerm885 reducedTerm886 := by decide +kernel

theorem reducedMerge880Check : reducedMerge880 = Integer.Sparse.mergeBy masterLess reducedTerm884 reducedMerge879 := by decide +kernel

theorem reducedMerge881Check : reducedMerge881 = Integer.Sparse.mergeBy masterLess reducedTerm887 reducedTerm888 := by decide +kernel

theorem reducedMerge882Check : reducedMerge882 = Integer.Sparse.mergeBy masterLess reducedTerm889 reducedTerm890 := by decide +kernel

theorem reducedMerge883Check : reducedMerge883 = Integer.Sparse.mergeBy masterLess reducedMerge881 reducedMerge882 := by decide +kernel

theorem reducedMerge884Check : reducedMerge884 = Integer.Sparse.mergeBy masterLess reducedMerge880 reducedMerge883 := by decide +kernel

theorem reducedMerge885Check : reducedMerge885 = Integer.Sparse.mergeBy masterLess reducedTerm891 reducedTerm892 := by decide +kernel

theorem reducedMerge886Check : reducedMerge886 = Integer.Sparse.mergeBy masterLess reducedTerm893 reducedTerm894 := by decide +kernel

theorem reducedMerge887Check : reducedMerge887 = Integer.Sparse.mergeBy masterLess reducedMerge885 reducedMerge886 := by decide +kernel

theorem reducedMerge888Check : reducedMerge888 = Integer.Sparse.mergeBy masterLess reducedTerm895 reducedTerm896 := by decide +kernel

theorem reducedMerge889Check : reducedMerge889 = Integer.Sparse.mergeBy masterLess reducedTerm897 reducedTerm898 := by decide +kernel

theorem reducedMerge890Check : reducedMerge890 = Integer.Sparse.mergeBy masterLess reducedMerge888 reducedMerge889 := by decide +kernel

theorem reducedMerge891Check : reducedMerge891 = Integer.Sparse.mergeBy masterLess reducedMerge887 reducedMerge890 := by decide +kernel

theorem reducedMerge892Check : reducedMerge892 = Integer.Sparse.mergeBy masterLess reducedMerge884 reducedMerge891 := by decide +kernel

theorem reducedMerge893Check : reducedMerge893 = Integer.Sparse.mergeBy masterLess reducedMerge878 reducedMerge892 := by decide +kernel

theorem reducedMerge894Check : reducedMerge894 = Integer.Sparse.mergeBy masterLess reducedMerge864 reducedMerge893 := by decide +kernel

theorem reducedMerge895Check : reducedMerge895 = Integer.Sparse.mergeBy masterLess reducedTerm900 reducedTerm901 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge896Check : reducedMerge896 = Integer.Sparse.mergeBy masterLess reducedTerm899 reducedMerge895 := by decide +kernel

theorem reducedMerge897Check : reducedMerge897 = Integer.Sparse.mergeBy masterLess reducedTerm902 reducedTerm903 := by decide +kernel

theorem reducedMerge898Check : reducedMerge898 = Integer.Sparse.mergeBy masterLess reducedTerm904 reducedTerm905 := by decide +kernel

theorem reducedMerge899Check : reducedMerge899 = Integer.Sparse.mergeBy masterLess reducedMerge897 reducedMerge898 := by decide +kernel

theorem reducedMerge900Check : reducedMerge900 = Integer.Sparse.mergeBy masterLess reducedMerge896 reducedMerge899 := by decide +kernel

theorem reducedMerge901Check : reducedMerge901 = Integer.Sparse.mergeBy masterLess reducedTerm906 reducedTerm907 := by decide +kernel

theorem reducedMerge902Check : reducedMerge902 = Integer.Sparse.mergeBy masterLess reducedTerm908 reducedTerm909 := by decide +kernel

theorem reducedMerge903Check : reducedMerge903 = Integer.Sparse.mergeBy masterLess reducedMerge901 reducedMerge902 := by decide +kernel

theorem reducedMerge904Check : reducedMerge904 = Integer.Sparse.mergeBy masterLess reducedTerm910 reducedTerm911 := by decide +kernel

theorem reducedMerge905Check : reducedMerge905 = Integer.Sparse.mergeBy masterLess reducedTerm912 reducedTerm913 := by decide +kernel

theorem reducedMerge906Check : reducedMerge906 = Integer.Sparse.mergeBy masterLess reducedMerge904 reducedMerge905 := by decide +kernel

theorem reducedMerge907Check : reducedMerge907 = Integer.Sparse.mergeBy masterLess reducedMerge903 reducedMerge906 := by decide +kernel

theorem reducedMerge908Check : reducedMerge908 = Integer.Sparse.mergeBy masterLess reducedMerge900 reducedMerge907 := by decide +kernel

theorem reducedMerge909Check : reducedMerge909 = Integer.Sparse.mergeBy masterLess reducedTerm915 reducedTerm916 := by decide +kernel

theorem reducedMerge910Check : reducedMerge910 = Integer.Sparse.mergeBy masterLess reducedTerm914 reducedMerge909 := by decide +kernel

theorem reducedMerge911Check : reducedMerge911 = Integer.Sparse.mergeBy masterLess reducedTerm917 reducedTerm918 := by decide +kernel

theorem reducedMerge912Check : reducedMerge912 = Integer.Sparse.mergeBy masterLess reducedTerm919 reducedTerm920 := by decide +kernel

theorem reducedMerge913Check : reducedMerge913 = Integer.Sparse.mergeBy masterLess reducedMerge911 reducedMerge912 := by decide +kernel

theorem reducedMerge914Check : reducedMerge914 = Integer.Sparse.mergeBy masterLess reducedMerge910 reducedMerge913 := by decide +kernel

theorem reducedMerge915Check : reducedMerge915 = Integer.Sparse.mergeBy masterLess reducedTerm921 reducedTerm922 := by decide +kernel

theorem reducedMerge916Check : reducedMerge916 = Integer.Sparse.mergeBy masterLess reducedTerm923 reducedTerm924 := by decide +kernel

theorem reducedMerge917Check : reducedMerge917 = Integer.Sparse.mergeBy masterLess reducedMerge915 reducedMerge916 := by decide +kernel

theorem reducedMerge918Check : reducedMerge918 = Integer.Sparse.mergeBy masterLess reducedTerm925 reducedTerm926 := by decide +kernel

theorem reducedMerge919Check : reducedMerge919 = Integer.Sparse.mergeBy masterLess reducedTerm927 reducedTerm928 := by decide +kernel

theorem reducedMerge920Check : reducedMerge920 = Integer.Sparse.mergeBy masterLess reducedMerge918 reducedMerge919 := by decide +kernel

theorem reducedMerge921Check : reducedMerge921 = Integer.Sparse.mergeBy masterLess reducedMerge917 reducedMerge920 := by decide +kernel

theorem reducedMerge922Check : reducedMerge922 = Integer.Sparse.mergeBy masterLess reducedMerge914 reducedMerge921 := by decide +kernel

theorem reducedMerge923Check : reducedMerge923 = Integer.Sparse.mergeBy masterLess reducedMerge908 reducedMerge922 := by decide +kernel

theorem reducedMerge924Check : reducedMerge924 = Integer.Sparse.mergeBy masterLess reducedTerm930 reducedTerm931 := by decide +kernel

theorem reducedMerge925Check : reducedMerge925 = Integer.Sparse.mergeBy masterLess reducedTerm929 reducedMerge924 := by decide +kernel

theorem reducedMerge926Check : reducedMerge926 = Integer.Sparse.mergeBy masterLess reducedTerm932 reducedTerm933 := by decide +kernel

theorem reducedMerge927Check : reducedMerge927 = Integer.Sparse.mergeBy masterLess reducedTerm934 reducedTerm935 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge928Check : reducedMerge928 = Integer.Sparse.mergeBy masterLess reducedMerge926 reducedMerge927 := by decide +kernel

theorem reducedMerge929Check : reducedMerge929 = Integer.Sparse.mergeBy masterLess reducedMerge925 reducedMerge928 := by decide +kernel

theorem reducedMerge930Check : reducedMerge930 = Integer.Sparse.mergeBy masterLess reducedTerm936 reducedTerm937 := by decide +kernel

theorem reducedMerge931Check : reducedMerge931 = Integer.Sparse.mergeBy masterLess reducedTerm938 reducedTerm939 := by decide +kernel

theorem reducedMerge932Check : reducedMerge932 = Integer.Sparse.mergeBy masterLess reducedMerge930 reducedMerge931 := by decide +kernel

theorem reducedMerge933Check : reducedMerge933 = Integer.Sparse.mergeBy masterLess reducedTerm940 reducedTerm941 := by decide +kernel

theorem reducedMerge934Check : reducedMerge934 = Integer.Sparse.mergeBy masterLess reducedTerm942 reducedTerm943 := by decide +kernel

theorem reducedMerge935Check : reducedMerge935 = Integer.Sparse.mergeBy masterLess reducedMerge933 reducedMerge934 := by decide +kernel

theorem reducedMerge936Check : reducedMerge936 = Integer.Sparse.mergeBy masterLess reducedMerge932 reducedMerge935 := by decide +kernel

theorem reducedMerge937Check : reducedMerge937 = Integer.Sparse.mergeBy masterLess reducedMerge929 reducedMerge936 := by decide +kernel

theorem reducedMerge938Check : reducedMerge938 = Integer.Sparse.mergeBy masterLess reducedTerm945 reducedTerm946 := by decide +kernel

theorem reducedMerge939Check : reducedMerge939 = Integer.Sparse.mergeBy masterLess reducedTerm944 reducedMerge938 := by decide +kernel

theorem reducedMerge940Check : reducedMerge940 = Integer.Sparse.mergeBy masterLess reducedTerm947 reducedTerm948 := by decide +kernel

theorem reducedMerge941Check : reducedMerge941 = Integer.Sparse.mergeBy masterLess reducedTerm949 reducedTerm950 := by decide +kernel

theorem reducedMerge942Check : reducedMerge942 = Integer.Sparse.mergeBy masterLess reducedMerge940 reducedMerge941 := by decide +kernel

theorem reducedMerge943Check : reducedMerge943 = Integer.Sparse.mergeBy masterLess reducedMerge939 reducedMerge942 := by decide +kernel

theorem reducedMerge944Check : reducedMerge944 = Integer.Sparse.mergeBy masterLess reducedTerm951 reducedTerm952 := by decide +kernel

theorem reducedMerge945Check : reducedMerge945 = Integer.Sparse.mergeBy masterLess reducedTerm953 reducedTerm954 := by decide +kernel

theorem reducedMerge946Check : reducedMerge946 = Integer.Sparse.mergeBy masterLess reducedMerge944 reducedMerge945 := by decide +kernel

theorem reducedMerge947Check : reducedMerge947 = Integer.Sparse.mergeBy masterLess reducedTerm955 reducedTerm956 := by decide +kernel

theorem reducedMerge948Check : reducedMerge948 = Integer.Sparse.mergeBy masterLess reducedTerm957 reducedTerm958 := by decide +kernel

theorem reducedMerge949Check : reducedMerge949 = Integer.Sparse.mergeBy masterLess reducedMerge947 reducedMerge948 := by decide +kernel

theorem reducedMerge950Check : reducedMerge950 = Integer.Sparse.mergeBy masterLess reducedMerge946 reducedMerge949 := by decide +kernel

theorem reducedMerge951Check : reducedMerge951 = Integer.Sparse.mergeBy masterLess reducedMerge943 reducedMerge950 := by decide +kernel

theorem reducedMerge952Check : reducedMerge952 = Integer.Sparse.mergeBy masterLess reducedMerge937 reducedMerge951 := by decide +kernel

theorem reducedMerge953Check : reducedMerge953 = Integer.Sparse.mergeBy masterLess reducedMerge923 reducedMerge952 := by decide +kernel

theorem reducedMerge954Check : reducedMerge954 = Integer.Sparse.mergeBy masterLess reducedMerge894 reducedMerge953 := by decide +kernel

theorem reducedMerge955Check : reducedMerge955 = Integer.Sparse.mergeBy masterLess reducedMerge835 reducedMerge954 := by decide +kernel

theorem reducedMerge956Check : reducedMerge956 = Integer.Sparse.mergeBy masterLess reducedMerge716 reducedMerge955 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval719 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm719 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm719 (originalVector B) := by
  rw [reducedTermArithmetic719, ← sound1804 B hB hF]
  change (2797448960684851200000 : ℝ) * mixedMoment B node1804 node1804Labels =
    (37623398400 : ℝ) * ((74353968000 : ℝ) * mixedMoment B node1804 node1804Labels + 0)
  ring

theorem reducedTermEval720 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm720 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm720 (originalVector B) := by
  rw [reducedTermArithmetic720, ← sound1805 B hB hF]
  change (3885170543988572160000 : ℝ) * mixedMoment B node1805 node1805Labels =
    (37623398400 : ℝ) * ((103264742400 : ℝ) * mixedMoment B node1805 node1805Labels + 0)
  ring

theorem reducedTermEval721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm721 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm721 (originalVector B) := by
  rw [reducedTermArithmetic721, ← sound1806 B hB hF]
  change (-9608222007357603840000 : ℝ) * mixedMoment B node1806 node1806Labels =
    (37623398400 : ℝ) * (((-255378897600 : ℤ) : ℝ) * mixedMoment B node1806 node1806Labels + 0)
  ring

theorem reducedTermEval722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm722 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm722 (originalVector B) := by
  rw [reducedTermArithmetic722, ← sound1807 B hB hF]
  change (9318508415649054720000 : ℝ) * mixedMoment B node1807 node1807Labels =
    (37623398400 : ℝ) * ((247678540800 : ℝ) * mixedMoment B node1807 node1807Labels + 0)
  ring

theorem reducedTermEval723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm723 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm723 (originalVector B) := by
  rw [reducedTermArithmetic723, ← sound1808 B hB hF]
  change (-4955053941050572800000 : ℝ) * mixedMoment B node1808 node1808Labels =
    (37623398400 : ℝ) * (((-131701392000 : ℤ) : ℝ) * mixedMoment B node1808 node1808Labels + 0)
  ring

theorem reducedTermEval724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm724 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm724 (originalVector B) := by
  rw [reducedTermArithmetic724, ← sound1809 B hB hF]
  change (-3537875996458352640000 : ℝ) * mixedMoment B node1809 node1809Labels =
    (37623398400 : ℝ) * (((-94033929600 : ℤ) : ℝ) * mixedMoment B node1809 node1809Labels + 0)
  ring

theorem reducedTermEval725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm725 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm725 (originalVector B) := by
  rw [reducedTermArithmetic725, ← sound1810 B hB hF]
  change (-3345967769848381440000 : ℝ) * mixedMoment B node1810 node1810Labels =
    (37623398400 : ℝ) * (((-88933161600 : ℤ) : ℝ) * mixedMoment B node1810 node1810Labels + 0)
  ring

theorem reducedTermEval726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm726 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm726 (originalVector B) := by
  rw [reducedTermArithmetic726, ← sound1811 B hB hF]
  change (4908991524093296640000 : ℝ) * mixedMoment B node1811 node1811Labels =
    (37623398400 : ℝ) * ((130477089600 : ℝ) * mixedMoment B node1811 node1811Labels + 0)
  ring

theorem reducedTermEval727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm727 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm727 (originalVector B) := by
  rw [reducedTermArithmetic727, ← sound1812 B hB hF]
  change (-11721265473473740800000 : ℝ) * mixedMoment B node1812 node1812Labels =
    (37623398400 : ℝ) * (((-311541912000 : ℤ) : ℝ) * mixedMoment B node1812 node1812Labels + 0)
  ring

theorem reducedTermEval728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm728 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm728 (originalVector B) := by
  rw [reducedTermArithmetic728, ← sound1813 B hB hF]
  change (6324490501957877760000 : ℝ) * mixedMoment B node1813 node1813Labels =
    (37623398400 : ℝ) * ((168099926400 : ℝ) * mixedMoment B node1813 node1813Labels + 0)
  ring

theorem reducedTermEval729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm729 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm729 (originalVector B) := by
  rw [reducedTermArithmetic729, ← sound1814 B hB hF]
  change (2579448756790886400000 : ℝ) * mixedMoment B node1814 node1814Labels =
    (37623398400 : ℝ) * ((68559696000 : ℝ) * mixedMoment B node1814 node1814Labels + 0)
  ring

theorem reducedTermEval730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm730 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm730 (originalVector B) := by
  rw [reducedTermArithmetic730, ← sound1815 B hB hF]
  change (-8001262491225292800000 : ℝ) * mixedMoment B node1815 node1815Labels =
    (37623398400 : ℝ) * (((-212667192000 : ℤ) : ℝ) * mixedMoment B node1815 node1815Labels + 0)
  ring

theorem reducedTermEval731 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm731 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm731 (originalVector B) := by
  rw [reducedTermArithmetic731, ← sound1816 B hB hF]
  change (8788236653722337280000 : ℝ) * mixedMoment B node1816 node1816Labels =
    (37623398400 : ℝ) * ((233584339200 : ℝ) * mixedMoment B node1816 node1816Labels + 0)
  ring

theorem reducedTermEval732 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm732 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm732 (originalVector B) := by
  rw [reducedTermArithmetic732, ← sound1817 B hB hF]
  change (-1747607698444124160000 : ℝ) * mixedMoment B node1817 node1817Labels =
    (37623398400 : ℝ) * (((-46450022400 : ℤ) : ℝ) * mixedMoment B node1817 node1817Labels + 0)
  ring

theorem reducedTermEval733 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm733 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm733 (originalVector B) := by
  rw [reducedTermArithmetic733, ← sound1818 B hB hF]
  change (-7591910646227927040000 : ℝ) * mixedMoment B node1818 node1818Labels =
    (37623398400 : ℝ) * (((-201786945600 : ℤ) : ℝ) * mixedMoment B node1818 node1818Labels + 0)
  ring

theorem reducedTermEval734 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm734 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm734 (originalVector B) := by
  rw [reducedTermArithmetic734, ← sound1819 B hB hF]
  change (-10541826291919749120000 : ℝ) * mixedMoment B node1819 node1819Labels =
    (37623398400 : ℝ) * (((-280193356800 : ℤ) : ℝ) * mixedMoment B node1819 node1819Labels + 0)
  ring

theorem reducedTermEval735 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm735 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm735 (originalVector B) := by
  rw [reducedTermArithmetic735, ← sound1820 B hB hF]
  change (-629645571257794560000 : ℝ) * mixedMoment B node1820 node1820Labels =
    (37623398400 : ℝ) * (((-16735478400 : ℤ) : ℝ) * mixedMoment B node1820 node1820Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm736 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm736 (originalVector B) := by
  rw [reducedTermArithmetic736, ← sound1821 B hB hF]
  change (1301309194638458880000 : ℝ) * mixedMoment B node1821 node1821Labels =
    (37623398400 : ℝ) * ((34587763200 : ℝ) * mixedMoment B node1821 node1821Labels + 0)
  ring

theorem reducedTermEval737 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm737 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm737 (originalVector B) := by
  rw [reducedTermArithmetic737, ← sound1822 B hB hF]
  change (1098658614922444800000 : ℝ) * mixedMoment B node1822 node1822Labels =
    (37623398400 : ℝ) * ((29201472000 : ℝ) * mixedMoment B node1822 node1822Labels + 0)
  ring

theorem reducedTermEval738 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm738 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm738 (originalVector B) := by
  rw [reducedTermArithmetic738, ← sound1823 B hB hF]
  change (-1301309194638458880000 : ℝ) * mixedMoment B node1823 node1823Labels =
    (37623398400 : ℝ) * (((-34587763200 : ℤ) : ℝ) * mixedMoment B node1823 node1823Labels + 0)
  ring

theorem reducedTermEval739 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm739 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm739 (originalVector B) := by
  rw [reducedTermArithmetic739, ← sound1824 B hB hF]
  change (819808734353817600000 : ℝ) * mixedMoment B node1824 node1824Labels =
    (37623398400 : ℝ) * ((21789864000 : ℝ) * mixedMoment B node1824 node1824Labels + 0)
  ring

theorem reducedTermEval740 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm740 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm740 (originalVector B) := by
  rw [reducedTermArithmetic740, ← sound1825 B hB hF]
  change (3329639154745344000000 : ℝ) * mixedMoment B node1825 node1825Labels =
    (37623398400 : ℝ) * ((88499160000 : ℝ) * mixedMoment B node1825 node1825Labels + 0)
  ring

theorem reducedTermEval741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm741 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm741 (originalVector B) := by
  rw [reducedTermArithmetic741, ← sound1826 B hB hF]
  change (2357878242882355200000 : ℝ) * mixedMoment B node1826 node1826Labels =
    (37623398400 : ℝ) * ((62670528000 : ℝ) * mixedMoment B node1826 node1826Labels + 0)
  ring

theorem reducedTermEval742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm742 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm742 (originalVector B) := by
  rw [reducedTermArithmetic742, ← sound1827 B hB hF]
  change (-1098658614922444800000 : ℝ) * mixedMoment B node1827 node1827Labels =
    (37623398400 : ℝ) * (((-29201472000 : ℤ) : ℝ) * mixedMoment B node1827 node1827Labels + 0)
  ring

theorem reducedTermEval743 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm743 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm743 (originalVector B) := by
  rw [reducedTermArithmetic743, ← sound1828 B hB hF]
  change (-750480790392668160000 : ℝ) * mixedMoment B node1828 node1828Labels =
    (37623398400 : ℝ) * (((-19947182400 : ℤ) : ℝ) * mixedMoment B node1828 node1828Labels + 0)
  ring

theorem reducedTermEval744 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm744 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm744 (originalVector B) := by
  rw [reducedTermArithmetic744, ← sound1829 B hB hF]
  change (6755524079380070400000 : ℝ) * mixedMoment B node1829 node1829Labels =
    (37623398400 : ℝ) * ((179556456000 : ℝ) * mixedMoment B node1829 node1829Labels + 0)
  ring

theorem reducedTermEval745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm745 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm745 (originalVector B) := by
  rw [reducedTermArithmetic745, ← sound1830 B hB hF]
  change (2387485449525657600000 : ℝ) * mixedMoment B node1830 node1830Labels =
    (37623398400 : ℝ) * ((63457464000 : ℝ) * mixedMoment B node1830 node1830Labels + 0)
  ring

theorem reducedTermEval746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm746 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm746 (originalVector B) := by
  rw [reducedTermArithmetic746, ← sound1831 B hB hF]
  change (4222772882708889600000 : ℝ) * mixedMoment B node1831 node1831Labels =
    (37623398400 : ℝ) * ((112237944000 : ℝ) * mixedMoment B node1831 node1831Labels + 0)
  ring

theorem reducedTermEval747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm747 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm747 (originalVector B) := by
  rw [reducedTermArithmetic747, ← sound1832 B hB hF]
  change (-971893105435607040000 : ℝ) * mixedMoment B node1832 node1832Labels =
    (37623398400 : ℝ) * (((-25832145600 : ℤ) : ℝ) * mixedMoment B node1832 node1832Labels + 0)
  ring

theorem reducedTermEval748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm748 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm748 (originalVector B) := by
  rw [reducedTermArithmetic748, ← sound1957 B hB hF]
  change (-478232461800898560000 : ℝ) * mixedMoment B node1957 node1957Labels =
    (37623398400 : ℝ) * (((-12711038400 : ℤ) : ℝ) * mixedMoment B node1957 node1957Labels + 0)
  ring

theorem reducedTermEval749 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm749 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm749 (originalVector B) := by
  rw [reducedTermArithmetic749, ← sound1964 B hB hF]
  change (-23934621521018880000 : ℝ) * mixedMoment B node1964 node1964Labels =
    (37623398400 : ℝ) * (((-636163200 : ℤ) : ℝ) * mixedMoment B node1964 node1964Labels + 0)
  ring

theorem reducedTermEval750 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm750 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm750 (originalVector B) := by
  rw [reducedTermArithmetic750, ← sound1965 B hB hF]
  change (2241235474277990400000 : ℝ) * mixedMoment B node1965 node1965Labels =
    (37623398400 : ℝ) * ((59570256000 : ℝ) * mixedMoment B node1965 node1965Labels + 0)
  ring

theorem reducedTermEval751 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm751 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm751 (originalVector B) := by
  rw [reducedTermArithmetic751, ← sound1966 B hB hF]
  change (5347929085248798720000 : ℝ) * mixedMoment B node1966 node1966Labels =
    (37623398400 : ℝ) * ((142143700800 : ℝ) * mixedMoment B node1966 node1966Labels + 0)
  ring

theorem reducedTermEval752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm752 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm752 (originalVector B) := by
  rw [reducedTermArithmetic752, ← sound1967 B hB hF]
  change (842806262366208000000 : ℝ) * mixedMoment B node1967 node1967Labels =
    (37623398400 : ℝ) * ((22401120000 : ℝ) * mixedMoment B node1967 node1967Labels + 0)
  ring

theorem reducedTermEval753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm753 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm753 (originalVector B) := by
  rw [reducedTermArithmetic753, ← sound1970 B hB hF]
  change (2206413845208760320000 : ℝ) * mixedMoment B node1970 node1970Labels =
    (37623398400 : ℝ) * ((58644724800 : ℝ) * mixedMoment B node1970 node1970Labels + 0)
  ring

theorem reducedTermEval754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm754 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm754 (originalVector B) := by
  rw [reducedTermArithmetic754, ← sound1971 B hB hF]
  change (3110224913045913600000 : ℝ) * mixedMoment B node1971 node1971Labels =
    (37623398400 : ℝ) * ((82667304000 : ℝ) * mixedMoment B node1971 node1971Labels + 0)
  ring

theorem reducedTermEval755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm755 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm755 (originalVector B) := by
  rw [reducedTermArithmetic755, ← sound1973 B hB hF]
  change (6990515310978662400000 : ℝ) * mixedMoment B node1973 node1973Labels =
    (37623398400 : ℝ) * ((185802336000 : ℝ) * mixedMoment B node1973 node1973Labels + 0)
  ring

theorem reducedTermEval756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm756 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm756 (originalVector B) := by
  rw [reducedTermArithmetic756, ← sound1976 B hB hF]
  change (2052530594103951360000 : ℝ) * mixedMoment B node1976 node1976Labels =
    (37623398400 : ℝ) * ((54554630400 : ℝ) * mixedMoment B node1976 node1976Labels + 0)
  ring

theorem reducedTermEval757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm757 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm757 (originalVector B) := by
  rw [reducedTermArithmetic757, ← sound1977 B hB hF]
  change (-1235015743301222400000 : ℝ) * mixedMoment B node1977 node1977Labels =
    (37623398400 : ℝ) * (((-32825736000 : ℤ) : ℝ) * mixedMoment B node1977 node1977Labels + 0)
  ring

theorem reducedTermEval758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm758 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm758 (originalVector B) := by
  rw [reducedTermArithmetic758, ← sound1978 B hB hF]
  change (4959624732475392000000 : ℝ) * mixedMoment B node1978 node1978Labels =
    (37623398400 : ℝ) * ((131822880000 : ℝ) * mixedMoment B node1978 node1978Labels + 0)
  ring

theorem reducedTermEval759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm759 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm759 (originalVector B) := by
  rw [reducedTermArithmetic759, ← sound1979 B hB hF]
  change (5755499567677440000000 : ℝ) * mixedMoment B node1979 node1979Labels =
    (37623398400 : ℝ) * ((152976600000 : ℝ) * mixedMoment B node1979 node1979Labels + 0)
  ring

theorem reducedTermEval760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm760 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm760 (originalVector B) := by
  rw [reducedTermArithmetic760, ← sound1980 B hB hF]
  change (5338073982173184000000 : ℝ) * mixedMoment B node1980 node1980Labels =
    (37623398400 : ℝ) * ((141881760000 : ℝ) * mixedMoment B node1980 node1980Labels + 0)
  ring

theorem reducedTermEval761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm761 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm761 (originalVector B) := by
  rw [reducedTermArithmetic761, ← sound2010 B hB hF]
  change (-3936013149156802560000 : ℝ) * mixedMoment B node2010 node2010Labels =
    (37623398400 : ℝ) * (((-104616098400 : ℤ) : ℝ) * mixedMoment B node2010 node2010Labels + 0)
  ring

theorem reducedTermEval762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm762 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm762 (originalVector B) := by
  rw [reducedTermArithmetic762, ← sound2019 B hB hF]
  change (-2983567758946467840000 : ℝ) * mixedMoment B node2019 node2019Labels =
    (37623398400 : ℝ) * (((-79300857600 : ℤ) : ℝ) * mixedMoment B node2019 node2019Labels + 0)
  ring

theorem reducedTermEval763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm763 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm763 (originalVector B) := by
  rw [reducedTermArithmetic763, ← sound2020 B hB hF]
  change (755963843883171840000 : ℝ) * mixedMoment B node2020 node2020Labels =
    (37623398400 : ℝ) * ((20092917600 : ℝ) * mixedMoment B node2020 node2020Labels + 0)
  ring

theorem reducedTermEval764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm764 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm764 (originalVector B) := by
  rw [reducedTermArithmetic764, ← sound2022 B hB hF]
  change (2983567758946467840000 : ℝ) * mixedMoment B node2022 node2022Labels =
    (37623398400 : ℝ) * ((79300857600 : ℝ) * mixedMoment B node2022 node2022Labels + 0)
  ring

theorem reducedTermEval765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm765 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm765 (originalVector B) := by
  rw [reducedTermArithmetic765, ← sound2023 B hB hF]
  change (88617370024673280000 : ℝ) * mixedMoment B node2023 node2023Labels =
    (37623398400 : ℝ) * ((2355379200 : ℝ) * mixedMoment B node2023 node2023Labels + 0)
  ring

theorem reducedTermEval766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm766 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm766 (originalVector B) := by
  rw [reducedTermArithmetic766, ← sound2025 B hB hF]
  change (-4644957617419714560000 : ℝ) * mixedMoment B node2025 node2025Labels =
    (37623398400 : ℝ) * (((-123459278400 : ℤ) : ℝ) * mixedMoment B node2025 node2025Labels + 0)
  ring

theorem reducedTermEval767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm767 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm767 (originalVector B) := by
  rw [reducedTermArithmetic767, ← sound2026 B hB hF]
  change (3018336835652812800000 : ℝ) * mixedMoment B node2026 node2026Labels =
    (37623398400 : ℝ) * ((80224992000 : ℝ) * mixedMoment B node2026 node2026Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval717 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge717 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge717 (originalVector B) := by
  rw [reducedMerge717Check, Integer.Sparse.eval_mergeBy, reducedTermEval720 B hB hF, reducedTermEval721 B hB hF]
  rw [originalMerge717, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge718 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge718 (originalVector B) := by
  rw [reducedMerge718Check, Integer.Sparse.eval_mergeBy, reducedTermEval719 B hB hF, reducedMergeEval717 B hB hF]
  rw [originalMerge718, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval719 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge719 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge719 (originalVector B) := by
  rw [reducedMerge719Check, Integer.Sparse.eval_mergeBy, reducedTermEval722 B hB hF, reducedTermEval723 B hB hF]
  rw [originalMerge719, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval720 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge720 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge720 (originalVector B) := by
  rw [reducedMerge720Check, Integer.Sparse.eval_mergeBy, reducedTermEval724 B hB hF, reducedTermEval725 B hB hF]
  rw [originalMerge720, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge721 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge721 (originalVector B) := by
  rw [reducedMerge721Check, Integer.Sparse.eval_mergeBy, reducedMergeEval719 B hB hF, reducedMergeEval720 B hB hF]
  rw [originalMerge721, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge722 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge722 (originalVector B) := by
  rw [reducedMerge722Check, Integer.Sparse.eval_mergeBy, reducedMergeEval718 B hB hF, reducedMergeEval721 B hB hF]
  rw [originalMerge722, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge723 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge723 (originalVector B) := by
  rw [reducedMerge723Check, Integer.Sparse.eval_mergeBy, reducedTermEval726 B hB hF, reducedTermEval727 B hB hF]
  rw [originalMerge723, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge724 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge724 (originalVector B) := by
  rw [reducedMerge724Check, Integer.Sparse.eval_mergeBy, reducedTermEval728 B hB hF, reducedTermEval729 B hB hF]
  rw [originalMerge724, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge725 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge725 (originalVector B) := by
  rw [reducedMerge725Check, Integer.Sparse.eval_mergeBy, reducedMergeEval723 B hB hF, reducedMergeEval724 B hB hF]
  rw [originalMerge725, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge726 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge726 (originalVector B) := by
  rw [reducedMerge726Check, Integer.Sparse.eval_mergeBy, reducedTermEval730 B hB hF, reducedTermEval731 B hB hF]
  rw [originalMerge726, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge727 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge727 (originalVector B) := by
  rw [reducedMerge727Check, Integer.Sparse.eval_mergeBy, reducedTermEval732 B hB hF, reducedTermEval733 B hB hF]
  rw [originalMerge727, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge728 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge728 (originalVector B) := by
  rw [reducedMerge728Check, Integer.Sparse.eval_mergeBy, reducedMergeEval726 B hB hF, reducedMergeEval727 B hB hF]
  rw [originalMerge728, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge729 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge729 (originalVector B) := by
  rw [reducedMerge729Check, Integer.Sparse.eval_mergeBy, reducedMergeEval725 B hB hF, reducedMergeEval728 B hB hF]
  rw [originalMerge729, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge730 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge730 (originalVector B) := by
  rw [reducedMerge730Check, Integer.Sparse.eval_mergeBy, reducedMergeEval722 B hB hF, reducedMergeEval729 B hB hF]
  rw [originalMerge730, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval731 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge731 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge731 (originalVector B) := by
  rw [reducedMerge731Check, Integer.Sparse.eval_mergeBy, reducedTermEval735 B hB hF, reducedTermEval736 B hB hF]
  rw [originalMerge731, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval732 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge732 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge732 (originalVector B) := by
  rw [reducedMerge732Check, Integer.Sparse.eval_mergeBy, reducedTermEval734 B hB hF, reducedMergeEval731 B hB hF]
  rw [originalMerge732, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval733 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge733 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge733 (originalVector B) := by
  rw [reducedMerge733Check, Integer.Sparse.eval_mergeBy, reducedTermEval737 B hB hF, reducedTermEval738 B hB hF]
  rw [originalMerge733, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval734 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge734 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge734 (originalVector B) := by
  rw [reducedMerge734Check, Integer.Sparse.eval_mergeBy, reducedTermEval739 B hB hF, reducedTermEval740 B hB hF]
  rw [originalMerge734, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval735 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge735 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge735 (originalVector B) := by
  rw [reducedMerge735Check, Integer.Sparse.eval_mergeBy, reducedMergeEval733 B hB hF, reducedMergeEval734 B hB hF]
  rw [originalMerge735, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm768 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm768 (originalVector B) := by
  rw [reducedTermArithmetic768, ← sound2028 B hB hF]
  change (590858676786954240000 : ℝ) * mixedMoment B node2028 node2028Labels =
    (37623398400 : ℝ) * ((15704553600 : ℝ) * mixedMoment B node2028 node2028Labels + 0)
  ring

theorem reducedTermEval769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm769 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm769 (originalVector B) := by
  rw [reducedTermArithmetic769, ← sound2029 B hB hF]
  change (-2441576368615587840000 : ℝ) * mixedMoment B node2029 node2029Labels =
    (37623398400 : ℝ) * (((-64895157600 : ℤ) : ℝ) * mixedMoment B node2029 node2029Labels + 0)
  ring

theorem reducedTermEval770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm770 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm770 (originalVector B) := by
  rw [reducedTermArithmetic770, ← sound2037 B hB hF]
  change (4121680737526087680000 : ℝ) * mixedMoment B node2037 node2037Labels =
    (37623398400 : ℝ) * ((109550995200 : ℝ) * mixedMoment B node2037 node2037Labels + 0)
  ring

theorem reducedTermEval771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm771 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm771 (originalVector B) := by
  rw [reducedTermArithmetic771, ← sound2039 B hB hF]
  change (6300739362226176000000 : ℝ) * mixedMoment B node2039 node2039Labels =
    (37623398400 : ℝ) * ((167468640000 : ℝ) * mixedMoment B node2039 node2039Labels + 0)
  ring

theorem reducedTermEval772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm772 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm772 (originalVector B) := by
  rw [reducedTermArithmetic772, ← sound2051 B hB hF]
  change (-2470341383010385920000 : ℝ) * mixedMoment B node2051 node2051Labels =
    (37623398400 : ℝ) * (((-65659708800 : ℤ) : ℝ) * mixedMoment B node2051 node2051Labels + 0)
  ring

theorem reducedTermEval773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm773 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm773 (originalVector B) := by
  rw [reducedTermArithmetic773, ← sound2054 B hB hF]
  change (2470341383010385920000 : ℝ) * mixedMoment B node2054 node2054Labels =
    (37623398400 : ℝ) * ((65659708800 : ℝ) * mixedMoment B node2054 node2054Labels + 0)
  ring

theorem reducedTermEval774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm774 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm774 (originalVector B) := by
  rw [reducedTermArithmetic774, ← sound2058 B hB hF]
  change (-2837840598442967040000 : ℝ) * mixedMoment B node2058 node2058Labels =
    (37623398400 : ℝ) * (((-75427545600 : ℤ) : ℝ) * mixedMoment B node2058 node2058Labels + 0)
  ring

theorem reducedTermEval775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm775 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm775 (originalVector B) := by
  rw [reducedTermArithmetic775, ← sound2062 B hB hF]
  change (-3893099630053294080000 : ℝ) * mixedMoment B node2062 node2062Labels =
    (37623398400 : ℝ) * (((-103475491200 : ℤ) : ℝ) * mixedMoment B node2062 node2062Labels + 0)
  ring

theorem reducedTermEval776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm776 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm776 (originalVector B) := by
  rw [reducedTermArithmetic776, ← sound2088 B hB hF]
  change (-2282493232765992960000 : ℝ) * mixedMoment B node2088 node2088Labels =
    (37623398400 : ℝ) * (((-60666854400 : ℤ) : ℝ) * mixedMoment B node2088 node2088Labels + 0)
  ring

theorem reducedTermEval777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm777 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm777 (originalVector B) := by
  rw [reducedTermArithmetic777, ← sound2089 B hB hF]
  change (-18920168420746199040000 : ℝ) * mixedMoment B node2089 node2089Labels =
    (37623398400 : ℝ) * (((-502883025600 : ℤ) : ℝ) * mixedMoment B node2089 node2089Labels + 0)
  ring

theorem reducedTermEval778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm778 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm778 (originalVector B) := by
  rw [reducedTermArithmetic778, ← sound2090 B hB hF]
  change (-27244411052347883520000 : ℝ) * mixedMoment B node2090 node2090Labels =
    (37623398400 : ℝ) * (((-724134772800 : ℤ) : ℝ) * mixedMoment B node2090 node2090Labels + 0)
  ring

theorem reducedTermEval779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm779 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm779 (originalVector B) := by
  rw [reducedTermArithmetic779, ← sound2092 B hB hF]
  change (14205848185641369600000 : ℝ) * mixedMoment B node2092 node2092Labels =
    (37623398400 : ℝ) * ((377580144000 : ℝ) * mixedMoment B node2092 node2092Labels + 0)
  ring

theorem reducedTermEval780 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm780 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm780 (originalVector B) := by
  rw [reducedTermArithmetic780, ← sound2094 B hB hF]
  change (15839955060530872320000 : ℝ) * mixedMoment B node2094 node2094Labels =
    (37623398400 : ℝ) * ((421013404800 : ℝ) * mixedMoment B node2094 node2094Labels + 0)
  ring

theorem reducedTermEval781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm781 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm781 (originalVector B) := by
  rw [reducedTermArithmetic781, ← sound2104 B hB hF]
  change (-28541892592926720000 : ℝ) * mixedMoment B node2104 node2104Labels =
    (37623398400 : ℝ) * (((-758620800 : ℤ) : ℝ) * mixedMoment B node2104 node2104Labels + 0)
  ring

theorem reducedTermEval782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm782 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm782 (originalVector B) := by
  rw [reducedTermArithmetic782, ← sound2105 B hB hF]
  change (-338218339097640960000 : ℝ) * mixedMoment B node2105 node2105Labels =
    (37623398400 : ℝ) * (((-8989574400 : ℤ) : ℝ) * mixedMoment B node2105 node2105Labels + 0)
  ring

theorem reducedTermEval783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm783 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm783 (originalVector B) := by
  rw [reducedTermArithmetic783, ← sound2106 B hB hF]
  change (283347893291581440000 : ℝ) * mixedMoment B node2106 node2106Labels =
    (37623398400 : ℝ) * ((7531161600 : ℝ) * mixedMoment B node2106 node2106Labels + 0)
  ring

theorem reducedTermEval784 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm784 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm784 (originalVector B) := by
  rw [reducedTermArithmetic784, ← sound2107 B hB hF]
  change (5704108413360537600000 : ℝ) * mixedMoment B node2107 node2107Labels =
    (37623398400 : ℝ) * ((151610664000 : ℝ) * mixedMoment B node2107 node2107Labels + 0)
  ring

theorem reducedTermEval785 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm785 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm785 (originalVector B) := by
  rw [reducedTermArithmetic785, ← sound2108 B hB hF]
  change (-18375094409940172800000 : ℝ) * mixedMoment B node2108 node2108Labels =
    (37623398400 : ℝ) * (((-488395392000 : ℤ) : ℝ) * mixedMoment B node2108 node2108Labels + 0)
  ring

theorem reducedTermEval786 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm786 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm786 (originalVector B) := by
  rw [reducedTermArithmetic786, ← sound2109 B hB hF]
  change (5542318650230046720000 : ℝ) * mixedMoment B node2109 node2109Labels =
    (37623398400 : ℝ) * ((147310420800 : ℝ) * mixedMoment B node2109 node2109Labels + 0)
  ring

theorem reducedTermEval787 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm787 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm787 (originalVector B) := by
  rw [reducedTermArithmetic787, ← sound2110 B hB hF]
  change (-14180570318501314560000 : ℝ) * mixedMoment B node2110 node2110Labels =
    (37623398400 : ℝ) * (((-376908278400 : ℤ) : ℝ) * mixedMoment B node2110 node2110Labels + 0)
  ring

theorem reducedTermEval788 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm788 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm788 (originalVector B) := by
  rw [reducedTermArithmetic788, ← sound2112 B hB hF]
  change (-3684095090420613120000 : ℝ) * mixedMoment B node2112 node2112Labels =
    (37623398400 : ℝ) * (((-97920316800 : ℤ) : ℝ) * mixedMoment B node2112 node2112Labels + 0)
  ring

theorem reducedTermEval789 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm789 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm789 (originalVector B) := by
  rw [reducedTermArithmetic789, ← sound2113 B hB hF]
  change (-757176972741181440000 : ℝ) * mixedMoment B node2113 node2113Labels =
    (37623398400 : ℝ) * (((-20125161600 : ℤ) : ℝ) * mixedMoment B node2113 node2113Labels + 0)
  ring

theorem reducedTermEval790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm790 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm790 (originalVector B) := by
  rw [reducedTermArithmetic790, ← sound2115 B hB hF]
  change (-12013936625481154560000 : ℝ) * mixedMoment B node2115 node2115Labels =
    (37623398400 : ℝ) * (((-319320878400 : ℤ) : ℝ) * mixedMoment B node2115 node2115Labels + 0)
  ring

theorem reducedTermEval791 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm791 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm791 (originalVector B) := by
  rw [reducedTermArithmetic791, ← sound2116 B hB hF]
  change (-1563346111522406400000 : ℝ) * mixedMoment B node2116 node2116Labels =
    (37623398400 : ℝ) * (((-41552496000 : ℤ) : ℝ) * mixedMoment B node2116 node2116Labels + 0)
  ring

theorem reducedTermEval792 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm792 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm792 (originalVector B) := by
  rw [reducedTermArithmetic792, ← sound2131 B hB hF]
  change (1418945220960583680000 : ℝ) * mixedMoment B node2131 node2131Labels =
    (37623398400 : ℝ) * ((37714435200 : ℝ) * mixedMoment B node2131 node2131Labels + 0)
  ring

theorem reducedTermEval793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm793 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm793 (originalVector B) := by
  rw [reducedTermArithmetic793, ← sound2132 B hB hF]
  change (-1418945220960583680000 : ℝ) * mixedMoment B node2132 node2132Labels =
    (37623398400 : ℝ) * (((-37714435200 : ℤ) : ℝ) * mixedMoment B node2132 node2132Labels + 0)
  ring

theorem reducedTermEval794 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm794 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm794 (originalVector B) := by
  rw [reducedTermArithmetic794, ← sound2133 B hB hF]
  change (11767743613933977600000 : ℝ) * mixedMoment B node2133 node2133Labels =
    (37623398400 : ℝ) * ((312777264000 : ℝ) * mixedMoment B node2133 node2133Labels + 0)
  ring

theorem reducedTermEval795 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm795 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm795 (originalVector B) := by
  rw [reducedTermArithmetic795, ← sound2134 B hB hF]
  change (4056479869678387200000 : ℝ) * mixedMoment B node2134 node2134Labels =
    (37623398400 : ℝ) * ((107818008000 : ℝ) * mixedMoment B node2134 node2134Labels + 0)
  ring

theorem reducedTermEval796 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm796 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm796 (originalVector B) := by
  rw [reducedTermArithmetic796, ← sound2136 B hB hF]
  change (-40767630952366080000 : ℝ) * mixedMoment B node2136 node2136Labels =
    (37623398400 : ℝ) * (((-1083571200 : ℤ) : ℝ) * mixedMoment B node2136 node2136Labels + 0)
  ring

theorem reducedTermEval797 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm797 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm797 (originalVector B) := by
  rw [reducedTermArithmetic797, ← sound2138 B hB hF]
  change (8053752549762662400000 : ℝ) * mixedMoment B node2138 node2138Labels =
    (37623398400 : ℝ) * ((214062336000 : ℝ) * mixedMoment B node2138 node2138Labels + 0)
  ring

theorem reducedTermEval798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm798 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm798 (originalVector B) := by
  rw [reducedTermArithmetic798, ← sound2140 B hB hF]
  change (-1056230257065984000000 : ℝ) * mixedMoment B node2140 node2140Labels =
    (37623398400 : ℝ) * (((-28073760000 : ℤ) : ℝ) * mixedMoment B node2140 node2140Labels + 0)
  ring

theorem reducedTermEval799 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm799 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm799 (originalVector B) := by
  rw [reducedTermArithmetic799, ← sound2142 B hB hF]
  change (-1423280520010137600000 : ℝ) * mixedMoment B node2142 node2142Labels =
    (37623398400 : ℝ) * (((-37829664000 : ℤ) : ℝ) * mixedMoment B node2142 node2142Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge736 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge736 (originalVector B) := by
  rw [reducedMerge736Check, Integer.Sparse.eval_mergeBy, reducedMergeEval732 B hB hF, reducedMergeEval735 B hB hF]
  rw [originalMerge736, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval737 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge737 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge737 (originalVector B) := by
  rw [reducedMerge737Check, Integer.Sparse.eval_mergeBy, reducedTermEval741 B hB hF, reducedTermEval742 B hB hF]
  rw [originalMerge737, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval738 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge738 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge738 (originalVector B) := by
  rw [reducedMerge738Check, Integer.Sparse.eval_mergeBy, reducedTermEval743 B hB hF, reducedTermEval744 B hB hF]
  rw [originalMerge738, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval739 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge739 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge739 (originalVector B) := by
  rw [reducedMerge739Check, Integer.Sparse.eval_mergeBy, reducedMergeEval737 B hB hF, reducedMergeEval738 B hB hF]
  rw [originalMerge739, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval740 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge740 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge740 (originalVector B) := by
  rw [reducedMerge740Check, Integer.Sparse.eval_mergeBy, reducedTermEval745 B hB hF, reducedTermEval746 B hB hF]
  rw [originalMerge740, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge741 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge741 (originalVector B) := by
  rw [reducedMerge741Check, Integer.Sparse.eval_mergeBy, reducedTermEval747 B hB hF, reducedTermEval748 B hB hF]
  rw [originalMerge741, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge742 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge742 (originalVector B) := by
  rw [reducedMerge742Check, Integer.Sparse.eval_mergeBy, reducedMergeEval740 B hB hF, reducedMergeEval741 B hB hF]
  rw [originalMerge742, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval743 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge743 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge743 (originalVector B) := by
  rw [reducedMerge743Check, Integer.Sparse.eval_mergeBy, reducedMergeEval739 B hB hF, reducedMergeEval742 B hB hF]
  rw [originalMerge743, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval744 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge744 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge744 (originalVector B) := by
  rw [reducedMerge744Check, Integer.Sparse.eval_mergeBy, reducedMergeEval736 B hB hF, reducedMergeEval743 B hB hF]
  rw [originalMerge744, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge745 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge745 (originalVector B) := by
  rw [reducedMerge745Check, Integer.Sparse.eval_mergeBy, reducedMergeEval730 B hB hF, reducedMergeEval744 B hB hF]
  rw [originalMerge745, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge746 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge746 (originalVector B) := by
  rw [reducedMerge746Check, Integer.Sparse.eval_mergeBy, reducedTermEval750 B hB hF, reducedTermEval751 B hB hF]
  rw [originalMerge746, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge747 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge747 (originalVector B) := by
  rw [reducedMerge747Check, Integer.Sparse.eval_mergeBy, reducedTermEval749 B hB hF, reducedMergeEval746 B hB hF]
  rw [originalMerge747, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge748 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge748 (originalVector B) := by
  rw [reducedMerge748Check, Integer.Sparse.eval_mergeBy, reducedTermEval752 B hB hF, reducedTermEval753 B hB hF]
  rw [originalMerge748, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval749 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge749 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge749 (originalVector B) := by
  rw [reducedMerge749Check, Integer.Sparse.eval_mergeBy, reducedTermEval754 B hB hF, reducedTermEval755 B hB hF]
  rw [originalMerge749, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval750 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge750 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge750 (originalVector B) := by
  rw [reducedMerge750Check, Integer.Sparse.eval_mergeBy, reducedMergeEval748 B hB hF, reducedMergeEval749 B hB hF]
  rw [originalMerge750, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval751 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge751 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge751 (originalVector B) := by
  rw [reducedMerge751Check, Integer.Sparse.eval_mergeBy, reducedMergeEval747 B hB hF, reducedMergeEval750 B hB hF]
  rw [originalMerge751, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge752 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge752 (originalVector B) := by
  rw [reducedMerge752Check, Integer.Sparse.eval_mergeBy, reducedTermEval756 B hB hF, reducedTermEval757 B hB hF]
  rw [originalMerge752, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge753 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge753 (originalVector B) := by
  rw [reducedMerge753Check, Integer.Sparse.eval_mergeBy, reducedTermEval758 B hB hF, reducedTermEval759 B hB hF]
  rw [originalMerge753, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge754 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge754 (originalVector B) := by
  rw [reducedMerge754Check, Integer.Sparse.eval_mergeBy, reducedMergeEval752 B hB hF, reducedMergeEval753 B hB hF]
  rw [originalMerge754, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge755 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge755 (originalVector B) := by
  rw [reducedMerge755Check, Integer.Sparse.eval_mergeBy, reducedTermEval760 B hB hF, reducedTermEval761 B hB hF]
  rw [originalMerge755, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge756 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge756 (originalVector B) := by
  rw [reducedMerge756Check, Integer.Sparse.eval_mergeBy, reducedTermEval762 B hB hF, reducedTermEval763 B hB hF]
  rw [originalMerge756, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge757 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge757 (originalVector B) := by
  rw [reducedMerge757Check, Integer.Sparse.eval_mergeBy, reducedMergeEval755 B hB hF, reducedMergeEval756 B hB hF]
  rw [originalMerge757, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge758 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge758 (originalVector B) := by
  rw [reducedMerge758Check, Integer.Sparse.eval_mergeBy, reducedMergeEval754 B hB hF, reducedMergeEval757 B hB hF]
  rw [originalMerge758, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge759 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge759 (originalVector B) := by
  rw [reducedMerge759Check, Integer.Sparse.eval_mergeBy, reducedMergeEval751 B hB hF, reducedMergeEval758 B hB hF]
  rw [originalMerge759, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge760 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge760 (originalVector B) := by
  rw [reducedMerge760Check, Integer.Sparse.eval_mergeBy, reducedTermEval765 B hB hF, reducedTermEval766 B hB hF]
  rw [originalMerge760, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge761 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge761 (originalVector B) := by
  rw [reducedMerge761Check, Integer.Sparse.eval_mergeBy, reducedTermEval764 B hB hF, reducedMergeEval760 B hB hF]
  rw [originalMerge761, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge762 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge762 (originalVector B) := by
  rw [reducedMerge762Check, Integer.Sparse.eval_mergeBy, reducedTermEval767 B hB hF, reducedTermEval768 B hB hF]
  rw [originalMerge762, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge763 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge763 (originalVector B) := by
  rw [reducedMerge763Check, Integer.Sparse.eval_mergeBy, reducedTermEval769 B hB hF, reducedTermEval770 B hB hF]
  rw [originalMerge763, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge764 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge764 (originalVector B) := by
  rw [reducedMerge764Check, Integer.Sparse.eval_mergeBy, reducedMergeEval762 B hB hF, reducedMergeEval763 B hB hF]
  rw [originalMerge764, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge765 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge765 (originalVector B) := by
  rw [reducedMerge765Check, Integer.Sparse.eval_mergeBy, reducedMergeEval761 B hB hF, reducedMergeEval764 B hB hF]
  rw [originalMerge765, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge766 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge766 (originalVector B) := by
  rw [reducedMerge766Check, Integer.Sparse.eval_mergeBy, reducedTermEval771 B hB hF, reducedTermEval772 B hB hF]
  rw [originalMerge766, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge767 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge767 (originalVector B) := by
  rw [reducedMerge767Check, Integer.Sparse.eval_mergeBy, reducedTermEval773 B hB hF, reducedTermEval774 B hB hF]
  rw [originalMerge767, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm800 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm800 (originalVector B) := by
  rw [reducedTermArithmetic800, ← sound2144 B hB hF]
  change (1234719933093642240000 : ℝ) * mixedMoment B node2144 node2144Labels =
    (37623398400 : ℝ) * ((32817873600 : ℝ) * mixedMoment B node2144 node2144Labels + 0)
  ring

theorem reducedTermEval801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm801 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm801 (originalVector B) := by
  rw [reducedTermArithmetic801, ← sound2145 B hB hF]
  change (747433945254592512000 : ℝ) * mixedMoment B node2145 node2145Labels =
    (37623398400 : ℝ) * ((19866199680 : ℝ) * mixedMoment B node2145 node2145Labels + 0)
  ring

theorem reducedTermEval802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm802 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm802 (originalVector B) := by
  rw [reducedTermArithmetic802, ← sound2146 B hB hF]
  change (-1041522169018318848000 : ℝ) * mixedMoment B node2146 node2146Labels =
    (37623398400 : ℝ) * (((-27682830720 : ℤ) : ℝ) * mixedMoment B node2146 node2146Labels + 0)
  ring

theorem reducedTermEval803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm803 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm803 (originalVector B) := by
  rw [reducedTermArithmetic803, ← sound2147 B hB hF]
  change (-1400262241941061632000 : ℝ) * mixedMoment B node2147 node2147Labels =
    (37623398400 : ℝ) * (((-37217856480 : ℤ) : ℝ) * mixedMoment B node2147 node2147Labels + 0)
  ring

theorem reducedTermEval804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm804 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm804 (originalVector B) := by
  rw [reducedTermArithmetic804, ← sound2148 B hB hF]
  change (-1951341470849433600000 : ℝ) * mixedMoment B node2148 node2148Labels =
    (37623398400 : ℝ) * (((-51865104000 : ℤ) : ℝ) * mixedMoment B node2148 node2148Labels + 0)
  ring

theorem reducedTermEval805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm805 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm805 (originalVector B) := by
  rw [reducedTermArithmetic805, ← sound2149 B hB hF]
  change (-3528479019960631296000 : ℝ) * mixedMoment B node2149 node2149Labels =
    (37623398400 : ℝ) * (((-93784165440 : ℤ) : ℝ) * mixedMoment B node2149 node2149Labels + 0)
  ring

theorem reducedTermEval806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm806 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm806 (originalVector B) := by
  rw [reducedTermArithmetic806, ← sound2153 B hB hF]
  change (-5084299705354813440000 : ℝ) * mixedMoment B node2153 node2153Labels =
    (37623398400 : ℝ) * (((-135136641600 : ℤ) : ℝ) * mixedMoment B node2153 node2153Labels + 0)
  ring

theorem reducedTermEval807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm807 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm807 (originalVector B) := by
  rw [reducedTermArithmetic807, ← sound2154 B hB hF]
  change (415726753622261760000 : ℝ) * mixedMoment B node2154 node2154Labels =
    (37623398400 : ℝ) * ((11049686400 : ℝ) * mixedMoment B node2154 node2154Labels + 0)
  ring

theorem reducedTermEval808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm808 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm808 (originalVector B) := by
  rw [reducedTermArithmetic808, ← sound2155 B hB hF]
  change (-199802494476877824000 : ℝ) * mixedMoment B node2155 node2155Labels =
    (37623398400 : ℝ) * (((-5310591360 : ℤ) : ℝ) * mixedMoment B node2155 node2155Labels + 0)
  ring

theorem reducedTermEval809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm809 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm809 (originalVector B) := by
  rw [reducedTermArithmetic809, ← sound2158 B hB hF]
  change (-1958086160293036032000 : ℝ) * mixedMoment B node2158 node2158Labels =
    (37623398400 : ℝ) * (((-52044372480 : ℤ) : ℝ) * mixedMoment B node2158 node2158Labels + 0)
  ring

theorem reducedTermEval810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm810 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm810 (originalVector B) := by
  rw [reducedTermArithmetic810, ← sound2160 B hB hF]
  change (350247195718189056000 : ℝ) * mixedMoment B node2160 node2160Labels =
    (37623398400 : ℝ) * ((9309291840 : ℝ) * mixedMoment B node2160 node2160Labels + 0)
  ring

theorem reducedTermEval811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm811 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm811 (originalVector B) := by
  rw [reducedTermArithmetic811, ← sound2161 B hB hF]
  change (460809475344433152000 : ℝ) * mixedMoment B node2161 node2161Labels =
    (37623398400 : ℝ) * ((12247949280 : ℝ) * mixedMoment B node2161 node2161Labels + 0)
  ring

theorem reducedTermEval812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm812 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm812 (originalVector B) := by
  rw [reducedTermArithmetic812, ← sound2162 B hB hF]
  change (1082771078483017728000 : ℝ) * mixedMoment B node2162 node2162Labels =
    (37623398400 : ℝ) * ((28779193920 : ℝ) * mixedMoment B node2162 node2162Labels + 0)
  ring

theorem reducedTermEval813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm813 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm813 (originalVector B) := by
  rw [reducedTermArithmetic813, ← sound2163 B hB hF]
  change (104801980817866752000 : ℝ) * mixedMoment B node2163 node2163Labels =
    (37623398400 : ℝ) * ((2785553280 : ℝ) * mixedMoment B node2163 node2163Labels + 0)
  ring

theorem reducedTermEval814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm814 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm814 (originalVector B) := by
  rw [reducedTermArithmetic814, ← sound2164 B hB hF]
  change (-4082980870490554368000 : ℝ) * mixedMoment B node2164 node2164Labels =
    (37623398400 : ℝ) * (((-108522383520 : ℤ) : ℝ) * mixedMoment B node2164 node2164Labels + 0)
  ring

theorem reducedTermEval815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm815 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm815 (originalVector B) := by
  rw [reducedTermArithmetic815, ← sound2171 B hB hF]
  change (-888215115745198080000 : ℝ) * mixedMoment B node2171 node2171Labels =
    (37623398400 : ℝ) * (((-23608051200 : ℤ) : ℝ) * mixedMoment B node2171 node2171Labels + 0)
  ring

theorem reducedTermEval816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm816 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm816 (originalVector B) := by
  rw [reducedTermArithmetic816, ← sound2172 B hB hF]
  change (-1086333153488142336000 : ℝ) * mixedMoment B node2172 node2172Labels =
    (37623398400 : ℝ) * (((-28873871040 : ℤ) : ℝ) * mixedMoment B node2172 node2172Labels + 0)
  ring

theorem reducedTermEval817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm817 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm817 (originalVector B) := by
  rw [reducedTermArithmetic817, ← sound2175 B hB hF]
  change (-2488877088999211008000 : ℝ) * mixedMoment B node2175 node2175Labels =
    (37623398400 : ℝ) * (((-66152373120 : ℤ) : ℝ) * mixedMoment B node2175 node2175Labels + 0)
  ring

theorem reducedTermEval818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm818 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm818 (originalVector B) := by
  rw [reducedTermArithmetic818, ← sound2176 B hB hF]
  change (-1039334509865336832000 : ℝ) * mixedMoment B node2176 node2176Labels =
    (37623398400 : ℝ) * (((-27624684480 : ℤ) : ℝ) * mixedMoment B node2176 node2176Labels + 0)
  ring

theorem reducedTermEval819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm819 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm819 (originalVector B) := by
  rw [reducedTermArithmetic819, ← sound2178 B hB hF]
  change (-2644281324676841472000 : ℝ) * mixedMoment B node2178 node2178Labels =
    (37623398400 : ℝ) * (((-70282894080 : ℤ) : ℝ) * mixedMoment B node2178 node2178Labels + 0)
  ring

theorem reducedTermEval820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm820 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm820 (originalVector B) := by
  rw [reducedTermArithmetic820, ← sound2179 B hB hF]
  change (382802499623190528000 : ℝ) * mixedMoment B node2179 node2179Labels =
    (37623398400 : ℝ) * ((10174585920 : ℝ) * mixedMoment B node2179 node2179Labels + 0)
  ring

theorem reducedTermEval821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm821 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm821 (originalVector B) := by
  rw [reducedTermArithmetic821, ← sound2180 B hB hF]
  change (80987525421465600000 : ℝ) * mixedMoment B node2180 node2180Labels =
    (37623398400 : ℝ) * ((2152584000 : ℝ) * mixedMoment B node2180 node2180Labels + 0)
  ring

theorem reducedTermEval822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm822 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm822 (originalVector B) := by
  rw [reducedTermArithmetic822, ← sound2181 B hB hF]
  change (-2480383209507323904000 : ℝ) * mixedMoment B node2181 node2181Labels =
    (37623398400 : ℝ) * (((-65926612560 : ℤ) : ℝ) * mixedMoment B node2181 node2181Labels + 0)
  ring

theorem reducedTermEval823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm823 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm823 (originalVector B) := by
  rw [reducedTermArithmetic823, ← sound2187 B hB hF]
  change (1069052130648391680000 : ℝ) * mixedMoment B node2187 node2187Labels =
    (37623398400 : ℝ) * ((28414555200 : ℝ) * mixedMoment B node2187 node2187Labels + 0)
  ring

theorem reducedTermEval824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm824 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm824 (originalVector B) := by
  rw [reducedTermArithmetic824, ← sound2189 B hB hF]
  change (-535625493262368768000 : ℝ) * mixedMoment B node2189 node2189Labels =
    (37623398400 : ℝ) * (((-14236499520 : ℤ) : ℝ) * mixedMoment B node2189 node2189Labels + 0)
  ring

theorem reducedTermEval825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm825 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm825 (originalVector B) := by
  rw [reducedTermArithmetic825, ← sound2192 B hB hF]
  change (2550756900341809152000 : ℝ) * mixedMoment B node2192 node2192Labels =
    (37623398400 : ℝ) * ((67797089280 : ℝ) * mixedMoment B node2192 node2192Labels + 0)
  ring

theorem reducedTermEval826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm826 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm826 (originalVector B) := by
  rw [reducedTermArithmetic826, ← sound2194 B hB hF]
  change (506714469983059968000 : ℝ) * mixedMoment B node2194 node2194Labels =
    (37623398400 : ℝ) * ((13468067520 : ℝ) * mixedMoment B node2194 node2194Labels + 0)
  ring

theorem reducedTermEval827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm827 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm827 (originalVector B) := by
  rw [reducedTermArithmetic827, ← sound2195 B hB hF]
  change (2281683348482162688000 : ℝ) * mixedMoment B node2195 node2195Labels =
    (37623398400 : ℝ) * ((60645328320 : ℝ) * mixedMoment B node2195 node2195Labels + 0)
  ring

theorem reducedTermEval828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm828 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm828 (originalVector B) := by
  rw [reducedTermArithmetic828, ← sound2196 B hB hF]
  change (4171042250963288064000 : ℝ) * mixedMoment B node2196 node2196Labels =
    (37623398400 : ℝ) * ((110862984960 : ℝ) * mixedMoment B node2196 node2196Labels + 0)
  ring

theorem reducedTermEval829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm829 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm829 (originalVector B) := by
  rw [reducedTermArithmetic829, ← sound2197 B hB hF]
  change (3716334068831354880000 : ℝ) * mixedMoment B node2197 node2197Labels =
    (37623398400 : ℝ) * ((98777203200 : ℝ) * mixedMoment B node2197 node2197Labels + 0)
  ring

theorem reducedTermEval830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm830 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm830 (originalVector B) := by
  rw [reducedTermArithmetic830, ← sound2198 B hB hF]
  change (-1758049717505163264000 : ℝ) * mixedMoment B node2198 node2198Labels =
    (37623398400 : ℝ) * (((-46727562960 : ℤ) : ℝ) * mixedMoment B node2198 node2198Labels + 0)
  ring

theorem reducedTermEval831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm831 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm831 (originalVector B) := by
  rw [reducedTermArithmetic831, ← sound2199 B hB hF]
  change (-529608735311265792000 : ℝ) * mixedMoment B node2199 node2199Labels =
    (37623398400 : ℝ) * (((-14076578880 : ℤ) : ℝ) * mixedMoment B node2199 node2199Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge768 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge768 (originalVector B) := by
  rw [reducedMerge768Check, Integer.Sparse.eval_mergeBy, reducedMergeEval766 B hB hF, reducedMergeEval767 B hB hF]
  rw [originalMerge768, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge769 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge769 (originalVector B) := by
  rw [reducedMerge769Check, Integer.Sparse.eval_mergeBy, reducedTermEval775 B hB hF, reducedTermEval776 B hB hF]
  rw [originalMerge769, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge770 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge770 (originalVector B) := by
  rw [reducedMerge770Check, Integer.Sparse.eval_mergeBy, reducedTermEval777 B hB hF, reducedTermEval778 B hB hF]
  rw [originalMerge770, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge771 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge771 (originalVector B) := by
  rw [reducedMerge771Check, Integer.Sparse.eval_mergeBy, reducedMergeEval769 B hB hF, reducedMergeEval770 B hB hF]
  rw [originalMerge771, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge772 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge772 (originalVector B) := by
  rw [reducedMerge772Check, Integer.Sparse.eval_mergeBy, reducedMergeEval768 B hB hF, reducedMergeEval771 B hB hF]
  rw [originalMerge772, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge773 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge773 (originalVector B) := by
  rw [reducedMerge773Check, Integer.Sparse.eval_mergeBy, reducedMergeEval765 B hB hF, reducedMergeEval772 B hB hF]
  rw [originalMerge773, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge774 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge774 (originalVector B) := by
  rw [reducedMerge774Check, Integer.Sparse.eval_mergeBy, reducedMergeEval759 B hB hF, reducedMergeEval773 B hB hF]
  rw [originalMerge774, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge775 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge775 (originalVector B) := by
  rw [reducedMerge775Check, Integer.Sparse.eval_mergeBy, reducedMergeEval745 B hB hF, reducedMergeEval774 B hB hF]
  rw [originalMerge775, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge776 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge776 (originalVector B) := by
  rw [reducedMerge776Check, Integer.Sparse.eval_mergeBy, reducedTermEval780 B hB hF, reducedTermEval781 B hB hF]
  rw [originalMerge776, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge777 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge777 (originalVector B) := by
  rw [reducedMerge777Check, Integer.Sparse.eval_mergeBy, reducedTermEval779 B hB hF, reducedMergeEval776 B hB hF]
  rw [originalMerge777, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge778 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge778 (originalVector B) := by
  rw [reducedMerge778Check, Integer.Sparse.eval_mergeBy, reducedTermEval782 B hB hF, reducedTermEval783 B hB hF]
  rw [originalMerge778, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge779 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge779 (originalVector B) := by
  rw [reducedMerge779Check, Integer.Sparse.eval_mergeBy, reducedTermEval784 B hB hF, reducedTermEval785 B hB hF]
  rw [originalMerge779, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval780 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge780 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge780 (originalVector B) := by
  rw [reducedMerge780Check, Integer.Sparse.eval_mergeBy, reducedMergeEval778 B hB hF, reducedMergeEval779 B hB hF]
  rw [originalMerge780, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge781 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge781 (originalVector B) := by
  rw [reducedMerge781Check, Integer.Sparse.eval_mergeBy, reducedMergeEval777 B hB hF, reducedMergeEval780 B hB hF]
  rw [originalMerge781, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge782 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge782 (originalVector B) := by
  rw [reducedMerge782Check, Integer.Sparse.eval_mergeBy, reducedTermEval786 B hB hF, reducedTermEval787 B hB hF]
  rw [originalMerge782, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge783 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge783 (originalVector B) := by
  rw [reducedMerge783Check, Integer.Sparse.eval_mergeBy, reducedTermEval788 B hB hF, reducedTermEval789 B hB hF]
  rw [originalMerge783, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval784 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge784 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge784 (originalVector B) := by
  rw [reducedMerge784Check, Integer.Sparse.eval_mergeBy, reducedMergeEval782 B hB hF, reducedMergeEval783 B hB hF]
  rw [originalMerge784, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval785 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge785 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge785 (originalVector B) := by
  rw [reducedMerge785Check, Integer.Sparse.eval_mergeBy, reducedTermEval790 B hB hF, reducedTermEval791 B hB hF]
  rw [originalMerge785, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval786 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge786 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge786 (originalVector B) := by
  rw [reducedMerge786Check, Integer.Sparse.eval_mergeBy, reducedTermEval792 B hB hF, reducedTermEval793 B hB hF]
  rw [originalMerge786, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval787 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge787 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge787 (originalVector B) := by
  rw [reducedMerge787Check, Integer.Sparse.eval_mergeBy, reducedMergeEval785 B hB hF, reducedMergeEval786 B hB hF]
  rw [originalMerge787, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval788 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge788 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge788 (originalVector B) := by
  rw [reducedMerge788Check, Integer.Sparse.eval_mergeBy, reducedMergeEval784 B hB hF, reducedMergeEval787 B hB hF]
  rw [originalMerge788, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval789 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge789 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge789 (originalVector B) := by
  rw [reducedMerge789Check, Integer.Sparse.eval_mergeBy, reducedMergeEval781 B hB hF, reducedMergeEval788 B hB hF]
  rw [originalMerge789, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge790 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge790 (originalVector B) := by
  rw [reducedMerge790Check, Integer.Sparse.eval_mergeBy, reducedTermEval795 B hB hF, reducedTermEval796 B hB hF]
  rw [originalMerge790, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval791 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge791 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge791 (originalVector B) := by
  rw [reducedMerge791Check, Integer.Sparse.eval_mergeBy, reducedTermEval794 B hB hF, reducedMergeEval790 B hB hF]
  rw [originalMerge791, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval792 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge792 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge792 (originalVector B) := by
  rw [reducedMerge792Check, Integer.Sparse.eval_mergeBy, reducedTermEval797 B hB hF, reducedTermEval798 B hB hF]
  rw [originalMerge792, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge793 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge793 (originalVector B) := by
  rw [reducedMerge793Check, Integer.Sparse.eval_mergeBy, reducedTermEval799 B hB hF, reducedTermEval800 B hB hF]
  rw [originalMerge793, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval794 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge794 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge794 (originalVector B) := by
  rw [reducedMerge794Check, Integer.Sparse.eval_mergeBy, reducedMergeEval792 B hB hF, reducedMergeEval793 B hB hF]
  rw [originalMerge794, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval795 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge795 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge795 (originalVector B) := by
  rw [reducedMerge795Check, Integer.Sparse.eval_mergeBy, reducedMergeEval791 B hB hF, reducedMergeEval794 B hB hF]
  rw [originalMerge795, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval796 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge796 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge796 (originalVector B) := by
  rw [reducedMerge796Check, Integer.Sparse.eval_mergeBy, reducedTermEval801 B hB hF, reducedTermEval802 B hB hF]
  rw [originalMerge796, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval797 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge797 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge797 (originalVector B) := by
  rw [reducedMerge797Check, Integer.Sparse.eval_mergeBy, reducedTermEval803 B hB hF, reducedTermEval804 B hB hF]
  rw [originalMerge797, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge798 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge798 (originalVector B) := by
  rw [reducedMerge798Check, Integer.Sparse.eval_mergeBy, reducedMergeEval796 B hB hF, reducedMergeEval797 B hB hF]
  rw [originalMerge798, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval799 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge799 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge799 (originalVector B) := by
  rw [reducedMerge799Check, Integer.Sparse.eval_mergeBy, reducedTermEval805 B hB hF, reducedTermEval806 B hB hF]
  rw [originalMerge799, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm832 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm832 (originalVector B) := by
  rw [reducedTermArithmetic832, ← sound2200 B hB hF]
  change (-2923000637003661312000 : ℝ) * mixedMoment B node2200 node2200Labels =
    (37623398400 : ℝ) * (((-77691031680 : ℤ) : ℝ) * mixedMoment B node2200 node2200Labels + 0)
  ring

theorem reducedTermEval833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm833 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm833 (originalVector B) := by
  rw [reducedTermArithmetic833, ← sound2201 B hB hF]
  change (-968581412641898496000 : ℝ) * mixedMoment B node2201 node2201Labels =
    (37623398400 : ℝ) * (((-25744123440 : ℤ) : ℝ) * mixedMoment B node2201 node2201Labels + 0)
  ring

theorem reducedTermEval834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm834 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm834 (originalVector B) := by
  rw [reducedTermArithmetic834, ← sound2207 B hB hF]
  change (-1075562447389065216000 : ℝ) * mixedMoment B node2207 node2207Labels =
    (37623398400 : ℝ) * (((-28587594240 : ℤ) : ℝ) * mixedMoment B node2207 node2207Labels + 0)
  ring

theorem reducedTermEval835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm835 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm835 (originalVector B) := by
  rw [reducedTermArithmetic835, ← sound2211 B hB hF]
  change (3118020017674125312000 : ℝ) * mixedMoment B node2211 node2211Labels =
    (37623398400 : ℝ) * ((82874491680 : ℝ) * mixedMoment B node2211 node2211Labels + 0)
  ring

theorem reducedTermEval836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm836 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm836 (originalVector B) := by
  rw [reducedTermArithmetic836, ← sound2212 B hB hF]
  change (3417517613264928768000 : ℝ) * mixedMoment B node2212 node2212Labels =
    (37623398400 : ℝ) * ((90834899520 : ℝ) * mixedMoment B node2212 node2212Labels + 0)
  ring

theorem reducedTermEval837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm837 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm837 (originalVector B) := by
  rw [reducedTermArithmetic837, ← sound2213 B hB hF]
  change (-164392035143712768000 : ℝ) * mixedMoment B node2213 node2213Labels =
    (37623398400 : ℝ) * (((-4369409520 : ℤ) : ℝ) * mixedMoment B node2213 node2213Labels + 0)
  ring

theorem reducedTermEval838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm838 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm838 (originalVector B) := by
  rw [reducedTermArithmetic838, ← sound2217 B hB hF]
  change (6106405275203272704000 : ℝ) * mixedMoment B node2217 node2217Labels =
    (37623398400 : ℝ) * ((162303394560 : ℝ) * mixedMoment B node2217 node2217Labels + 0)
  ring

theorem reducedTermEval839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm839 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm839 (originalVector B) := by
  rw [reducedTermArithmetic839, ← sound2219 B hB hF]
  change (543996082382635008000 : ℝ) * mixedMoment B node2219 node2219Labels =
    (37623398400 : ℝ) * ((14458983120 : ℝ) * mixedMoment B node2219 node2219Labels + 0)
  ring

theorem reducedTermEval840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm840 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm840 (originalVector B) := by
  rw [reducedTermArithmetic840, ← sound2220 B hB hF]
  change (1698881328169353216000 : ℝ) * mixedMoment B node2220 node2220Labels =
    (37623398400 : ℝ) * ((45154914240 : ℝ) * mixedMoment B node2220 node2220Labels + 0)
  ring

theorem reducedTermEval841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm841 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm841 (originalVector B) := by
  rw [reducedTermArithmetic841, ← sound2221 B hB hF]
  change (-2422443967567626240000 : ℝ) * mixedMoment B node2221 node2221Labels =
    (37623398400 : ℝ) * (((-64386633600 : ℤ) : ℝ) * mixedMoment B node2221 node2221Labels + 0)
  ring

theorem reducedTermEval842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm842 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm842 (originalVector B) := by
  rw [reducedTermArithmetic842, ← sound2222 B hB hF]
  change (-2652931479726194688000 : ℝ) * mixedMoment B node2222 node2222Labels =
    (37623398400 : ℝ) * (((-70512808320 : ℤ) : ℝ) * mixedMoment B node2222 node2222Labels + 0)
  ring

theorem reducedTermEval843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm843 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm843 (originalVector B) := by
  rw [reducedTermArithmetic843, ← sound2223 B hB hF]
  change (454996272018161664000 : ℝ) * mixedMoment B node2223 node2223Labels =
    (37623398400 : ℝ) * ((12093438960 : ℝ) * mixedMoment B node2223 node2223Labels + 0)
  ring

theorem reducedTermEval844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm844 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm844 (originalVector B) := by
  rw [reducedTermArithmetic844, ← sound2231 B hB hF]
  change (522094469787942912000 : ℝ) * mixedMoment B node2231 node2231Labels =
    (37623398400 : ℝ) * ((13876855680 : ℝ) * mixedMoment B node2231 node2231Labels + 0)
  ring

theorem reducedTermEval845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm845 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm845 (originalVector B) := by
  rw [reducedTermArithmetic845, ← sound2232 B hB hF]
  change (825412766634344448000 : ℝ) * mixedMoment B node2232 node2232Labels =
    (37623398400 : ℝ) * ((21938814720 : ℝ) * mixedMoment B node2232 node2232Labels + 0)
  ring

theorem reducedTermEval846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm846 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm846 (originalVector B) := by
  rw [reducedTermArithmetic846, ← sound2233 B hB hF]
  change (-7143996310767009792000 : ℝ) * mixedMoment B node2233 node2233Labels =
    (37623398400 : ℝ) * (((-189881738880 : ℤ) : ℝ) * mixedMoment B node2233 node2233Labels + 0)
  ring

theorem reducedTermEval847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm847 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm847 (originalVector B) := by
  rw [reducedTermArithmetic847, ← sound2234 B hB hF]
  change (5281412168984297472000 : ℝ) * mixedMoment B node2234 node2234Labels =
    (37623398400 : ℝ) * ((140375734080 : ℝ) * mixedMoment B node2234 node2234Labels + 0)
  ring

theorem reducedTermEval848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm848 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm848 (originalVector B) := by
  rw [reducedTermArithmetic848, ← sound2235 B hB hF]
  change (8991466736109355008000 : ℝ) * mixedMoment B node2235 node2235Labels =
    (37623398400 : ℝ) * ((238986033120 : ℝ) * mixedMoment B node2235 node2235Labels + 0)
  ring

theorem reducedTermEval849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm849 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm849 (originalVector B) := by
  rw [reducedTermArithmetic849, ← sound2238 B hB hF]
  change (1167171979199643648000 : ℝ) * mixedMoment B node2238 node2238Labels =
    (37623398400 : ℝ) * ((31022502720 : ℝ) * mixedMoment B node2238 node2238Labels + 0)
  ring

theorem reducedTermEval850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm850 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm850 (originalVector B) := by
  rw [reducedTermArithmetic850, ← sound2239 B hB hF]
  change (-11939427307487232000 : ℝ) * mixedMoment B node2239 node2239Labels =
    (37623398400 : ℝ) * (((-317340480 : ℤ) : ℝ) * mixedMoment B node2239 node2239Labels + 0)
  ring

theorem reducedTermEval851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm851 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm851 (originalVector B) := by
  rw [reducedTermArithmetic851, ← sound2240 B hB hF]
  change (-912884097845035008000 : ℝ) * mixedMoment B node2240 node2240Labels =
    (37623398400 : ℝ) * (((-24263733120 : ℤ) : ℝ) * mixedMoment B node2240 node2240Labels + 0)
  ring

theorem reducedTermEval852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm852 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm852 (originalVector B) := by
  rw [reducedTermArithmetic852, ← sound2243 B hB hF]
  change (-3530220507746795520000 : ℝ) * mixedMoment B node2243 node2243Labels =
    (37623398400 : ℝ) * (((-93830452800 : ℤ) : ℝ) * mixedMoment B node2243 node2243Labels + 0)
  ring

theorem reducedTermEval853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm853 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm853 (originalVector B) := by
  rw [reducedTermArithmetic853, ← sound2244 B hB hF]
  change (-13288538835716014080000 : ℝ) * mixedMoment B node2244 node2244Labels =
    (37623398400 : ℝ) * (((-353198791200 : ℤ) : ℝ) * mixedMoment B node2244 node2244Labels + 0)
  ring

theorem reducedTermEval854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm854 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm854 (originalVector B) := by
  rw [reducedTermArithmetic854, ← sound2245 B hB hF]
  change (5084282729677455360000 : ℝ) * mixedMoment B node2245 node2245Labels =
    (37623398400 : ℝ) * ((135136190400 : ℝ) * mixedMoment B node2245 node2245Labels + 0)
  ring

theorem reducedTermEval855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm855 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm855 (originalVector B) := by
  rw [reducedTermArithmetic855, ← sound2246 B hB hF]
  change (14561556817950277632000 : ℝ) * mixedMoment B node2246 node2246Labels =
    (37623398400 : ℝ) * ((387034596480 : ℝ) * mixedMoment B node2246 node2246Labels + 0)
  ring

theorem reducedTermEval856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm856 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm856 (originalVector B) := by
  rw [reducedTermArithmetic856, ← sound2247 B hB hF]
  change (-12514908548880138240000 : ℝ) * mixedMoment B node2247 node2247Labels =
    (37623398400 : ℝ) * (((-332636313600 : ℤ) : ℝ) * mixedMoment B node2247 node2247Labels + 0)
  ring

theorem reducedTermEval857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm857 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm857 (originalVector B) := by
  rw [reducedTermArithmetic857, ← sound2248 B hB hF]
  change (-2840232254671945728000 : ℝ) * mixedMoment B node2248 node2248Labels =
    (37623398400 : ℝ) * (((-75491113920 : ℤ) : ℝ) * mixedMoment B node2248 node2248Labels + 0)
  ring

theorem reducedTermEval858 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm858 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm858 (originalVector B) := by
  rw [reducedTermArithmetic858, ← sound2249 B hB hF]
  change (-2254308298937597952000 : ℝ) * mixedMoment B node2249 node2249Labels =
    (37623398400 : ℝ) * (((-59917721280 : ℤ) : ℝ) * mixedMoment B node2249 node2249Labels + 0)
  ring

theorem reducedTermEval859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm859 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm859 (originalVector B) := by
  rw [reducedTermArithmetic859, ← sound2250 B hB hF]
  change (6385220328544468992000 : ℝ) * mixedMoment B node2250 node2250Labels =
    (37623398400 : ℝ) * ((169714076880 : ℝ) * mixedMoment B node2250 node2250Labels + 0)
  ring

theorem reducedTermEval860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm860 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm860 (originalVector B) := by
  rw [reducedTermArithmetic860, ← sound2251 B hB hF]
  change (6295106507412602880000 : ℝ) * mixedMoment B node2251 node2251Labels =
    (37623398400 : ℝ) * ((167318923200 : ℝ) * mixedMoment B node2251 node2251Labels + 0)
  ring

theorem reducedTermEval861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm861 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm861 (originalVector B) := by
  rw [reducedTermArithmetic861, ← sound2252 B hB hF]
  change (-1717100482923528192000 : ℝ) * mixedMoment B node2252 node2252Labels =
    (37623398400 : ℝ) * (((-45639164880 : ℤ) : ℝ) * mixedMoment B node2252 node2252Labels + 0)
  ring

theorem reducedTermEval862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm862 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm862 (originalVector B) := by
  rw [reducedTermArithmetic862, ← sound2253 B hB hF]
  change (-11806284324964663296000 : ℝ) * mixedMoment B node2253 node2253Labels =
    (37623398400 : ℝ) * (((-313801645440 : ℤ) : ℝ) * mixedMoment B node2253 node2253Labels + 0)
  ring

theorem reducedTermEval863 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm863 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm863 (originalVector B) := by
  rw [reducedTermArithmetic863, ← sound2254 B hB hF]
  change (3977835312798498816000 : ℝ) * mixedMoment B node2254 node2254Labels =
    (37623398400 : ℝ) * ((105727698240 : ℝ) * mixedMoment B node2254 node2254Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge800 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge800 (originalVector B) := by
  rw [reducedMerge800Check, Integer.Sparse.eval_mergeBy, reducedTermEval807 B hB hF, reducedTermEval808 B hB hF]
  rw [originalMerge800, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge801 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge801 (originalVector B) := by
  rw [reducedMerge801Check, Integer.Sparse.eval_mergeBy, reducedMergeEval799 B hB hF, reducedMergeEval800 B hB hF]
  rw [originalMerge801, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge802 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge802 (originalVector B) := by
  rw [reducedMerge802Check, Integer.Sparse.eval_mergeBy, reducedMergeEval798 B hB hF, reducedMergeEval801 B hB hF]
  rw [originalMerge802, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge803 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge803 (originalVector B) := by
  rw [reducedMerge803Check, Integer.Sparse.eval_mergeBy, reducedMergeEval795 B hB hF, reducedMergeEval802 B hB hF]
  rw [originalMerge803, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge804 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge804 (originalVector B) := by
  rw [reducedMerge804Check, Integer.Sparse.eval_mergeBy, reducedMergeEval789 B hB hF, reducedMergeEval803 B hB hF]
  rw [originalMerge804, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge805 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge805 (originalVector B) := by
  rw [reducedMerge805Check, Integer.Sparse.eval_mergeBy, reducedTermEval810 B hB hF, reducedTermEval811 B hB hF]
  rw [originalMerge805, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge806 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge806 (originalVector B) := by
  rw [reducedMerge806Check, Integer.Sparse.eval_mergeBy, reducedTermEval809 B hB hF, reducedMergeEval805 B hB hF]
  rw [originalMerge806, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge807 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge807 (originalVector B) := by
  rw [reducedMerge807Check, Integer.Sparse.eval_mergeBy, reducedTermEval812 B hB hF, reducedTermEval813 B hB hF]
  rw [originalMerge807, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge808 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge808 (originalVector B) := by
  rw [reducedMerge808Check, Integer.Sparse.eval_mergeBy, reducedTermEval814 B hB hF, reducedTermEval815 B hB hF]
  rw [originalMerge808, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge809 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge809 (originalVector B) := by
  rw [reducedMerge809Check, Integer.Sparse.eval_mergeBy, reducedMergeEval807 B hB hF, reducedMergeEval808 B hB hF]
  rw [originalMerge809, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge810 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge810 (originalVector B) := by
  rw [reducedMerge810Check, Integer.Sparse.eval_mergeBy, reducedMergeEval806 B hB hF, reducedMergeEval809 B hB hF]
  rw [originalMerge810, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge811 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge811 (originalVector B) := by
  rw [reducedMerge811Check, Integer.Sparse.eval_mergeBy, reducedTermEval816 B hB hF, reducedTermEval817 B hB hF]
  rw [originalMerge811, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge812 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge812 (originalVector B) := by
  rw [reducedMerge812Check, Integer.Sparse.eval_mergeBy, reducedTermEval818 B hB hF, reducedTermEval819 B hB hF]
  rw [originalMerge812, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge813 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge813 (originalVector B) := by
  rw [reducedMerge813Check, Integer.Sparse.eval_mergeBy, reducedMergeEval811 B hB hF, reducedMergeEval812 B hB hF]
  rw [originalMerge813, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge814 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge814 (originalVector B) := by
  rw [reducedMerge814Check, Integer.Sparse.eval_mergeBy, reducedTermEval820 B hB hF, reducedTermEval821 B hB hF]
  rw [originalMerge814, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge815 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge815 (originalVector B) := by
  rw [reducedMerge815Check, Integer.Sparse.eval_mergeBy, reducedTermEval822 B hB hF, reducedTermEval823 B hB hF]
  rw [originalMerge815, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge816 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge816 (originalVector B) := by
  rw [reducedMerge816Check, Integer.Sparse.eval_mergeBy, reducedMergeEval814 B hB hF, reducedMergeEval815 B hB hF]
  rw [originalMerge816, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge817 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge817 (originalVector B) := by
  rw [reducedMerge817Check, Integer.Sparse.eval_mergeBy, reducedMergeEval813 B hB hF, reducedMergeEval816 B hB hF]
  rw [originalMerge817, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge818 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge818 (originalVector B) := by
  rw [reducedMerge818Check, Integer.Sparse.eval_mergeBy, reducedMergeEval810 B hB hF, reducedMergeEval817 B hB hF]
  rw [originalMerge818, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge819 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge819 (originalVector B) := by
  rw [reducedMerge819Check, Integer.Sparse.eval_mergeBy, reducedTermEval825 B hB hF, reducedTermEval826 B hB hF]
  rw [originalMerge819, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge820 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge820 (originalVector B) := by
  rw [reducedMerge820Check, Integer.Sparse.eval_mergeBy, reducedTermEval824 B hB hF, reducedMergeEval819 B hB hF]
  rw [originalMerge820, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge821 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge821 (originalVector B) := by
  rw [reducedMerge821Check, Integer.Sparse.eval_mergeBy, reducedTermEval827 B hB hF, reducedTermEval828 B hB hF]
  rw [originalMerge821, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge822 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge822 (originalVector B) := by
  rw [reducedMerge822Check, Integer.Sparse.eval_mergeBy, reducedTermEval829 B hB hF, reducedTermEval830 B hB hF]
  rw [originalMerge822, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge823 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge823 (originalVector B) := by
  rw [reducedMerge823Check, Integer.Sparse.eval_mergeBy, reducedMergeEval821 B hB hF, reducedMergeEval822 B hB hF]
  rw [originalMerge823, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge824 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge824 (originalVector B) := by
  rw [reducedMerge824Check, Integer.Sparse.eval_mergeBy, reducedMergeEval820 B hB hF, reducedMergeEval823 B hB hF]
  rw [originalMerge824, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge825 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge825 (originalVector B) := by
  rw [reducedMerge825Check, Integer.Sparse.eval_mergeBy, reducedTermEval831 B hB hF, reducedTermEval832 B hB hF]
  rw [originalMerge825, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge826 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge826 (originalVector B) := by
  rw [reducedMerge826Check, Integer.Sparse.eval_mergeBy, reducedTermEval833 B hB hF, reducedTermEval834 B hB hF]
  rw [originalMerge826, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge827 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge827 (originalVector B) := by
  rw [reducedMerge827Check, Integer.Sparse.eval_mergeBy, reducedMergeEval825 B hB hF, reducedMergeEval826 B hB hF]
  rw [originalMerge827, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge828 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge828 (originalVector B) := by
  rw [reducedMerge828Check, Integer.Sparse.eval_mergeBy, reducedTermEval835 B hB hF, reducedTermEval836 B hB hF]
  rw [originalMerge828, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge829 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge829 (originalVector B) := by
  rw [reducedMerge829Check, Integer.Sparse.eval_mergeBy, reducedTermEval837 B hB hF, reducedTermEval838 B hB hF]
  rw [originalMerge829, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge830 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge830 (originalVector B) := by
  rw [reducedMerge830Check, Integer.Sparse.eval_mergeBy, reducedMergeEval828 B hB hF, reducedMergeEval829 B hB hF]
  rw [originalMerge830, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge831 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge831 (originalVector B) := by
  rw [reducedMerge831Check, Integer.Sparse.eval_mergeBy, reducedMergeEval827 B hB hF, reducedMergeEval830 B hB hF]
  rw [originalMerge831, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval864 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm864 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm864 (originalVector B) := by
  rw [reducedTermArithmetic864, ← sound2255 B hB hF]
  change (13423761248418791424000 : ℝ) * mixedMoment B node2255 node2255Labels =
    (37623398400 : ℝ) * ((356792895360 : ℝ) * mixedMoment B node2255 node2255Labels + 0)
  ring

theorem reducedTermEval865 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm865 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm865 (originalVector B) := by
  rw [reducedTermArithmetic865, ← sound2256 B hB hF]
  change (-3060986888631877632000 : ℝ) * mixedMoment B node2256 node2256Labels =
    (37623398400 : ℝ) * (((-81358596480 : ℤ) : ℝ) * mixedMoment B node2256 node2256Labels + 0)
  ring

theorem reducedTermEval866 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm866 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm866 (originalVector B) := by
  rw [reducedTermArithmetic866, ← sound2257 B hB hF]
  change (356540332144066560000 : ℝ) * mixedMoment B node2257 node2257Labels =
    (37623398400 : ℝ) * ((9476558400 : ℝ) * mixedMoment B node2257 node2257Labels + 0)
  ring

theorem reducedTermEval867 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm867 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm867 (originalVector B) := by
  rw [reducedTermArithmetic867, ← sound2258 B hB hF]
  change (-285682392053710848000 : ℝ) * mixedMoment B node2258 node2258Labels =
    (37623398400 : ℝ) * (((-7593210720 : ℤ) : ℝ) * mixedMoment B node2258 node2258Labels + 0)
  ring

theorem reducedTermEval868 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm868 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm868 (originalVector B) := by
  rw [reducedTermArithmetic868, ← sound2259 B hB hF]
  change (-2232992392359837696000 : ℝ) * mixedMoment B node2259 node2259Labels =
    (37623398400 : ℝ) * (((-59351161440 : ℤ) : ℝ) * mixedMoment B node2259 node2259Labels + 0)
  ring

theorem reducedTermEval869 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm869 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm869 (originalVector B) := by
  rw [reducedTermArithmetic869, ← sound2262 B hB hF]
  change (4747445379992125440000 : ℝ) * mixedMoment B node2262 node2262Labels =
    (37623398400 : ℝ) * ((126183321600 : ℝ) * mixedMoment B node2262 node2262Labels + 0)
  ring

theorem reducedTermEval870 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm870 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm870 (originalVector B) := by
  rw [reducedTermArithmetic870, ← sound2263 B hB hF]
  change (-4937762046553620480000 : ℝ) * mixedMoment B node2263 node2263Labels =
    (37623398400 : ℝ) * (((-131241787200 : ℤ) : ℝ) * mixedMoment B node2263 node2263Labels + 0)
  ring

theorem reducedTermEval871 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm871 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm871 (originalVector B) := by
  rw [reducedTermArithmetic871, ← sound2264 B hB hF]
  change (-6331906344670986240000 : ℝ) * mixedMoment B node2264 node2264Labels =
    (37623398400 : ℝ) * (((-168297033600 : ℤ) : ℝ) * mixedMoment B node2264 node2264Labels + 0)
  ring

theorem reducedTermEval872 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm872 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm872 (originalVector B) := by
  rw [reducedTermArithmetic872, ← sound2265 B hB hF]
  change (25915389786791608320000 : ℝ) * mixedMoment B node2265 node2265Labels =
    (37623398400 : ℝ) * ((688810444800 : ℝ) * mixedMoment B node2265 node2265Labels + 0)
  ring

theorem reducedTermEval873 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm873 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm873 (originalVector B) := by
  rw [reducedTermArithmetic873, ← sound2266 B hB hF]
  change (-17198383075263774720000 : ℝ) * mixedMoment B node2266 node2266Labels =
    (37623398400 : ℝ) * (((-457119340800 : ℤ) : ℝ) * mixedMoment B node2266 node2266Labels + 0)
  ring

theorem reducedTermEval874 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm874 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm874 (originalVector B) := by
  rw [reducedTermArithmetic874, ← sound2267 B hB hF]
  change (2456191162674708480000 : ℝ) * mixedMoment B node2267 node2267Labels =
    (37623398400 : ℝ) * ((65283607200 : ℝ) * mixedMoment B node2267 node2267Labels + 0)
  ring

theorem reducedTermEval875 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm875 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm875 (originalVector B) := by
  rw [reducedTermArithmetic875, ← sound2268 B hB hF]
  change (-6892394631702773760000 : ℝ) * mixedMoment B node2268 node2268Labels =
    (37623398400 : ℝ) * (((-183194366400 : ℤ) : ℝ) * mixedMoment B node2268 node2268Labels + 0)
  ring

theorem reducedTermEval876 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm876 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm876 (originalVector B) := by
  rw [reducedTermArithmetic876, ← sound2272 B hB hF]
  change (620385158666649600000 : ℝ) * mixedMoment B node2272 node2272Labels =
    (37623398400 : ℝ) * ((16489344000 : ℝ) * mixedMoment B node2272 node2272Labels + 0)
  ring

theorem reducedTermEval877 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm877 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm877 (originalVector B) := by
  rw [reducedTermArithmetic877, ← sound2273 B hB hF]
  change (1530801552859987968000 : ℝ) * mixedMoment B node2273 node2273Labels =
    (37623398400 : ℝ) * ((40687487520 : ℝ) * mixedMoment B node2273 node2273Labels + 0)
  ring

theorem reducedTermEval878 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm878 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm878 (originalVector B) := by
  rw [reducedTermArithmetic878, ← sound2274 B hB hF]
  change (11930424302148452352000 : ℝ) * mixedMoment B node2274 node2274Labels =
    (37623398400 : ℝ) * ((317101187280 : ℝ) * mixedMoment B node2274 node2274Labels + 0)
  ring

theorem reducedTermEval879 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm879 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm879 (originalVector B) := by
  rw [reducedTermArithmetic879, ← sound2277 B hB hF]
  change (7044709980352020480000 : ℝ) * mixedMoment B node2277 node2277Labels =
    (37623398400 : ℝ) * ((187242787200 : ℝ) * mixedMoment B node2277 node2277Labels + 0)
  ring

theorem reducedTermEval880 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm880 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm880 (originalVector B) := by
  rw [reducedTermArithmetic880, ← sound2278 B hB hF]
  change (613475877389598720000 : ℝ) * mixedMoment B node2278 node2278Labels =
    (37623398400 : ℝ) * ((16305700800 : ℝ) * mixedMoment B node2278 node2278Labels + 0)
  ring

theorem reducedTermEval881 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm881 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm881 (originalVector B) := by
  rw [reducedTermArithmetic881, ← sound2279 B hB hF]
  change (4948572573257564160000 : ℝ) * mixedMoment B node2279 node2279Labels =
    (37623398400 : ℝ) * ((131529122400 : ℝ) * mixedMoment B node2279 node2279Labels + 0)
  ring

theorem reducedTermEval882 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm882 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm882 (originalVector B) := by
  rw [reducedTermArithmetic882, ← sound2280 B hB hF]
  change (4794515628466765824000 : ℝ) * mixedMoment B node2280 node2280Labels =
    (37623398400 : ℝ) * ((127434411360 : ℝ) * mixedMoment B node2280 node2280Labels + 0)
  ring

theorem reducedTermEval883 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm883 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm883 (originalVector B) := by
  rw [reducedTermArithmetic883, ← sound2281 B hB hF]
  change (9591223123887390720000 : ℝ) * mixedMoment B node2281 node2281Labels =
    (37623398400 : ℝ) * ((254927080800 : ℝ) * mixedMoment B node2281 node2281Labels + 0)
  ring

theorem reducedTermEval884 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm884 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm884 (originalVector B) := by
  rw [reducedTermArithmetic884, ← sound2282 B hB hF]
  change (-328449504969621504000 : ℝ) * mixedMoment B node2282 node2282Labels =
    (37623398400 : ℝ) * (((-8729926560 : ℤ) : ℝ) * mixedMoment B node2282 node2282Labels + 0)
  ring

theorem reducedTermEval885 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm885 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm885 (originalVector B) := by
  rw [reducedTermArithmetic885, ← sound2283 B hB hF]
  change (1069657792115834880000 : ℝ) * mixedMoment B node2283 node2283Labels =
    (37623398400 : ℝ) * ((28430653200 : ℝ) * mixedMoment B node2283 node2283Labels + 0)
  ring

theorem reducedTermEval886 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm886 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm886 (originalVector B) := by
  rw [reducedTermArithmetic886, ← sound2284 B hB hF]
  change (3942379037195698176000 : ℝ) * mixedMoment B node2284 node2284Labels =
    (37623398400 : ℝ) * ((104785298640 : ℝ) * mixedMoment B node2284 node2284Labels + 0)
  ring

theorem reducedTermEval887 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm887 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm887 (originalVector B) := by
  rw [reducedTermArithmetic887, ← sound2285 B hB hF]
  change (88491352709136384000 : ℝ) * mixedMoment B node2285 node2285Labels =
    (37623398400 : ℝ) * ((2352029760 : ℝ) * mixedMoment B node2285 node2285Labels + 0)
  ring

theorem reducedTermEval888 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm888 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm888 (originalVector B) := by
  rw [reducedTermArithmetic888, ← sound2286 B hB hF]
  change (1402778741635547136000 : ℝ) * mixedMoment B node2286 node2286Labels =
    (37623398400 : ℝ) * ((37284743040 : ℝ) * mixedMoment B node2286 node2286Labels + 0)
  ring

theorem reducedTermEval889 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm889 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm889 (originalVector B) := by
  rw [reducedTermArithmetic889, ← sound2291 B hB hF]
  change (-7179555731668992000000 : ℝ) * mixedMoment B node2291 node2291Labels =
    (37623398400 : ℝ) * (((-190826880000 : ℤ) : ℝ) * mixedMoment B node2291 node2291Labels + 0)
  ring

theorem reducedTermEval890 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm890 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm890 (originalVector B) := by
  rw [reducedTermArithmetic890, ← sound2293 B hB hF]
  change (-1904143670024601600000 : ℝ) * mixedMoment B node2293 node2293Labels =
    (37623398400 : ℝ) * (((-50610624000 : ℤ) : ℝ) * mixedMoment B node2293 node2293Labels + 0)
  ring

theorem reducedTermEval891 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm891 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm891 (originalVector B) := by
  rw [reducedTermArithmetic891, ← sound2294 B hB hF]
  change (-9942532690001264640000 : ℝ) * mixedMoment B node2294 node2294Labels =
    (37623398400 : ℝ) * (((-264264609600 : ℤ) : ℝ) * mixedMoment B node2294 node2294Labels + 0)
  ring

theorem reducedTermEval892 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm892 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm892 (originalVector B) := by
  rw [reducedTermArithmetic892, ← sound2323 B hB hF]
  change (-5775400208422010880000 : ℝ) * mixedMoment B node2323 node2323Labels =
    (37623398400 : ℝ) * (((-153505543200 : ℤ) : ℝ) * mixedMoment B node2323 node2323Labels + 0)
  ring

theorem reducedTermEval893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm893 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm893 (originalVector B) := by
  rw [reducedTermArithmetic893, ← sound2327 B hB hF]
  change (1409374911961497600000 : ℝ) * mixedMoment B node2327 node2327Labels =
    (37623398400 : ℝ) * ((37460064000 : ℝ) * mixedMoment B node2327 node2327Labels + 0)
  ring

theorem reducedTermEval894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm894 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm894 (originalVector B) := by
  rw [reducedTermArithmetic894, ← sound2330 B hB hF]
  change (-1021462625098137600000 : ℝ) * mixedMoment B node2330 node2330Labels =
    (37623398400 : ℝ) * (((-27149664000 : ℤ) : ℝ) * mixedMoment B node2330 node2330Labels + 0)
  ring

theorem reducedTermEval895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm895 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm895 (originalVector B) := by
  rw [reducedTermArithmetic895, ← sound2332 B hB hF]
  change (8792971061782118400000 : ℝ) * mixedMoment B node2332 node2332Labels =
    (37623398400 : ℝ) * ((233710176000 : ℝ) * mixedMoment B node2332 node2332Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge832 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge832 (originalVector B) := by
  rw [reducedMerge832Check, Integer.Sparse.eval_mergeBy, reducedMergeEval824 B hB hF, reducedMergeEval831 B hB hF]
  rw [originalMerge832, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge833 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge833 (originalVector B) := by
  rw [reducedMerge833Check, Integer.Sparse.eval_mergeBy, reducedMergeEval818 B hB hF, reducedMergeEval832 B hB hF]
  rw [originalMerge833, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge834 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge834 (originalVector B) := by
  rw [reducedMerge834Check, Integer.Sparse.eval_mergeBy, reducedMergeEval804 B hB hF, reducedMergeEval833 B hB hF]
  rw [originalMerge834, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge835 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge835 (originalVector B) := by
  rw [reducedMerge835Check, Integer.Sparse.eval_mergeBy, reducedMergeEval775 B hB hF, reducedMergeEval834 B hB hF]
  rw [originalMerge835, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge836 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge836 (originalVector B) := by
  rw [reducedMerge836Check, Integer.Sparse.eval_mergeBy, reducedTermEval840 B hB hF, reducedTermEval841 B hB hF]
  rw [originalMerge836, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge837 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge837 (originalVector B) := by
  rw [reducedMerge837Check, Integer.Sparse.eval_mergeBy, reducedTermEval839 B hB hF, reducedMergeEval836 B hB hF]
  rw [originalMerge837, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge838 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge838 (originalVector B) := by
  rw [reducedMerge838Check, Integer.Sparse.eval_mergeBy, reducedTermEval842 B hB hF, reducedTermEval843 B hB hF]
  rw [originalMerge838, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge839 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge839 (originalVector B) := by
  rw [reducedMerge839Check, Integer.Sparse.eval_mergeBy, reducedTermEval844 B hB hF, reducedTermEval845 B hB hF]
  rw [originalMerge839, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge840 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge840 (originalVector B) := by
  rw [reducedMerge840Check, Integer.Sparse.eval_mergeBy, reducedMergeEval838 B hB hF, reducedMergeEval839 B hB hF]
  rw [originalMerge840, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge841 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge841 (originalVector B) := by
  rw [reducedMerge841Check, Integer.Sparse.eval_mergeBy, reducedMergeEval837 B hB hF, reducedMergeEval840 B hB hF]
  rw [originalMerge841, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge842 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge842 (originalVector B) := by
  rw [reducedMerge842Check, Integer.Sparse.eval_mergeBy, reducedTermEval846 B hB hF, reducedTermEval847 B hB hF]
  rw [originalMerge842, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge843 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge843 (originalVector B) := by
  rw [reducedMerge843Check, Integer.Sparse.eval_mergeBy, reducedTermEval848 B hB hF, reducedTermEval849 B hB hF]
  rw [originalMerge843, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge844 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge844 (originalVector B) := by
  rw [reducedMerge844Check, Integer.Sparse.eval_mergeBy, reducedMergeEval842 B hB hF, reducedMergeEval843 B hB hF]
  rw [originalMerge844, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge845 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge845 (originalVector B) := by
  rw [reducedMerge845Check, Integer.Sparse.eval_mergeBy, reducedTermEval850 B hB hF, reducedTermEval851 B hB hF]
  rw [originalMerge845, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge846 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge846 (originalVector B) := by
  rw [reducedMerge846Check, Integer.Sparse.eval_mergeBy, reducedTermEval852 B hB hF, reducedTermEval853 B hB hF]
  rw [originalMerge846, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge847 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge847 (originalVector B) := by
  rw [reducedMerge847Check, Integer.Sparse.eval_mergeBy, reducedMergeEval845 B hB hF, reducedMergeEval846 B hB hF]
  rw [originalMerge847, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge848 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge848 (originalVector B) := by
  rw [reducedMerge848Check, Integer.Sparse.eval_mergeBy, reducedMergeEval844 B hB hF, reducedMergeEval847 B hB hF]
  rw [originalMerge848, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge849 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge849 (originalVector B) := by
  rw [reducedMerge849Check, Integer.Sparse.eval_mergeBy, reducedMergeEval841 B hB hF, reducedMergeEval848 B hB hF]
  rw [originalMerge849, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge850 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge850 (originalVector B) := by
  rw [reducedMerge850Check, Integer.Sparse.eval_mergeBy, reducedTermEval855 B hB hF, reducedTermEval856 B hB hF]
  rw [originalMerge850, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge851 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge851 (originalVector B) := by
  rw [reducedMerge851Check, Integer.Sparse.eval_mergeBy, reducedTermEval854 B hB hF, reducedMergeEval850 B hB hF]
  rw [originalMerge851, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge852 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge852 (originalVector B) := by
  rw [reducedMerge852Check, Integer.Sparse.eval_mergeBy, reducedTermEval857 B hB hF, reducedTermEval858 B hB hF]
  rw [originalMerge852, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge853 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge853 (originalVector B) := by
  rw [reducedMerge853Check, Integer.Sparse.eval_mergeBy, reducedTermEval859 B hB hF, reducedTermEval860 B hB hF]
  rw [originalMerge853, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge854 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge854 (originalVector B) := by
  rw [reducedMerge854Check, Integer.Sparse.eval_mergeBy, reducedMergeEval852 B hB hF, reducedMergeEval853 B hB hF]
  rw [originalMerge854, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge855 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge855 (originalVector B) := by
  rw [reducedMerge855Check, Integer.Sparse.eval_mergeBy, reducedMergeEval851 B hB hF, reducedMergeEval854 B hB hF]
  rw [originalMerge855, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge856 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge856 (originalVector B) := by
  rw [reducedMerge856Check, Integer.Sparse.eval_mergeBy, reducedTermEval861 B hB hF, reducedTermEval862 B hB hF]
  rw [originalMerge856, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge857 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge857 (originalVector B) := by
  rw [reducedMerge857Check, Integer.Sparse.eval_mergeBy, reducedTermEval863 B hB hF, reducedTermEval864 B hB hF]
  rw [originalMerge857, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval858 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge858 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge858 (originalVector B) := by
  rw [reducedMerge858Check, Integer.Sparse.eval_mergeBy, reducedMergeEval856 B hB hF, reducedMergeEval857 B hB hF]
  rw [originalMerge858, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge859 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge859 (originalVector B) := by
  rw [reducedMerge859Check, Integer.Sparse.eval_mergeBy, reducedTermEval865 B hB hF, reducedTermEval866 B hB hF]
  rw [originalMerge859, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge860 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge860 (originalVector B) := by
  rw [reducedMerge860Check, Integer.Sparse.eval_mergeBy, reducedTermEval867 B hB hF, reducedTermEval868 B hB hF]
  rw [originalMerge860, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge861 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge861 (originalVector B) := by
  rw [reducedMerge861Check, Integer.Sparse.eval_mergeBy, reducedMergeEval859 B hB hF, reducedMergeEval860 B hB hF]
  rw [originalMerge861, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge862 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge862 (originalVector B) := by
  rw [reducedMerge862Check, Integer.Sparse.eval_mergeBy, reducedMergeEval858 B hB hF, reducedMergeEval861 B hB hF]
  rw [originalMerge862, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval863 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge863 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge863 (originalVector B) := by
  rw [reducedMerge863Check, Integer.Sparse.eval_mergeBy, reducedMergeEval855 B hB hF, reducedMergeEval862 B hB hF]
  rw [originalMerge863, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval896 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm896 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm896 (originalVector B) := by
  rw [reducedTermArithmetic896, ← sound2334 B hB hF]
  change (1021462625098137600000 : ℝ) * mixedMoment B node2334 node2334Labels =
    (37623398400 : ℝ) * ((27149664000 : ℝ) * mixedMoment B node2334 node2334Labels + 0)
  ring

theorem reducedTermEval897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm897 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm897 (originalVector B) := by
  rw [reducedTermArithmetic897, ← sound2337 B hB hF]
  change (2042925250196275200000 : ℝ) * mixedMoment B node2337 node2337Labels =
    (37623398400 : ℝ) * ((54299328000 : ℝ) * mixedMoment B node2337 node2337Labels + 0)
  ring

theorem reducedTermEval898 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm898 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm898 (originalVector B) := by
  rw [reducedTermArithmetic898, ← sound2338 B hB hF]
  change (6349509219129753600000 : ℝ) * mixedMoment B node2338 node2338Labels =
    (37623398400 : ℝ) * ((168764904000 : ℝ) * mixedMoment B node2338 node2338Labels + 0)
  ring

theorem reducedTermEval899 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm899 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm899 (originalVector B) := by
  rw [reducedTermArithmetic899, ← sound2339 B hB hF]
  change (-1957928575441305600000 : ℝ) * mixedMoment B node2339 node2339Labels =
    (37623398400 : ℝ) * (((-52040184000 : ℤ) : ℝ) * mixedMoment B node2339 node2339Labels + 0)
  ring

theorem reducedTermEval900 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm900 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm900 (originalVector B) := by
  rw [reducedTermArithmetic900, ← sound2340 B hB hF]
  change (-5831241247610634240000 : ℝ) * mixedMoment B node2340 node2340Labels =
    (37623398400 : ℝ) * (((-154989753600 : ℤ) : ℝ) * mixedMoment B node2340 node2340Labels + 0)
  ring

theorem reducedTermEval901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm901 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm901 (originalVector B) := by
  rw [reducedTermArithmetic901, ← sound2341 B hB hF]
  change (-4592195406267678720000 : ℝ) * mixedMoment B node2341 node2341Labels =
    (37623398400 : ℝ) * (((-122056900800 : ℤ) : ℝ) * mixedMoment B node2341 node2341Labels + 0)
  ring

theorem reducedTermEval902 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm902 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm902 (originalVector B) := by
  rw [reducedTermArithmetic902, ← sound2342 B hB hF]
  change (-8792971061782118400000 : ℝ) * mixedMoment B node2342 node2342Labels =
    (37623398400 : ℝ) * (((-233710176000 : ℤ) : ℝ) * mixedMoment B node2342 node2342Labels + 0)
  ring

theorem reducedTermEval903 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm903 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm903 (originalVector B) := by
  rw [reducedTermArithmetic903, ← sound2344 B hB hF]
  change (-1021462625098137600000 : ℝ) * mixedMoment B node2344 node2344Labels =
    (37623398400 : ℝ) * (((-27149664000 : ℤ) : ℝ) * mixedMoment B node2344 node2344Labels + 0)
  ring

theorem reducedTermEval904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm904 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm904 (originalVector B) := by
  rw [reducedTermArithmetic904, ← sound2345 B hB hF]
  change (-15267702809682247680000 : ℝ) * mixedMoment B node2345 node2345Labels =
    (37623398400 : ℝ) * (((-405803395200 : ℤ) : ℝ) * mixedMoment B node2345 node2345Labels + 0)
  ring

theorem reducedTermEval905 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm905 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm905 (originalVector B) := by
  rw [reducedTermArithmetic905, ← sound2346 B hB hF]
  change (3811111984406200320000 : ℝ) * mixedMoment B node2346 node2346Labels =
    (37623398400 : ℝ) * ((101296324800 : ℝ) * mixedMoment B node2346 node2346Labels + 0)
  ring

theorem reducedTermEval906 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm906 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm906 (originalVector B) := by
  rw [reducedTermArithmetic906, ← sound2347 B hB hF]
  change (54778388874854400000 : ℝ) * mixedMoment B node2347 node2347Labels =
    (37623398400 : ℝ) * ((1455966000 : ℝ) * mixedMoment B node2347 node2347Labels + 0)
  ring

theorem reducedTermEval907 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm907 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm907 (originalVector B) := by
  rw [reducedTermArithmetic907, ← sound2348 B hB hF]
  change (-54778388874854400000 : ℝ) * mixedMoment B node2348 node2348Labels =
    (37623398400 : ℝ) * (((-1455966000 : ℤ) : ℝ) * mixedMoment B node2348 node2348Labels + 0)
  ring

theorem reducedTermEval908 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm908 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm908 (originalVector B) := by
  rw [reducedTermArithmetic908, ← sound2349 B hB hF]
  change (-598839592845312000000 : ℝ) * mixedMoment B node2349 node2349Labels =
    (37623398400 : ℝ) * (((-15916680000 : ℤ) : ℝ) * mixedMoment B node2349 node2349Labels + 0)
  ring

theorem reducedTermEval909 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm909 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm909 (originalVector B) := by
  rw [reducedTermArithmetic909, ← sound2350 B hB hF]
  change (-2122040394523607040000 : ℝ) * mixedMoment B node2350 node2350Labels =
    (37623398400 : ℝ) * (((-56402145600 : ℤ) : ℝ) * mixedMoment B node2350 node2350Labels + 0)
  ring

theorem reducedTermEval910 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm910 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm910 (originalVector B) := by
  rw [reducedTermArithmetic910, ← sound2352 B hB hF]
  change (14499441893476270080000 : ℝ) * mixedMoment B node2352 node2352Labels =
    (37623398400 : ℝ) * ((385383631200 : ℝ) * mixedMoment B node2352 node2352Labels + 0)
  ring

theorem reducedTermEval911 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm911 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm911 (originalVector B) := by
  rw [reducedTermArithmetic911, ← sound2353 B hB hF]
  change (-4008567374777548800000 : ℝ) * mixedMoment B node2353 node2353Labels =
    (37623398400 : ℝ) * (((-106544532000 : ℤ) : ℝ) * mixedMoment B node2353 node2353Labels + 0)
  ring

theorem reducedTermEval912 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm912 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm912 (originalVector B) := by
  rw [reducedTermArithmetic912, ← sound2355 B hB hF]
  change (-3201531558440140800000 : ℝ) * mixedMoment B node2355 node2355Labels =
    (37623398400 : ℝ) * (((-85094162000 : ℤ) : ℝ) * mixedMoment B node2355 node2355Labels + 0)
  ring

theorem reducedTermEval913 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm913 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm913 (originalVector B) := by
  rw [reducedTermArithmetic913, ← sound2356 B hB hF]
  change (7210098933217689600000 : ℝ) * mixedMoment B node2356 node2356Labels =
    (37623398400 : ℝ) * ((191638694000 : ℝ) * mixedMoment B node2356 node2356Labels + 0)
  ring

theorem reducedTermEval914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm914 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm914 (originalVector B) := by
  rw [reducedTermArithmetic914, ← sound2361 B hB hF]
  change (-4433171053215744000000 : ℝ) * mixedMoment B node2361 node2361Labels =
    (37623398400 : ℝ) * (((-117830160000 : ℤ) : ℝ) * mixedMoment B node2361 node2361Labels + 0)
  ring

theorem reducedTermEval915 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm915 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm915 (originalVector B) := by
  rw [reducedTermArithmetic915, ← sound2362 B hB hF]
  change (-9916201969680384000000 : ℝ) * mixedMoment B node2362 node2362Labels =
    (37623398400 : ℝ) * (((-263564760000 : ℤ) : ℝ) * mixedMoment B node2362 node2362Labels + 0)
  ring

theorem reducedTermEval916 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm916 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm916 (originalVector B) := by
  rw [reducedTermArithmetic916, ← sound2423 B hB hF]
  change (5684917680995696640000 : ℝ) * mixedMoment B node2423 node2423Labels =
    (37623398400 : ℝ) * ((151100589600 : ℝ) * mixedMoment B node2423 node2423Labels + 0)
  ring

theorem reducedTermEval917 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm917 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm917 (originalVector B) := by
  rw [reducedTermArithmetic917, ← sound2425 B hB hF]
  change (-3022934715924480000000 : ℝ) * mixedMoment B node2425 node2425Labels =
    (37623398400 : ℝ) * (((-80347200000 : ℤ) : ℝ) * mixedMoment B node2425 node2425Labels + 0)
  ring

theorem reducedTermEval918 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm918 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm918 (originalVector B) := by
  rw [reducedTermArithmetic918, ← sound2426 B hB hF]
  change (-2089015568665804800000 : ℝ) * mixedMoment B node2426 node2426Labels =
    (37623398400 : ℝ) * (((-55524372000 : ℤ) : ℝ) * mixedMoment B node2426 node2426Labels + 0)
  ring

theorem reducedTermEval919 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm919 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm919 (originalVector B) := by
  rw [reducedTermArithmetic919, ← sound2428 B hB hF]
  change (5559732986314752000000 : ℝ) * mixedMoment B node2428 node2428Labels =
    (37623398400 : ℝ) * ((147773280000 : ℝ) * mixedMoment B node2428 node2428Labels + 0)
  ring

theorem reducedTermEval920 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm920 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm920 (originalVector B) := by
  rw [reducedTermArithmetic920, ← sound2429 B hB hF]
  change (-3513264514950758400000 : ℝ) * mixedMoment B node2429 node2429Labels =
    (37623398400 : ℝ) * (((-93379776000 : ℤ) : ℝ) * mixedMoment B node2429 node2429Labels + 0)
  ring

theorem reducedTermEval921 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm921 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm921 (originalVector B) := by
  rw [reducedTermArithmetic921, ← sound2430 B hB hF]
  change (19962365120110264320000 : ℝ) * mixedMoment B node2430 node2430Labels =
    (37623398400 : ℝ) * ((530583784800 : ℝ) * mixedMoment B node2430 node2430Labels + 0)
  ring

theorem reducedTermEval922 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm922 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm922 (originalVector B) := by
  rw [reducedTermArithmetic922, ← sound2431 B hB hF]
  change (14124724583912570880000 : ℝ) * mixedMoment B node2431 node2431Labels =
    (37623398400 : ℝ) * ((375423943200 : ℝ) * mixedMoment B node2431 node2431Labels + 0)
  ring

theorem reducedTermEval923 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm923 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm923 (originalVector B) := by
  rw [reducedTermArithmetic923, ← sound2432 B hB hF]
  change (762973624782028800000 : ℝ) * mixedMoment B node2432 node2432Labels =
    (37623398400 : ℝ) * ((20279232000 : ℝ) * mixedMoment B node2432 node2432Labels + 0)
  ring

theorem reducedTermEval924 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm924 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm924 (originalVector B) := by
  rw [reducedTermArithmetic924, ← sound2433 B hB hF]
  change (2089015568665804800000 : ℝ) * mixedMoment B node2433 node2433Labels =
    (37623398400 : ℝ) * ((55524372000 : ℝ) * mixedMoment B node2433 node2433Labels + 0)
  ring

theorem reducedTermEval925 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm925 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm925 (originalVector B) := by
  rw [reducedTermArithmetic925, ← sound2434 B hB hF]
  change (-4285922492777103360000 : ℝ) * mixedMoment B node2434 node2434Labels =
    (37623398400 : ℝ) * (((-113916410400 : ℤ) : ℝ) * mixedMoment B node2434 node2434Labels + 0)
  ring

theorem reducedTermEval926 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm926 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm926 (originalVector B) := by
  rw [reducedTermArithmetic926, ← sound2435 B hB hF]
  change (5339288646065848320000 : ℝ) * mixedMoment B node2435 node2435Labels =
    (37623398400 : ℝ) * ((141914044800 : ℝ) * mixedMoment B node2435 node2435Labels + 0)
  ring

theorem reducedTermEval927 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm927 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm927 (originalVector B) := by
  rw [reducedTermArithmetic927, ← sound2437 B hB hF]
  change (-29125569354242457600000 : ℝ) * mixedMoment B node2437 node2437Labels =
    (37623398400 : ℝ) * (((-774134464000 : ℤ) : ℝ) * mixedMoment B node2437 node2437Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval864 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge864 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge864 (originalVector B) := by
  rw [reducedMerge864Check, Integer.Sparse.eval_mergeBy, reducedMergeEval849 B hB hF, reducedMergeEval863 B hB hF]
  rw [originalMerge864, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval865 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge865 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge865 (originalVector B) := by
  rw [reducedMerge865Check, Integer.Sparse.eval_mergeBy, reducedTermEval870 B hB hF, reducedTermEval871 B hB hF]
  rw [originalMerge865, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval866 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge866 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge866 (originalVector B) := by
  rw [reducedMerge866Check, Integer.Sparse.eval_mergeBy, reducedTermEval869 B hB hF, reducedMergeEval865 B hB hF]
  rw [originalMerge866, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval867 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge867 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge867 (originalVector B) := by
  rw [reducedMerge867Check, Integer.Sparse.eval_mergeBy, reducedTermEval872 B hB hF, reducedTermEval873 B hB hF]
  rw [originalMerge867, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval868 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge868 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge868 (originalVector B) := by
  rw [reducedMerge868Check, Integer.Sparse.eval_mergeBy, reducedTermEval874 B hB hF, reducedTermEval875 B hB hF]
  rw [originalMerge868, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval869 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge869 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge869 (originalVector B) := by
  rw [reducedMerge869Check, Integer.Sparse.eval_mergeBy, reducedMergeEval867 B hB hF, reducedMergeEval868 B hB hF]
  rw [originalMerge869, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval870 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge870 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge870 (originalVector B) := by
  rw [reducedMerge870Check, Integer.Sparse.eval_mergeBy, reducedMergeEval866 B hB hF, reducedMergeEval869 B hB hF]
  rw [originalMerge870, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval871 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge871 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge871 (originalVector B) := by
  rw [reducedMerge871Check, Integer.Sparse.eval_mergeBy, reducedTermEval876 B hB hF, reducedTermEval877 B hB hF]
  rw [originalMerge871, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval872 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge872 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge872 (originalVector B) := by
  rw [reducedMerge872Check, Integer.Sparse.eval_mergeBy, reducedTermEval878 B hB hF, reducedTermEval879 B hB hF]
  rw [originalMerge872, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval873 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge873 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge873 (originalVector B) := by
  rw [reducedMerge873Check, Integer.Sparse.eval_mergeBy, reducedMergeEval871 B hB hF, reducedMergeEval872 B hB hF]
  rw [originalMerge873, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval874 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge874 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge874 (originalVector B) := by
  rw [reducedMerge874Check, Integer.Sparse.eval_mergeBy, reducedTermEval880 B hB hF, reducedTermEval881 B hB hF]
  rw [originalMerge874, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval875 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge875 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge875 (originalVector B) := by
  rw [reducedMerge875Check, Integer.Sparse.eval_mergeBy, reducedTermEval882 B hB hF, reducedTermEval883 B hB hF]
  rw [originalMerge875, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval876 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge876 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge876 (originalVector B) := by
  rw [reducedMerge876Check, Integer.Sparse.eval_mergeBy, reducedMergeEval874 B hB hF, reducedMergeEval875 B hB hF]
  rw [originalMerge876, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval877 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge877 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge877 (originalVector B) := by
  rw [reducedMerge877Check, Integer.Sparse.eval_mergeBy, reducedMergeEval873 B hB hF, reducedMergeEval876 B hB hF]
  rw [originalMerge877, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval878 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge878 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge878 (originalVector B) := by
  rw [reducedMerge878Check, Integer.Sparse.eval_mergeBy, reducedMergeEval870 B hB hF, reducedMergeEval877 B hB hF]
  rw [originalMerge878, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval879 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge879 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge879 (originalVector B) := by
  rw [reducedMerge879Check, Integer.Sparse.eval_mergeBy, reducedTermEval885 B hB hF, reducedTermEval886 B hB hF]
  rw [originalMerge879, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval880 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge880 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge880 (originalVector B) := by
  rw [reducedMerge880Check, Integer.Sparse.eval_mergeBy, reducedTermEval884 B hB hF, reducedMergeEval879 B hB hF]
  rw [originalMerge880, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval881 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge881 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge881 (originalVector B) := by
  rw [reducedMerge881Check, Integer.Sparse.eval_mergeBy, reducedTermEval887 B hB hF, reducedTermEval888 B hB hF]
  rw [originalMerge881, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval882 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge882 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge882 (originalVector B) := by
  rw [reducedMerge882Check, Integer.Sparse.eval_mergeBy, reducedTermEval889 B hB hF, reducedTermEval890 B hB hF]
  rw [originalMerge882, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval883 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge883 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge883 (originalVector B) := by
  rw [reducedMerge883Check, Integer.Sparse.eval_mergeBy, reducedMergeEval881 B hB hF, reducedMergeEval882 B hB hF]
  rw [originalMerge883, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval884 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge884 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge884 (originalVector B) := by
  rw [reducedMerge884Check, Integer.Sparse.eval_mergeBy, reducedMergeEval880 B hB hF, reducedMergeEval883 B hB hF]
  rw [originalMerge884, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval885 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge885 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge885 (originalVector B) := by
  rw [reducedMerge885Check, Integer.Sparse.eval_mergeBy, reducedTermEval891 B hB hF, reducedTermEval892 B hB hF]
  rw [originalMerge885, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval886 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge886 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge886 (originalVector B) := by
  rw [reducedMerge886Check, Integer.Sparse.eval_mergeBy, reducedTermEval893 B hB hF, reducedTermEval894 B hB hF]
  rw [originalMerge886, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval887 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge887 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge887 (originalVector B) := by
  rw [reducedMerge887Check, Integer.Sparse.eval_mergeBy, reducedMergeEval885 B hB hF, reducedMergeEval886 B hB hF]
  rw [originalMerge887, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval888 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge888 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge888 (originalVector B) := by
  rw [reducedMerge888Check, Integer.Sparse.eval_mergeBy, reducedTermEval895 B hB hF, reducedTermEval896 B hB hF]
  rw [originalMerge888, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval889 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge889 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge889 (originalVector B) := by
  rw [reducedMerge889Check, Integer.Sparse.eval_mergeBy, reducedTermEval897 B hB hF, reducedTermEval898 B hB hF]
  rw [originalMerge889, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval890 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge890 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge890 (originalVector B) := by
  rw [reducedMerge890Check, Integer.Sparse.eval_mergeBy, reducedMergeEval888 B hB hF, reducedMergeEval889 B hB hF]
  rw [originalMerge890, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval891 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge891 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge891 (originalVector B) := by
  rw [reducedMerge891Check, Integer.Sparse.eval_mergeBy, reducedMergeEval887 B hB hF, reducedMergeEval890 B hB hF]
  rw [originalMerge891, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval892 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge892 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge892 (originalVector B) := by
  rw [reducedMerge892Check, Integer.Sparse.eval_mergeBy, reducedMergeEval884 B hB hF, reducedMergeEval891 B hB hF]
  rw [originalMerge892, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge893 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge893 (originalVector B) := by
  rw [reducedMerge893Check, Integer.Sparse.eval_mergeBy, reducedMergeEval878 B hB hF, reducedMergeEval892 B hB hF]
  rw [originalMerge893, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge894 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge894 (originalVector B) := by
  rw [reducedMerge894Check, Integer.Sparse.eval_mergeBy, reducedMergeEval864 B hB hF, reducedMergeEval893 B hB hF]
  rw [originalMerge894, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge895 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge895 (originalVector B) := by
  rw [reducedMerge895Check, Integer.Sparse.eval_mergeBy, reducedTermEval900 B hB hF, reducedTermEval901 B hB hF]
  rw [originalMerge895, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval928 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm928 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm928 (originalVector B) := by
  rw [reducedTermArithmetic928, ← sound2438 B hB hF]
  change (-4666690457468928000000 : ℝ) * mixedMoment B node2438 node2438Labels =
    (37623398400 : ℝ) * (((-124036920000 : ℤ) : ℝ) * mixedMoment B node2438 node2438Labels + 0)
  ring

theorem reducedTermEval929 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm929 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm929 (originalVector B) := by
  rw [reducedTermArithmetic929, ← sound2440 B hB hF]
  change (-1089057424637952000000 : ℝ) * mixedMoment B node2440 node2440Labels =
    (37623398400 : ℝ) * (((-28946280000 : ℤ) : ℝ) * mixedMoment B node2440 node2440Labels + 0)
  ring

theorem reducedTermEval930 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm930 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm930 (originalVector B) := by
  rw [reducedTermArithmetic930, ← sound2441 B hB hF]
  change (-27156418471526400000 : ℝ) * mixedMoment B node2441 node2441Labels =
    (37623398400 : ℝ) * (((-721796000 : ℤ) : ℝ) * mixedMoment B node2441 node2441Labels + 0)
  ring

theorem reducedTermEval931 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm931 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm931 (originalVector B) := by
  rw [reducedTermArithmetic931, ← sound2442 B hB hF]
  change (4167404634193920000000 : ℝ) * mixedMoment B node2442 node2442Labels =
    (37623398400 : ℝ) * ((110766300000 : ℝ) * mixedMoment B node2442 node2442Labels + 0)
  ring

theorem reducedTermEval932 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm932 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm932 (originalVector B) := by
  rw [reducedTermArithmetic932, ← sound2443 B hB hF]
  change (-6201565287992524800000 : ℝ) * mixedMoment B node2443 node2443Labels =
    (37623398400 : ℝ) * (((-164832672000 : ℤ) : ℝ) * mixedMoment B node2443 node2443Labels + 0)
  ring

theorem reducedTermEval933 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm933 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm933 (originalVector B) := by
  rw [reducedTermArithmetic933, ← sound2470 B hB hF]
  change (-669848715789926400000 : ℝ) * mixedMoment B node2470 node2470Labels =
    (37623398400 : ℝ) * (((-17804046000 : ℤ) : ℝ) * mixedMoment B node2470 node2470Labels + 0)
  ring

theorem reducedTermEval934 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm934 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm934 (originalVector B) := by
  rw [reducedTermArithmetic934, ← sound2471 B hB hF]
  change (5402275542460661760000 : ℝ) * mixedMoment B node2471 node2471Labels =
    (37623398400 : ℝ) * ((143588186400 : ℝ) * mixedMoment B node2471 node2471Labels + 0)
  ring

theorem reducedTermEval935 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm935 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm935 (originalVector B) := by
  rw [reducedTermArithmetic935, ← sound2473 B hB hF]
  change (669848715789926400000 : ℝ) * mixedMoment B node2473 node2473Labels =
    (37623398400 : ℝ) * ((17804046000 : ℝ) * mixedMoment B node2473 node2473Labels + 0)
  ring

theorem reducedTermEval936 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm936 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm936 (originalVector B) := by
  rw [reducedTermArithmetic936, ← sound2479 B hB hF]
  change (-21951447043276800000 : ℝ) * mixedMoment B node2479 node2479Labels =
    (37623398400 : ℝ) * (((-583452000 : ℤ) : ℝ) * mixedMoment B node2479 node2479Labels + 0)
  ring

theorem reducedTermEval937 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm937 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm937 (originalVector B) := by
  rw [reducedTermArithmetic937, ← sound2480 B hB hF]
  change (-12811011857783193600000 : ℝ) * mixedMoment B node2480 node2480Labels =
    (37623398400 : ℝ) * (((-340506504000 : ℤ) : ℝ) * mixedMoment B node2480 node2480Labels + 0)
  ring

theorem reducedTermEval938 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm938 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm938 (originalVector B) := by
  rw [reducedTermArithmetic938, ← sound2482 B hB hF]
  change (3044886162967756800000 : ℝ) * mixedMoment B node2482 node2482Labels =
    (37623398400 : ℝ) * ((80930652000 : ℝ) * mixedMoment B node2482 node2482Labels + 0)
  ring

theorem reducedTermEval939 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm939 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm939 (originalVector B) := by
  rw [reducedTermArithmetic939, ← sound2483 B hB hF]
  change (10730200326977617920000 : ℝ) * mixedMoment B node2483 node2483Labels =
    (37623398400 : ℝ) * ((285200188800 : ℝ) * mixedMoment B node2483 node2483Labels + 0)
  ring

theorem reducedTermEval940 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm940 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm940 (originalVector B) := by
  rw [reducedTermArithmetic940, ← sound2485 B hB hF]
  change (-7075268186112000000000 : ℝ) * mixedMoment B node2485 node2485Labels =
    (37623398400 : ℝ) * (((-188055000000 : ℤ) : ℝ) * mixedMoment B node2485 node2485Labels + 0)
  ring

theorem reducedTermEval941 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm941 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm941 (originalVector B) := by
  rw [reducedTermArithmetic941, ← sound2486 B hB hF]
  change (-10132091952404889600000 : ℝ) * mixedMoment B node2486 node2486Labels =
    (37623398400 : ℝ) * (((-269302944000 : ℤ) : ℝ) * mixedMoment B node2486 node2486Labels + 0)
  ring

theorem reducedTermEval942 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm942 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm942 (originalVector B) := by
  rw [reducedTermArithmetic942, ← sound2488 B hB hF]
  change (3036144140609126400000 : ℝ) * mixedMoment B node2488 node2488Labels =
    (37623398400 : ℝ) * ((80698296000 : ℝ) * mixedMoment B node2488 node2488Labels + 0)
  ring

theorem reducedTermEval943 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm943 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm943 (originalVector B) := by
  rw [reducedTermArithmetic943, ← sound2489 B hB hF]
  change (12048038233001164800000 : ℝ) * mixedMoment B node2489 node2489Labels =
    (37623398400 : ℝ) * ((320227272000 : ℝ) * mixedMoment B node2489 node2489Labels + 0)
  ring

theorem reducedTermEval944 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm944 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm944 (originalVector B) := by
  rw [reducedTermArithmetic944, ← sound2494 B hB hF]
  change (882109921738752000000 : ℝ) * mixedMoment B node2494 node2494Labels =
    (37623398400 : ℝ) * ((23445780000 : ℝ) * mixedMoment B node2494 node2494Labels + 0)
  ring

theorem reducedTermEval945 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm945 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm945 (originalVector B) := by
  rw [reducedTermArithmetic945, ← sound2495 B hB hF]
  change (421979070165811200000 : ℝ) * mixedMoment B node2495 node2495Labels =
    (37623398400 : ℝ) * ((11215868000 : ℝ) * mixedMoment B node2495 node2495Labels + 0)
  ring

theorem reducedTermEval946 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm946 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm946 (originalVector B) := by
  rw [reducedTermArithmetic946, ← sound2497 B hB hF]
  change (2247947368157675520000 : ℝ) * mixedMoment B node2497 node2497Labels =
    (37623398400 : ℝ) * ((59748652800 : ℝ) * mixedMoment B node2497 node2497Labels + 0)
  ring

theorem reducedTermEval947 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm947 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm947 (originalVector B) := by
  rw [reducedTermArithmetic947, ← sound2499 B hB hF]
  change (-7786684812636979200000 : ℝ) * mixedMoment B node2499 node2499Labels =
    (37623398400 : ℝ) * (((-206963888000 : ℤ) : ℝ) * mixedMoment B node2499 node2499Labels + 0)
  ring

theorem reducedTermEval948 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm948 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm948 (originalVector B) := by
  rw [reducedTermArithmetic948, ← sound2508 B hB hF]
  change (4693700295180288000000 : ℝ) * mixedMoment B node2508 node2508Labels =
    (37623398400 : ℝ) * ((124754820000 : ℝ) * mixedMoment B node2508 node2508Labels + 0)
  ring

theorem reducedTermEval949 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm949 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm949 (originalVector B) := by
  rw [reducedTermArithmetic949, ← sound2512 B hB hF]
  change (-8251961190668697600000 : ℝ) * mixedMoment B node2512 node2512Labels =
    (37623398400 : ℝ) * (((-219330564000 : ℤ) : ℝ) * mixedMoment B node2512 node2512Labels + 0)
  ring

theorem reducedTermEval950 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm950 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm950 (originalVector B) := by
  rw [reducedTermArithmetic950, ← sound2513 B hB hF]
  change (-4629005356695552000000 : ℝ) * mixedMoment B node2513 node2513Labels =
    (37623398400 : ℝ) * (((-123035280000 : ℤ) : ℝ) * mixedMoment B node2513 node2513Labels + 0)
  ring

theorem reducedTermEval951 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm951 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm951 (originalVector B) := by
  rw [reducedTermArithmetic951, ← sound2515 B hB hF]
  change (20072224660871577600000 : ℝ) * mixedMoment B node2515 node2515Labels =
    (37623398400 : ℝ) * ((533503764000 : ℝ) * mixedMoment B node2515 node2515Labels + 0)
  ring

theorem reducedTermEval952 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm952 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm952 (originalVector B) := by
  rw [reducedTermArithmetic952, ← sound2519 B hB hF]
  change (4382870405576785920000 : ℝ) * mixedMoment B node2519 node2519Labels =
    (37623398400 : ℝ) * ((116493208800 : ℝ) * mixedMoment B node2519 node2519Labels + 0)
  ring

theorem reducedTermEval953 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm953 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm953 (originalVector B) := by
  rw [reducedTermArithmetic953, ← sound2520 B hB hF]
  change (3829273250294661120000 : ℝ) * mixedMoment B node2520 node2520Labels =
    (37623398400 : ℝ) * ((101779036800 : ℝ) * mixedMoment B node2520 node2520Labels + 0)
  ring

theorem reducedTermEval954 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm954 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm954 (originalVector B) := by
  rw [reducedTermArithmetic954, ← sound2522 B hB hF]
  change (-46570423131832320000 : ℝ) * mixedMoment B node2522 node2522Labels =
    (37623398400 : ℝ) * (((-1237804800 : ℤ) : ℝ) * mixedMoment B node2522 node2522Labels + 0)
  ring

theorem reducedTermEval955 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm955 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm955 (originalVector B) := by
  rw [reducedTermArithmetic955, ← sound2524 B hB hF]
  change (94866766992506880000 : ℝ) * mixedMoment B node2524 node2524Labels =
    (37623398400 : ℝ) * ((2521483200 : ℝ) * mixedMoment B node2524 node2524Labels + 0)
  ring

theorem reducedTermEval956 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm956 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm956 (originalVector B) := by
  rw [reducedTermArithmetic956, ← sound2529 B hB hF]
  change (-1138001372530606080000 : ℝ) * mixedMoment B node2529 node2529Labels =
    (37623398400 : ℝ) * (((-30247171200 : ℤ) : ℝ) * mixedMoment B node2529 node2529Labels + 0)
  ring

theorem reducedTermEval957 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm957 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm957 (originalVector B) := by
  rw [reducedTermArithmetic957, ← sound2545 B hB hF]
  change (-1139201814778675200000 : ℝ) * mixedMoment B node2545 node2545Labels =
    (37623398400 : ℝ) * (((-30279078000 : ℤ) : ℝ) * mixedMoment B node2545 node2545Labels + 0)
  ring

theorem reducedTermEval958 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm958 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm958 (originalVector B) := by
  rw [reducedTermArithmetic958, ← sound2553 B hB hF]
  change (-5874441005529169920000 : ℝ) * mixedMoment B node2553 node2553Labels =
    (37623398400 : ℝ) * (((-156137968800 : ℤ) : ℝ) * mixedMoment B node2553 node2553Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval896 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge896 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge896 (originalVector B) := by
  rw [reducedMerge896Check, Integer.Sparse.eval_mergeBy, reducedTermEval899 B hB hF, reducedMergeEval895 B hB hF]
  rw [originalMerge896, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge897 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge897 (originalVector B) := by
  rw [reducedMerge897Check, Integer.Sparse.eval_mergeBy, reducedTermEval902 B hB hF, reducedTermEval903 B hB hF]
  rw [originalMerge897, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval898 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge898 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge898 (originalVector B) := by
  rw [reducedMerge898Check, Integer.Sparse.eval_mergeBy, reducedTermEval904 B hB hF, reducedTermEval905 B hB hF]
  rw [originalMerge898, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval899 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge899 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge899 (originalVector B) := by
  rw [reducedMerge899Check, Integer.Sparse.eval_mergeBy, reducedMergeEval897 B hB hF, reducedMergeEval898 B hB hF]
  rw [originalMerge899, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval900 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge900 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge900 (originalVector B) := by
  rw [reducedMerge900Check, Integer.Sparse.eval_mergeBy, reducedMergeEval896 B hB hF, reducedMergeEval899 B hB hF]
  rw [originalMerge900, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge901 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge901 (originalVector B) := by
  rw [reducedMerge901Check, Integer.Sparse.eval_mergeBy, reducedTermEval906 B hB hF, reducedTermEval907 B hB hF]
  rw [originalMerge901, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval902 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge902 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge902 (originalVector B) := by
  rw [reducedMerge902Check, Integer.Sparse.eval_mergeBy, reducedTermEval908 B hB hF, reducedTermEval909 B hB hF]
  rw [originalMerge902, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval903 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge903 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge903 (originalVector B) := by
  rw [reducedMerge903Check, Integer.Sparse.eval_mergeBy, reducedMergeEval901 B hB hF, reducedMergeEval902 B hB hF]
  rw [originalMerge903, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge904 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge904 (originalVector B) := by
  rw [reducedMerge904Check, Integer.Sparse.eval_mergeBy, reducedTermEval910 B hB hF, reducedTermEval911 B hB hF]
  rw [originalMerge904, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval905 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge905 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge905 (originalVector B) := by
  rw [reducedMerge905Check, Integer.Sparse.eval_mergeBy, reducedTermEval912 B hB hF, reducedTermEval913 B hB hF]
  rw [originalMerge905, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval906 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge906 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge906 (originalVector B) := by
  rw [reducedMerge906Check, Integer.Sparse.eval_mergeBy, reducedMergeEval904 B hB hF, reducedMergeEval905 B hB hF]
  rw [originalMerge906, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval907 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge907 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge907 (originalVector B) := by
  rw [reducedMerge907Check, Integer.Sparse.eval_mergeBy, reducedMergeEval903 B hB hF, reducedMergeEval906 B hB hF]
  rw [originalMerge907, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval908 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge908 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge908 (originalVector B) := by
  rw [reducedMerge908Check, Integer.Sparse.eval_mergeBy, reducedMergeEval900 B hB hF, reducedMergeEval907 B hB hF]
  rw [originalMerge908, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval909 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge909 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge909 (originalVector B) := by
  rw [reducedMerge909Check, Integer.Sparse.eval_mergeBy, reducedTermEval915 B hB hF, reducedTermEval916 B hB hF]
  rw [originalMerge909, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval910 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge910 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge910 (originalVector B) := by
  rw [reducedMerge910Check, Integer.Sparse.eval_mergeBy, reducedTermEval914 B hB hF, reducedMergeEval909 B hB hF]
  rw [originalMerge910, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval911 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge911 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge911 (originalVector B) := by
  rw [reducedMerge911Check, Integer.Sparse.eval_mergeBy, reducedTermEval917 B hB hF, reducedTermEval918 B hB hF]
  rw [originalMerge911, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval912 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge912 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge912 (originalVector B) := by
  rw [reducedMerge912Check, Integer.Sparse.eval_mergeBy, reducedTermEval919 B hB hF, reducedTermEval920 B hB hF]
  rw [originalMerge912, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval913 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge913 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge913 (originalVector B) := by
  rw [reducedMerge913Check, Integer.Sparse.eval_mergeBy, reducedMergeEval911 B hB hF, reducedMergeEval912 B hB hF]
  rw [originalMerge913, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge914 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge914 (originalVector B) := by
  rw [reducedMerge914Check, Integer.Sparse.eval_mergeBy, reducedMergeEval910 B hB hF, reducedMergeEval913 B hB hF]
  rw [originalMerge914, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval915 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge915 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge915 (originalVector B) := by
  rw [reducedMerge915Check, Integer.Sparse.eval_mergeBy, reducedTermEval921 B hB hF, reducedTermEval922 B hB hF]
  rw [originalMerge915, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval916 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge916 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge916 (originalVector B) := by
  rw [reducedMerge916Check, Integer.Sparse.eval_mergeBy, reducedTermEval923 B hB hF, reducedTermEval924 B hB hF]
  rw [originalMerge916, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval917 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge917 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge917 (originalVector B) := by
  rw [reducedMerge917Check, Integer.Sparse.eval_mergeBy, reducedMergeEval915 B hB hF, reducedMergeEval916 B hB hF]
  rw [originalMerge917, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval918 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge918 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge918 (originalVector B) := by
  rw [reducedMerge918Check, Integer.Sparse.eval_mergeBy, reducedTermEval925 B hB hF, reducedTermEval926 B hB hF]
  rw [originalMerge918, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval919 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge919 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge919 (originalVector B) := by
  rw [reducedMerge919Check, Integer.Sparse.eval_mergeBy, reducedTermEval927 B hB hF, reducedTermEval928 B hB hF]
  rw [originalMerge919, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval920 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge920 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge920 (originalVector B) := by
  rw [reducedMerge920Check, Integer.Sparse.eval_mergeBy, reducedMergeEval918 B hB hF, reducedMergeEval919 B hB hF]
  rw [originalMerge920, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval921 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge921 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge921 (originalVector B) := by
  rw [reducedMerge921Check, Integer.Sparse.eval_mergeBy, reducedMergeEval917 B hB hF, reducedMergeEval920 B hB hF]
  rw [originalMerge921, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval922 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge922 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge922 (originalVector B) := by
  rw [reducedMerge922Check, Integer.Sparse.eval_mergeBy, reducedMergeEval914 B hB hF, reducedMergeEval921 B hB hF]
  rw [originalMerge922, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval923 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge923 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge923 (originalVector B) := by
  rw [reducedMerge923Check, Integer.Sparse.eval_mergeBy, reducedMergeEval908 B hB hF, reducedMergeEval922 B hB hF]
  rw [originalMerge923, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval924 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge924 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge924 (originalVector B) := by
  rw [reducedMerge924Check, Integer.Sparse.eval_mergeBy, reducedTermEval930 B hB hF, reducedTermEval931 B hB hF]
  rw [originalMerge924, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval925 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge925 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge925 (originalVector B) := by
  rw [reducedMerge925Check, Integer.Sparse.eval_mergeBy, reducedTermEval929 B hB hF, reducedMergeEval924 B hB hF]
  rw [originalMerge925, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval926 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge926 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge926 (originalVector B) := by
  rw [reducedMerge926Check, Integer.Sparse.eval_mergeBy, reducedTermEval932 B hB hF, reducedTermEval933 B hB hF]
  rw [originalMerge926, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval927 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge927 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge927 (originalVector B) := by
  rw [reducedMerge927Check, Integer.Sparse.eval_mergeBy, reducedTermEval934 B hB hF, reducedTermEval935 B hB hF]
  rw [originalMerge927, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval928 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge928 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge928 (originalVector B) := by
  rw [reducedMerge928Check, Integer.Sparse.eval_mergeBy, reducedMergeEval926 B hB hF, reducedMergeEval927 B hB hF]
  rw [originalMerge928, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval929 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge929 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge929 (originalVector B) := by
  rw [reducedMerge929Check, Integer.Sparse.eval_mergeBy, reducedMergeEval925 B hB hF, reducedMergeEval928 B hB hF]
  rw [originalMerge929, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval930 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge930 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge930 (originalVector B) := by
  rw [reducedMerge930Check, Integer.Sparse.eval_mergeBy, reducedTermEval936 B hB hF, reducedTermEval937 B hB hF]
  rw [originalMerge930, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval931 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge931 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge931 (originalVector B) := by
  rw [reducedMerge931Check, Integer.Sparse.eval_mergeBy, reducedTermEval938 B hB hF, reducedTermEval939 B hB hF]
  rw [originalMerge931, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval932 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge932 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge932 (originalVector B) := by
  rw [reducedMerge932Check, Integer.Sparse.eval_mergeBy, reducedMergeEval930 B hB hF, reducedMergeEval931 B hB hF]
  rw [originalMerge932, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval933 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge933 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge933 (originalVector B) := by
  rw [reducedMerge933Check, Integer.Sparse.eval_mergeBy, reducedTermEval940 B hB hF, reducedTermEval941 B hB hF]
  rw [originalMerge933, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval934 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge934 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge934 (originalVector B) := by
  rw [reducedMerge934Check, Integer.Sparse.eval_mergeBy, reducedTermEval942 B hB hF, reducedTermEval943 B hB hF]
  rw [originalMerge934, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval935 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge935 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge935 (originalVector B) := by
  rw [reducedMerge935Check, Integer.Sparse.eval_mergeBy, reducedMergeEval933 B hB hF, reducedMergeEval934 B hB hF]
  rw [originalMerge935, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval936 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge936 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge936 (originalVector B) := by
  rw [reducedMerge936Check, Integer.Sparse.eval_mergeBy, reducedMergeEval932 B hB hF, reducedMergeEval935 B hB hF]
  rw [originalMerge936, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval937 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge937 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge937 (originalVector B) := by
  rw [reducedMerge937Check, Integer.Sparse.eval_mergeBy, reducedMergeEval929 B hB hF, reducedMergeEval936 B hB hF]
  rw [originalMerge937, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval938 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge938 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge938 (originalVector B) := by
  rw [reducedMerge938Check, Integer.Sparse.eval_mergeBy, reducedTermEval945 B hB hF, reducedTermEval946 B hB hF]
  rw [originalMerge938, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval939 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge939 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge939 (originalVector B) := by
  rw [reducedMerge939Check, Integer.Sparse.eval_mergeBy, reducedTermEval944 B hB hF, reducedMergeEval938 B hB hF]
  rw [originalMerge939, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval940 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge940 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge940 (originalVector B) := by
  rw [reducedMerge940Check, Integer.Sparse.eval_mergeBy, reducedTermEval947 B hB hF, reducedTermEval948 B hB hF]
  rw [originalMerge940, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval941 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge941 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge941 (originalVector B) := by
  rw [reducedMerge941Check, Integer.Sparse.eval_mergeBy, reducedTermEval949 B hB hF, reducedTermEval950 B hB hF]
  rw [originalMerge941, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval942 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge942 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge942 (originalVector B) := by
  rw [reducedMerge942Check, Integer.Sparse.eval_mergeBy, reducedMergeEval940 B hB hF, reducedMergeEval941 B hB hF]
  rw [originalMerge942, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval943 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge943 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge943 (originalVector B) := by
  rw [reducedMerge943Check, Integer.Sparse.eval_mergeBy, reducedMergeEval939 B hB hF, reducedMergeEval942 B hB hF]
  rw [originalMerge943, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval944 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge944 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge944 (originalVector B) := by
  rw [reducedMerge944Check, Integer.Sparse.eval_mergeBy, reducedTermEval951 B hB hF, reducedTermEval952 B hB hF]
  rw [originalMerge944, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval945 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge945 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge945 (originalVector B) := by
  rw [reducedMerge945Check, Integer.Sparse.eval_mergeBy, reducedTermEval953 B hB hF, reducedTermEval954 B hB hF]
  rw [originalMerge945, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval946 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge946 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge946 (originalVector B) := by
  rw [reducedMerge946Check, Integer.Sparse.eval_mergeBy, reducedMergeEval944 B hB hF, reducedMergeEval945 B hB hF]
  rw [originalMerge946, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval947 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge947 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge947 (originalVector B) := by
  rw [reducedMerge947Check, Integer.Sparse.eval_mergeBy, reducedTermEval955 B hB hF, reducedTermEval956 B hB hF]
  rw [originalMerge947, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval948 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge948 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge948 (originalVector B) := by
  rw [reducedMerge948Check, Integer.Sparse.eval_mergeBy, reducedTermEval957 B hB hF, reducedTermEval958 B hB hF]
  rw [originalMerge948, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval949 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge949 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge949 (originalVector B) := by
  rw [reducedMerge949Check, Integer.Sparse.eval_mergeBy, reducedMergeEval947 B hB hF, reducedMergeEval948 B hB hF]
  rw [originalMerge949, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval950 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge950 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge950 (originalVector B) := by
  rw [reducedMerge950Check, Integer.Sparse.eval_mergeBy, reducedMergeEval946 B hB hF, reducedMergeEval949 B hB hF]
  rw [originalMerge950, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval951 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge951 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge951 (originalVector B) := by
  rw [reducedMerge951Check, Integer.Sparse.eval_mergeBy, reducedMergeEval943 B hB hF, reducedMergeEval950 B hB hF]
  rw [originalMerge951, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval952 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge952 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge952 (originalVector B) := by
  rw [reducedMerge952Check, Integer.Sparse.eval_mergeBy, reducedMergeEval937 B hB hF, reducedMergeEval951 B hB hF]
  rw [originalMerge952, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval953 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge953 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge953 (originalVector B) := by
  rw [reducedMerge953Check, Integer.Sparse.eval_mergeBy, reducedMergeEval923 B hB hF, reducedMergeEval952 B hB hF]
  rw [originalMerge953, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval954 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge954 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge954 (originalVector B) := by
  rw [reducedMerge954Check, Integer.Sparse.eval_mergeBy, reducedMergeEval894 B hB hF, reducedMergeEval953 B hB hF]
  rw [originalMerge954, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval955 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge955 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge955 (originalVector B) := by
  rw [reducedMerge955Check, Integer.Sparse.eval_mergeBy, reducedMergeEval835 B hB hF, reducedMergeEval954 B hB hF]
  rw [originalMerge955, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval956_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge956 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge956 (originalVector B) := by
  rw [reducedMerge956Check, Integer.Sparse.eval_mergeBy, reducedMergeEval716_e B hB hF, reducedMergeEval955 B hB hF]
  rw [originalMerge956, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e_oai
