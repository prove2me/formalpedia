-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:15:15.930207+00:00
-- url     : https://prove2.me/submissions/f8c3e942-b33b-4760-80d5-ca990b300410

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E138
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1196_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1315_e

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

theorem rowFourier_row_permutation {p : ℕ} (H : CMatrix) (a : Fin p → ℤ)
    (σ : Equiv.Perm (Fin p)) (ρ : Fin p ↪ Coord) :
    rowFourier H ρ (a ∘ σ) =
      rowFourier H (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) a := by
  unfold rowFourier
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => H (ρ (σ.symm i)) k ^ a i)

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem rowFourier_alpha_zero {H : CMatrix} (hH : FourierZero H)
    (ρ : Coord ↪ Coord) (σ : Equiv.Perm Coord) :
    rowFourier H ρ (permuteCharge σ alpha) = 0 := by
  rw [permuteCharge, rowFourier_row_permutation]
  let e : Coord ↪ Coord := Equiv.embeddingCongr σ (Equiv.refl Coord) ρ
  let π : Equiv.Perm Coord := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  exact hH π

theorem mixedMoment_alpha {n l : ℕ} (B : Fin 7 → Basis) (hB : AllTransitionsFourierZero B)
    (A : Matrix Coord (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (σ : Equiv.Perm Coord) (hA : (fun i => A i j) = permuteCharge σ alpha) :
    mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hA]
    exact rowFourier_alpha_zero (hB r _) ρ σ
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

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

theorem sound3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3633 node3633Labels = Sparse.eval nodeValue3633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3633) = mixedMoment B node3633 node3633Labels := rfl
  simpa [nodeValue3633, Sparse.eval] using hc.symm

theorem sound3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3814 node3814Labels = Sparse.eval nodeValue3814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3814) = mixedMoment B node3814 node3814Labels := rfl
  simpa [nodeValue3814, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3517 node3517Labels = Sparse.eval nodeValue3517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3517) = mixedMoment B node3517 node3517Labels := rfl
  simpa [nodeValue3517, Sparse.eval] using hc.symm

theorem sound3519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3519 node3519Labels = Sparse.eval nodeValue3519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3519) = mixedMoment B node3519 node3519Labels := rfl
  simpa [nodeValue3519, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = 0 := by
  exact mixedMoment_alpha B hF node3525 node3525Labels 1 permutation434
    (by decide +kernel)

theorem zero3547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = 0 := by
  exact mixedMoment_order_one B hB node3547 node3547Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3523 node3523Labels = Sparse.eval nodeValue3523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3523) = mixedMoment B node3523 node3523Labels := rfl
  simpa [nodeValue3523, Sparse.eval] using hc.symm

theorem sound3524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3524 node3524Labels = Sparse.eval nodeValue3524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3524) = mixedMoment B node3524 node3524Labels := rfl
  simpa [nodeValue3524, Sparse.eval] using hc.symm

theorem sound3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = Sparse.eval nodeValue3525 (mixedVector B) := by
  simpa only [nodeValue3525, Sparse.eval_nil] using zero3525 B _hB _hF

theorem sound3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3526 node3526Labels = Sparse.eval nodeValue3526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3526) = mixedMoment B node3526 node3526Labels := rfl
  simpa [nodeValue3526, Sparse.eval] using hc.symm

theorem sound3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3529 node3529Labels = Sparse.eval nodeValue3529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3529) = mixedMoment B node3529 node3529Labels := rfl
  simpa [nodeValue3529, Sparse.eval] using hc.symm

theorem sound3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3530 node3530Labels = Sparse.eval nodeValue3530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3530) = mixedMoment B node3530 node3530Labels := rfl
  simpa [nodeValue3530, Sparse.eval] using hc.symm

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3535 node3535Labels = Sparse.eval nodeValue3535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3535) = mixedMoment B node3535 node3535Labels := rfl
  simpa [nodeValue3535, Sparse.eval] using hc.symm

theorem sound3537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3537 node3537Labels = Sparse.eval nodeValue3537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3537) = mixedMoment B node3537 node3537Labels := rfl
  simpa [nodeValue3537, Sparse.eval] using hc.symm

theorem sound3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3538 node3538Labels = Sparse.eval nodeValue3538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3538) = mixedMoment B node3538 node3538Labels := rfl
  simpa [nodeValue3538, Sparse.eval] using hc.symm

theorem sound3539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3539 node3539Labels = Sparse.eval nodeValue3539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3539) = mixedMoment B node3539 node3539Labels := rfl
  simpa [nodeValue3539, Sparse.eval] using hc.symm

theorem sound3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3540 node3540Labels = Sparse.eval nodeValue3540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3540) = mixedMoment B node3540 node3540Labels := rfl
  simpa [nodeValue3540, Sparse.eval] using hc.symm

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

theorem sound3542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3542 node3542Labels = Sparse.eval nodeValue3542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3542) = mixedMoment B node3542 node3542Labels := rfl
  simpa [nodeValue3542, Sparse.eval] using hc.symm

theorem sound3543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3543 node3543Labels = Sparse.eval nodeValue3543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3543) = mixedMoment B node3543 node3543Labels := rfl
  simpa [nodeValue3543, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3549 node3549Labels = Sparse.eval nodeValue3549 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3549) = mixedMoment B node3549 node3549Labels := rfl
  simpa [nodeValue3549, Sparse.eval] using hc.symm

theorem sound3553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3553 node3553Labels = Sparse.eval nodeValue3553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3553) = mixedMoment B node3553 node3553Labels := rfl
  simpa [nodeValue3553, Sparse.eval] using hc.symm

theorem sound3554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3554 node3554Labels = Sparse.eval nodeValue3554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3554) = mixedMoment B node3554 node3554Labels := rfl
  simpa [nodeValue3554, Sparse.eval] using hc.symm

theorem sound3555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3555 node3555Labels = Sparse.eval nodeValue3555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3555) = mixedMoment B node3555 node3555Labels := rfl
  simpa [nodeValue3555, Sparse.eval] using hc.symm

theorem sound3556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3556 node3556Labels = Sparse.eval nodeValue3556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3556) = mixedMoment B node3556 node3556Labels := rfl
  simpa [nodeValue3556, Sparse.eval] using hc.symm

theorem sound3557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3557 node3557Labels = Sparse.eval nodeValue3557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3557) = mixedMoment B node3557 node3557Labels := rfl
  simpa [nodeValue3557, Sparse.eval] using hc.symm

theorem sound3558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3558 node3558Labels = Sparse.eval nodeValue3558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3558) = mixedMoment B node3558 node3558Labels := rfl
  simpa [nodeValue3558, Sparse.eval] using hc.symm

theorem sound3562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3562 node3562Labels = Sparse.eval nodeValue3562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3562) = mixedMoment B node3562 node3562Labels := rfl
  simpa [nodeValue3562, Sparse.eval] using hc.symm

theorem sound3565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3565 node3565Labels = Sparse.eval nodeValue3565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3565) = mixedMoment B node3565 node3565Labels := rfl
  simpa [nodeValue3565, Sparse.eval] using hc.symm

theorem sound3569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3569 node3569Labels = Sparse.eval nodeValue3569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3569) = mixedMoment B node3569 node3569Labels := rfl
  simpa [nodeValue3569, Sparse.eval] using hc.symm

theorem sound3570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3570 node3570Labels = Sparse.eval nodeValue3570 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3570) = mixedMoment B node3570 node3570Labels := rfl
  simpa [nodeValue3570, Sparse.eval] using hc.symm

theorem sound3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3571 node3571Labels = Sparse.eval nodeValue3571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3571) = mixedMoment B node3571 node3571Labels := rfl
  simpa [nodeValue3571, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

theorem sound3577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3577 node3577Labels = Sparse.eval nodeValue3577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3577) = mixedMoment B node3577 node3577Labels := rfl
  simpa [nodeValue3577, Sparse.eval] using hc.symm

theorem sound3578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3578 node3578Labels = Sparse.eval nodeValue3578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3578) = mixedMoment B node3578 node3578Labels := rfl
  simpa [nodeValue3578, Sparse.eval] using hc.symm

theorem sound3579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3579 node3579Labels = Sparse.eval nodeValue3579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3579) = mixedMoment B node3579 node3579Labels := rfl
  simpa [nodeValue3579, Sparse.eval] using hc.symm

theorem sound3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3580 node3580Labels = Sparse.eval nodeValue3580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3580) = mixedMoment B node3580 node3580Labels := rfl
  simpa [nodeValue3580, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3618 node3618Labels = 0 := by
  exact mixedMoment_alpha B hF node3618 node3618Labels 1 permutation434
    (by decide +kernel)

theorem zero3628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3628 node3628Labels = 0 := by
  exact mixedMoment_order_one B hB node3628 node3628Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3629 node3629Labels = 0 := by
  exact mixedMoment_order_one B hB node3629 node3629Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3635 node3635Labels = 0 := by
  exact mixedMoment_order_one B hB node3635 node3635Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3636 node3636Labels = 0 := by
  exact mixedMoment_order_one B hB node3636 node3636Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3584 node3584Labels = Sparse.eval nodeValue3584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3584) = mixedMoment B node3584 node3584Labels := rfl
  simpa [nodeValue3584, Sparse.eval] using hc.symm

theorem sound3618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3618 node3618Labels = Sparse.eval nodeValue3618 (mixedVector B) := by
  simpa only [nodeValue3618, Sparse.eval_nil] using zero3618 B _hB _hF

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

theorem sound3622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3622 node3622Labels = Sparse.eval nodeValue3622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3622) = mixedMoment B node3622 node3622Labels := rfl
  simpa [nodeValue3622, Sparse.eval] using hc.symm

theorem sound3623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3623 node3623Labels = Sparse.eval nodeValue3623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3623) = mixedMoment B node3623 node3623Labels := rfl
  simpa [nodeValue3623, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

theorem sound3628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3628 node3628Labels = Sparse.eval nodeValue3628 (mixedVector B) := by
  simpa only [nodeValue3628, Sparse.eval_nil] using zero3628 B _hB _hF

theorem sound3629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3629 node3629Labels = Sparse.eval nodeValue3629 (mixedVector B) := by
  simpa only [nodeValue3629, Sparse.eval_nil] using zero3629 B _hB _hF

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

theorem sound3635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3635 node3635Labels = Sparse.eval nodeValue3635 (mixedVector B) := by
  simpa only [nodeValue3635, Sparse.eval_nil] using zero3635 B _hB _hF

theorem sound3636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3636 node3636Labels = Sparse.eval nodeValue3636 (mixedVector B) := by
  simpa only [nodeValue3636, Sparse.eval_nil] using zero3636 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3670 node3670Labels = Sparse.eval nodeValue3670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3670) = mixedMoment B node3670 node3670Labels := rfl
  simpa [nodeValue3670, Sparse.eval] using hc.symm

theorem sound3671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3671 node3671Labels = Sparse.eval nodeValue3671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3671) = mixedMoment B node3671 node3671Labels := rfl
  simpa [nodeValue3671, Sparse.eval] using hc.symm

theorem sound3672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3672 node3672Labels = Sparse.eval nodeValue3672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3672) = mixedMoment B node3672 node3672Labels := rfl
  simpa [nodeValue3672, Sparse.eval] using hc.symm

theorem sound3673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3673 node3673Labels = Sparse.eval nodeValue3673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3673) = mixedMoment B node3673 node3673Labels := rfl
  simpa [nodeValue3673, Sparse.eval] using hc.symm

theorem sound3674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3674 node3674Labels = Sparse.eval nodeValue3674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3674) = mixedMoment B node3674 node3674Labels := rfl
  simpa [nodeValue3674, Sparse.eval] using hc.symm

theorem sound3676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3676 node3676Labels = Sparse.eval nodeValue3676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3676) = mixedMoment B node3676 node3676Labels := rfl
  simpa [nodeValue3676, Sparse.eval] using hc.symm

theorem sound3685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3685 node3685Labels = Sparse.eval nodeValue3685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3685) = mixedMoment B node3685 node3685Labels := rfl
  simpa [nodeValue3685, Sparse.eval] using hc.symm

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

theorem sound3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3692 node3692Labels = Sparse.eval nodeValue3692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3692) = mixedMoment B node3692 node3692Labels := rfl
  simpa [nodeValue3692, Sparse.eval] using hc.symm

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

theorem sound3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3694 node3694Labels = Sparse.eval nodeValue3694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3694) = mixedMoment B node3694 node3694Labels := rfl
  simpa [nodeValue3694, Sparse.eval] using hc.symm

theorem sound3698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3698 node3698Labels = Sparse.eval nodeValue3698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3698) = mixedMoment B node3698 node3698Labels := rfl
  simpa [nodeValue3698, Sparse.eval] using hc.symm

theorem sound3699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3699 node3699Labels = Sparse.eval nodeValue3699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3699) = mixedMoment B node3699 node3699Labels := rfl
  simpa [nodeValue3699, Sparse.eval] using hc.symm

theorem sound3703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3703 node3703Labels = Sparse.eval nodeValue3703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3703) = mixedMoment B node3703 node3703Labels := rfl
  simpa [nodeValue3703, Sparse.eval] using hc.symm

theorem sound3705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3705 node3705Labels = Sparse.eval nodeValue3705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3705) = mixedMoment B node3705 node3705Labels := rfl
  simpa [nodeValue3705, Sparse.eval] using hc.symm

theorem sound3706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3706 node3706Labels = Sparse.eval nodeValue3706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3706) = mixedMoment B node3706 node3706Labels := rfl
  simpa [nodeValue3706, Sparse.eval] using hc.symm

theorem sound3708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3708 node3708Labels = Sparse.eval nodeValue3708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3708) = mixedMoment B node3708 node3708Labels := rfl
  simpa [nodeValue3708, Sparse.eval] using hc.symm

theorem sound3709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3709 node3709Labels = Sparse.eval nodeValue3709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3709) = mixedMoment B node3709 node3709Labels := rfl
  simpa [nodeValue3709, Sparse.eval] using hc.symm

theorem sound3710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3710 node3710Labels = Sparse.eval nodeValue3710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3710) = mixedMoment B node3710 node3710Labels := rfl
  simpa [nodeValue3710, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3715 node3715Labels = Sparse.eval nodeValue3715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3715) = mixedMoment B node3715 node3715Labels := rfl
  simpa [nodeValue3715, Sparse.eval] using hc.symm

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3720 node3720Labels = Sparse.eval nodeValue3720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3720) = mixedMoment B node3720 node3720Labels := rfl
  simpa [nodeValue3720, Sparse.eval] using hc.symm

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3722 node3722Labels = Sparse.eval nodeValue3722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3722) = mixedMoment B node3722 node3722Labels := rfl
  simpa [nodeValue3722, Sparse.eval] using hc.symm

theorem sound3723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3723 node3723Labels = Sparse.eval nodeValue3723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3723) = mixedMoment B node3723 node3723Labels := rfl
  simpa [nodeValue3723, Sparse.eval] using hc.symm

theorem sound3724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3724 node3724Labels = Sparse.eval nodeValue3724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3724) = mixedMoment B node3724 node3724Labels := rfl
  simpa [nodeValue3724, Sparse.eval] using hc.symm

theorem sound3730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3730 node3730Labels = Sparse.eval nodeValue3730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3730) = mixedMoment B node3730 node3730Labels := rfl
  simpa [nodeValue3730, Sparse.eval] using hc.symm

theorem sound3731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3731 node3731Labels = Sparse.eval nodeValue3731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3731) = mixedMoment B node3731 node3731Labels := rfl
  simpa [nodeValue3731, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

theorem sound3733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3733 node3733Labels = Sparse.eval nodeValue3733 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3733) = mixedMoment B node3733 node3733Labels := rfl
  simpa [nodeValue3733, Sparse.eval] using hc.symm

theorem sound3755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3755 node3755Labels = Sparse.eval nodeValue3755 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3755) = mixedMoment B node3755 node3755Labels := rfl
  simpa [nodeValue3755, Sparse.eval] using hc.symm

theorem sound3759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3759 node3759Labels = Sparse.eval nodeValue3759 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3759) = mixedMoment B node3759 node3759Labels := rfl
  simpa [nodeValue3759, Sparse.eval] using hc.symm

theorem sound3760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3760 node3760Labels = Sparse.eval nodeValue3760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3760) = mixedMoment B node3760 node3760Labels := rfl
  simpa [nodeValue3760, Sparse.eval] using hc.symm

theorem sound3761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3761 node3761Labels = Sparse.eval nodeValue3761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3761) = mixedMoment B node3761 node3761Labels := rfl
  simpa [nodeValue3761, Sparse.eval] using hc.symm

theorem sound3762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3762 node3762Labels = Sparse.eval nodeValue3762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3762) = mixedMoment B node3762 node3762Labels := rfl
  simpa [nodeValue3762, Sparse.eval] using hc.symm

theorem sound3763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3763 node3763Labels = Sparse.eval nodeValue3763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3763) = mixedMoment B node3763 node3763Labels := rfl
  simpa [nodeValue3763, Sparse.eval] using hc.symm

theorem sound3768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3768 node3768Labels = Sparse.eval nodeValue3768 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3768) = mixedMoment B node3768 node3768Labels := rfl
  simpa [nodeValue3768, Sparse.eval] using hc.symm

theorem sound3772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3772 node3772Labels = Sparse.eval nodeValue3772 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3772) = mixedMoment B node3772 node3772Labels := rfl
  simpa [nodeValue3772, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = 0 := by
  exact mixedMoment_order_one B hB node3806 node3806Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = 0 := by
  exact mixedMoment_order_one B hB node3807 node3807Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = 0 := by
  exact mixedMoment_order_one B hB node3808 node3808Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = 0 := by
  exact mixedMoment_order_one B hB node3816 node3816Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = 0 := by
  exact mixedMoment_order_one B hB node3817 node3817Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

theorem sound3780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3780 node3780Labels = Sparse.eval nodeValue3780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3780) = mixedMoment B node3780 node3780Labels := rfl
  simpa [nodeValue3780, Sparse.eval] using hc.symm

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3782 node3782Labels = Sparse.eval nodeValue3782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3782) = mixedMoment B node3782 node3782Labels := rfl
  simpa [nodeValue3782, Sparse.eval] using hc.symm

theorem sound3783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3783 node3783Labels = Sparse.eval nodeValue3783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3783) = mixedMoment B node3783 node3783Labels := rfl
  simpa [nodeValue3783, Sparse.eval] using hc.symm

theorem sound3786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3786 node3786Labels = Sparse.eval nodeValue3786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3786) = mixedMoment B node3786 node3786Labels := rfl
  simpa [nodeValue3786, Sparse.eval] using hc.symm

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

theorem sound3788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3788 node3788Labels = Sparse.eval nodeValue3788 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3788) = mixedMoment B node3788 node3788Labels := rfl
  simpa [nodeValue3788, Sparse.eval] using hc.symm

theorem sound3789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3789 node3789Labels = Sparse.eval nodeValue3789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3789) = mixedMoment B node3789 node3789Labels := rfl
  simpa [nodeValue3789, Sparse.eval] using hc.symm

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3802 node3802Labels = Sparse.eval nodeValue3802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3802) = mixedMoment B node3802 node3802Labels := rfl
  simpa [nodeValue3802, Sparse.eval] using hc.symm

theorem sound3803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3803 node3803Labels = Sparse.eval nodeValue3803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3803) = mixedMoment B node3803 node3803Labels := rfl
  simpa [nodeValue3803, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

theorem sound3806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = Sparse.eval nodeValue3806 (mixedVector B) := by
  simpa only [nodeValue3806, Sparse.eval_nil] using zero3806 B _hB _hF

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = Sparse.eval nodeValue3808 (mixedVector B) := by
  simpa only [nodeValue3808, Sparse.eval_nil] using zero3808 B _hB _hF

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

theorem sound3817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = Sparse.eval nodeValue3817 (mixedVector B) := by
  simpa only [nodeValue3817, Sparse.eval_nil] using zero3817 B _hB _hF

theorem sound3819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3819 node3819Labels = Sparse.eval nodeValue3819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3819) = mixedMoment B node3819 node3819Labels := rfl
  simpa [nodeValue3819, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1319 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1319 x = (3031883170345451520000 : ℝ) * Sparse.eval nodeValue3517 x := by
  norm_num [reducedTerm1319, nodeValue3517, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1320 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1320 x = (-500927005576101888000 : ℝ) * Sparse.eval nodeValue3519 x := by
  norm_num [reducedTerm1320, nodeValue3519, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1321 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1321 x = (-12294580299389337600000 : ℝ) * Sparse.eval nodeValue3523 x := by
  norm_num [reducedTerm1321, nodeValue3523, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1322 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1322 x = (-1072771597873446912000 : ℝ) * Sparse.eval nodeValue3524 x := by
  norm_num [reducedTerm1322, nodeValue3524, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1323 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1323 x = (-6990515310978662400000 : ℝ) * Sparse.eval nodeValue3525 x := by
  norm_num [reducedTerm1323, nodeValue3525, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1324 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1324 x = (-8846701964077694976000 : ℝ) * Sparse.eval nodeValue3526 x := by
  norm_num [reducedTerm1324, nodeValue3526, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1325 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1325 x = (2431584286271078400000 : ℝ) * Sparse.eval nodeValue3529 x := by
  norm_num [reducedTerm1325, nodeValue3529, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1326 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1326 x = (6558674437762449408000 : ℝ) * Sparse.eval nodeValue3530 x := by
  norm_num [reducedTerm1326, nodeValue3530, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1327 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1327 x = (-1598770106249379840000 : ℝ) * Sparse.eval nodeValue3532 x := by
  norm_num [reducedTerm1327, nodeValue3532, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1328 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1328 x = (-1975281871324446720000 : ℝ) * Sparse.eval nodeValue3533 x := by
  norm_num [reducedTerm1328, nodeValue3533, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1329 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1329 x = (26110149656309268480000 : ℝ) * Sparse.eval nodeValue3534 x := by
  norm_num [reducedTerm1329, nodeValue3534, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1330 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1330 x = (4491472530225364992000 : ℝ) * Sparse.eval nodeValue3535 x := by
  norm_num [reducedTerm1330, nodeValue3535, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1331 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1331 x = (7698731041103413248000 : ℝ) * Sparse.eval nodeValue3537 x := by
  norm_num [reducedTerm1331, nodeValue3537, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1332 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1332 x = (1252704393088598016000 : ℝ) * Sparse.eval nodeValue3538 x := by
  norm_num [reducedTerm1332, nodeValue3538, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1333 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1333 x = (6590198986965909504000 : ℝ) * Sparse.eval nodeValue3539 x := by
  norm_num [reducedTerm1333, nodeValue3539, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1334 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1334 x = (442881254805405696000 : ℝ) * Sparse.eval nodeValue3540 x := by
  norm_num [reducedTerm1334, nodeValue3540, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1335 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1335 x = (-2683554743866687488000 : ℝ) * Sparse.eval nodeValue3541 x := by
  norm_num [reducedTerm1335, nodeValue3541, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1336 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1336 x = (-1438088403369590784000 : ℝ) * Sparse.eval nodeValue3542 x := by
  norm_num [reducedTerm1336, nodeValue3542, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1337 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1337 x = (-3946797413223727104000 : ℝ) * Sparse.eval nodeValue3543 x := by
  norm_num [reducedTerm1337, nodeValue3543, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1338 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1338 x = (-2488508247260528640000 : ℝ) * Sparse.eval nodeValue3544 x := by
  norm_num [reducedTerm1338, nodeValue3544, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1339 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1339 x = (-113253321790586880000 : ℝ) * Sparse.eval nodeValue3547 x := by
  norm_num [reducedTerm1339, nodeValue3547, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1340 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1340 x = (-1028860950356951040000 : ℝ) * Sparse.eval nodeValue3548 x := by
  norm_num [reducedTerm1340, nodeValue3548, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1341 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1341 x = (1255758373127946240000 : ℝ) * Sparse.eval nodeValue3549 x := by
  norm_num [reducedTerm1341, nodeValue3549, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1342 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1342 x = (-1133832859511095296000 : ℝ) * Sparse.eval nodeValue3553 x := by
  norm_num [reducedTerm1342, nodeValue3553, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1343 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1343 x = (-5933039869919232000000 : ℝ) * Sparse.eval nodeValue3554 x := by
  norm_num [reducedTerm1343, nodeValue3554, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1344 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1344 x = (-5743947411554107392000 : ℝ) * Sparse.eval nodeValue3555 x := by
  norm_num [reducedTerm1344, nodeValue3555, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1345 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1345 x = (-1645301575619444736000 : ℝ) * Sparse.eval nodeValue3556 x := by
  norm_num [reducedTerm1345, nodeValue3556, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1346 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1346 x = (900394580334477312000 : ℝ) * Sparse.eval nodeValue3557 x := by
  norm_num [reducedTerm1346, nodeValue3557, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1347 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1347 x = (8704054146298871808000 : ℝ) * Sparse.eval nodeValue3558 x := by
  norm_num [reducedTerm1347, nodeValue3558, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1348 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1348 x = (2987270009704415232000 : ℝ) * Sparse.eval nodeValue3562 x := by
  norm_num [reducedTerm1348, nodeValue3562, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1349 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1349 x = (5653339486845861888000 : ℝ) * Sparse.eval nodeValue3565 x := by
  norm_num [reducedTerm1349, nodeValue3565, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1350 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1350 x = (1962225745433985024000 : ℝ) * Sparse.eval nodeValue3569 x := by
  norm_num [reducedTerm1350, nodeValue3569, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1351 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1351 x = (2433073703307706368000 : ℝ) * Sparse.eval nodeValue3570 x := by
  norm_num [reducedTerm1351, nodeValue3570, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1352 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1352 x = (12926463385317801984000 : ℝ) * Sparse.eval nodeValue3571 x := by
  norm_num [reducedTerm1352, nodeValue3571, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1353 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1353 x = (-16798163909915049984000 : ℝ) * Sparse.eval nodeValue3572 x := by
  norm_num [reducedTerm1353, nodeValue3572, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1354 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1354 x = (19725678159807578112000 : ℝ) * Sparse.eval nodeValue3573 x := by
  norm_num [reducedTerm1354, nodeValue3573, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1355 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1355 x = (4629005356695552000000 : ℝ) * Sparse.eval nodeValue3577 x := by
  norm_num [reducedTerm1355, nodeValue3577, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1356 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1356 x = (13978224602687471616000 : ℝ) * Sparse.eval nodeValue3578 x := by
  norm_num [reducedTerm1356, nodeValue3578, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1357 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1357 x = (4549640633792593920000 : ℝ) * Sparse.eval nodeValue3579 x := by
  norm_num [reducedTerm1357, nodeValue3579, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1358 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1358 x = (831414264535056384000 : ℝ) * Sparse.eval nodeValue3580 x := by
  norm_num [reducedTerm1358, nodeValue3580, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1359 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1359 x = (-220499962681098240000 : ℝ) * Sparse.eval nodeValue3581 x := by
  norm_num [reducedTerm1359, nodeValue3581, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1360 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1360 x = (4158174109630464000000 : ℝ) * Sparse.eval nodeValue3582 x := by
  norm_num [reducedTerm1360, nodeValue3582, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1361 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1361 x = (-11906431827880181760000 : ℝ) * Sparse.eval nodeValue3583 x := by
  norm_num [reducedTerm1361, nodeValue3583, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1362 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1362 x = (29008204646800490496000 : ℝ) * Sparse.eval nodeValue3584 x := by
  norm_num [reducedTerm1362, nodeValue3584, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1363 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1363 x = (1173233126741114880000 : ℝ) * Sparse.eval nodeValue3618 x := by
  norm_num [reducedTerm1363, nodeValue3618, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1364 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1364 x = (-9131775422933237760000 : ℝ) * Sparse.eval nodeValue3619 x := by
  norm_num [reducedTerm1364, nodeValue3619, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1365 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1365 x = (13643436319594905600000 : ℝ) * Sparse.eval nodeValue3622 x := by
  norm_num [reducedTerm1365, nodeValue3622, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1366 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1366 x = (-6320730118534594560000 : ℝ) * Sparse.eval nodeValue3623 x := by
  norm_num [reducedTerm1366, nodeValue3623, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1367 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1367 x = (3684922744987975680000 : ℝ) * Sparse.eval nodeValue3625 x := by
  norm_num [reducedTerm1367, nodeValue3625, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1368 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1368 x = (5131131445562572800000 : ℝ) * Sparse.eval nodeValue3626 x := by
  norm_num [reducedTerm1368, nodeValue3626, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1369 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1369 x = (7417776676181114880000 : ℝ) * Sparse.eval nodeValue3627 x := by
  norm_num [reducedTerm1369, nodeValue3627, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1370 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1370 x = (-6336028725384314880000 : ℝ) * Sparse.eval nodeValue3628 x := by
  norm_num [reducedTerm1370, nodeValue3628, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1371 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1371 x = (-14329743722100817920000 : ℝ) * Sparse.eval nodeValue3629 x := by
  norm_num [reducedTerm1371, nodeValue3629, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1372 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1372 x = (-3609060248797839360000 : ℝ) * Sparse.eval nodeValue3632 x := by
  norm_num [reducedTerm1372, nodeValue3632, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1373 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1373 x = (17665403553650442240000 : ℝ) * Sparse.eval nodeValue3633 x := by
  norm_num [reducedTerm1373, nodeValue3633, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1374 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1374 x = (-6038654768971776000000 : ℝ) * Sparse.eval nodeValue3635 x := by
  norm_num [reducedTerm1374, nodeValue3635, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1375 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1375 x = (-1266335868026880000000 : ℝ) * Sparse.eval nodeValue3636 x := by
  norm_num [reducedTerm1375, nodeValue3636, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1376 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1376 x = (-3558260895488409600000 : ℝ) * Sparse.eval nodeValue3670 x := by
  norm_num [reducedTerm1376, nodeValue3670, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1377 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1377 x = (2856821572837048320000 : ℝ) * Sparse.eval nodeValue3671 x := by
  norm_num [reducedTerm1377, nodeValue3671, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1378 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1378 x = (8029997437000089600000 : ℝ) * Sparse.eval nodeValue3672 x := by
  norm_num [reducedTerm1378, nodeValue3672, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1379 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1379 x = (-2089015568665804800000 : ℝ) * Sparse.eval nodeValue3673 x := by
  norm_num [reducedTerm1379, nodeValue3673, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1380 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1380 x = (-3375760173907968000000 : ℝ) * Sparse.eval nodeValue3674 x := by
  norm_num [reducedTerm1380, nodeValue3674, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1381 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1381 x = (2139241300593868800000 : ℝ) * Sparse.eval nodeValue3676 x := by
  norm_num [reducedTerm1381, nodeValue3676, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1382 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1382 x = (-669848715789926400000 : ℝ) * Sparse.eval nodeValue3685 x := by
  norm_num [reducedTerm1382, nodeValue3685, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1383 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1383 x = (5058598529834680320000 : ℝ) * Sparse.eval nodeValue3689 x := by
  norm_num [reducedTerm1383, nodeValue3689, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1384 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1384 x = (-2714220736148275200000 : ℝ) * Sparse.eval nodeValue3690 x := by
  norm_num [reducedTerm1384, nodeValue3690, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1385 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1385 x = (-5214891424162775040000 : ℝ) * Sparse.eval nodeValue3692 x := by
  norm_num [reducedTerm1385, nodeValue3692, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1386 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1386 x = (-1773350590788403200000 : ℝ) * Sparse.eval nodeValue3693 x := by
  norm_num [reducedTerm1386, nodeValue3693, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1387 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1387 x = (-5315776700851814400000 : ℝ) * Sparse.eval nodeValue3694 x := by
  norm_num [reducedTerm1387, nodeValue3694, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1388 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1388 x = (3611345102733312000000 : ℝ) * Sparse.eval nodeValue3698 x := by
  norm_num [reducedTerm1388, nodeValue3698, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1389 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1389 x = (3293229788164915200000 : ℝ) * Sparse.eval nodeValue3699 x := by
  norm_num [reducedTerm1389, nodeValue3699, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1390 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1390 x = (-6378432071205519360000 : ℝ) * Sparse.eval nodeValue3703 x := by
  norm_num [reducedTerm1390, nodeValue3703, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1391 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1391 x = (8915230341595791360000 : ℝ) * Sparse.eval nodeValue3705 x := by
  norm_num [reducedTerm1391, nodeValue3705, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1392 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1392 x = (-10603132867144581120000 : ℝ) * Sparse.eval nodeValue3706 x := by
  norm_num [reducedTerm1392, nodeValue3706, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1393 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1393 x = (23153419811192832000000 : ℝ) * Sparse.eval nodeValue3708 x := by
  norm_num [reducedTerm1393, nodeValue3708, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1394 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1394 x = (7818430382751744000000 : ℝ) * Sparse.eval nodeValue3709 x := by
  norm_num [reducedTerm1394, nodeValue3709, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1395 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1395 x = (3622287461825249280000 : ℝ) * Sparse.eval nodeValue3710 x := by
  norm_num [reducedTerm1395, nodeValue3710, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1396 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1396 x = (11249654248211742720000 : ℝ) * Sparse.eval nodeValue3715 x := by
  norm_num [reducedTerm1396, nodeValue3715, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1397 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1397 x = (7397988905631744000000 : ℝ) * Sparse.eval nodeValue3719 x := by
  norm_num [reducedTerm1397, nodeValue3719, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1398 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1398 x = (6831804330736680960000 : ℝ) * Sparse.eval nodeValue3720 x := by
  norm_num [reducedTerm1398, nodeValue3720, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1399 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1399 x = (12949195045327994880000 : ℝ) * Sparse.eval nodeValue3721 x := by
  norm_num [reducedTerm1399, nodeValue3721, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1400 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1400 x = (-26217469888567050240000 : ℝ) * Sparse.eval nodeValue3722 x := by
  norm_num [reducedTerm1400, nodeValue3722, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1401 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1401 x = (3090408338022727680000 : ℝ) * Sparse.eval nodeValue3723 x := by
  norm_num [reducedTerm1401, nodeValue3723, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1402 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1402 x = (-12931866039110860800000 : ℝ) * Sparse.eval nodeValue3724 x := by
  norm_num [reducedTerm1402, nodeValue3724, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1403 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1403 x = (498588466060984320000 : ℝ) * Sparse.eval nodeValue3730 x := by
  norm_num [reducedTerm1403, nodeValue3730, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1404 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1404 x = (-4479366205522575360000 : ℝ) * Sparse.eval nodeValue3731 x := by
  norm_num [reducedTerm1404, nodeValue3731, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1405 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1405 x = (-15823981309321543680000 : ℝ) * Sparse.eval nodeValue3732 x := by
  norm_num [reducedTerm1405, nodeValue3732, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1406 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1406 x = (1301788622079590400000 : ℝ) * Sparse.eval nodeValue3733 x := by
  norm_num [reducedTerm1406, nodeValue3733, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1407 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1407 x = (885060905467576320000 : ℝ) * Sparse.eval nodeValue3755 x := by
  norm_num [reducedTerm1407, nodeValue3755, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1408 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1408 x = (-2229127337632333824000 : ℝ) * Sparse.eval nodeValue3759 x := by
  norm_num [reducedTerm1408, nodeValue3759, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1409 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1409 x = (7779502517921906688000 : ℝ) * Sparse.eval nodeValue3760 x := by
  norm_num [reducedTerm1409, nodeValue3760, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1410 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1410 x = (-2581778767834054656000 : ℝ) * Sparse.eval nodeValue3761 x := by
  norm_num [reducedTerm1410, nodeValue3761, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1411 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1411 x = (-3482485535088967680000 : ℝ) * Sparse.eval nodeValue3762 x := by
  norm_num [reducedTerm1411, nodeValue3762, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1412 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1412 x = (722635406229897216000 : ℝ) * Sparse.eval nodeValue3763 x := by
  norm_num [reducedTerm1412, nodeValue3763, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1413 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1413 x = (-629877478875660288000 : ℝ) * Sparse.eval nodeValue3768 x := by
  norm_num [reducedTerm1413, nodeValue3768, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1414 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1414 x = (-1457354951397015552000 : ℝ) * Sparse.eval nodeValue3772 x := by
  norm_num [reducedTerm1414, nodeValue3772, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1415 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1415 x = (-23279727428871782400000 : ℝ) * Sparse.eval nodeValue3779 x := by
  norm_num [reducedTerm1415, nodeValue3779, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1416 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1416 x = (4493455024472064000000 : ℝ) * Sparse.eval nodeValue3780 x := by
  norm_num [reducedTerm1416, nodeValue3780, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1417 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1417 x = (1745085365617950720000 : ℝ) * Sparse.eval nodeValue3781 x := by
  norm_num [reducedTerm1417, nodeValue3781, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1418 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1418 x = (-4452974806184755200000 : ℝ) * Sparse.eval nodeValue3782 x := by
  norm_num [reducedTerm1418, nodeValue3782, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1419 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1419 x = (1278536233166438400000 : ℝ) * Sparse.eval nodeValue3783 x := by
  norm_num [reducedTerm1419, nodeValue3783, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1420 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1420 x = (5625894605263994880000 : ℝ) * Sparse.eval nodeValue3786 x := by
  norm_num [reducedTerm1420, nodeValue3786, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1421 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1421 x = (-16392111811529932800000 : ℝ) * Sparse.eval nodeValue3787 x := by
  norm_num [reducedTerm1421, nodeValue3787, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1422 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1422 x = (2738043209843343360000 : ℝ) * Sparse.eval nodeValue3788 x := by
  norm_num [reducedTerm1422, nodeValue3788, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1423 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1423 x = (1441864010724802560000 : ℝ) * Sparse.eval nodeValue3789 x := by
  norm_num [reducedTerm1423, nodeValue3789, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1424 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1424 x = (26650108359770112000000 : ℝ) * Sparse.eval nodeValue3800 x := by
  norm_num [reducedTerm1424, nodeValue3800, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1425 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1425 x = (-13178290840890900480000 : ℝ) * Sparse.eval nodeValue3801 x := by
  norm_num [reducedTerm1425, nodeValue3801, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1426 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1426 x = (-5516271414691430400000 : ℝ) * Sparse.eval nodeValue3802 x := by
  norm_num [reducedTerm1426, nodeValue3802, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1427 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1427 x = (-6944207726412988416000 : ℝ) * Sparse.eval nodeValue3803 x := by
  norm_num [reducedTerm1427, nodeValue3803, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1428 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1428 x = (5260225873509089280000 : ℝ) * Sparse.eval nodeValue3805 x := by
  norm_num [reducedTerm1428, nodeValue3805, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1429 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1429 x = (669848715789926400000 : ℝ) * Sparse.eval nodeValue3806 x := by
  norm_num [reducedTerm1429, nodeValue3806, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1430 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1430 x = (42601625103803351040000 : ℝ) * Sparse.eval nodeValue3807 x := by
  norm_num [reducedTerm1430, nodeValue3807, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1431 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1431 x = (9955200277551513600000 : ℝ) * Sparse.eval nodeValue3808 x := by
  norm_num [reducedTerm1431, nodeValue3808, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1432 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1432 x = (-28544727109663457280000 : ℝ) * Sparse.eval nodeValue3809 x := by
  norm_num [reducedTerm1432, nodeValue3809, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1433 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1433 x = (10099373456256860160000 : ℝ) * Sparse.eval nodeValue3812 x := by
  norm_num [reducedTerm1433, nodeValue3812, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1434 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1434 x = (-31930167407745761280000 : ℝ) * Sparse.eval nodeValue3813 x := by
  norm_num [reducedTerm1434, nodeValue3813, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1435 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1435 x = (-18142276456326758400000 : ℝ) * Sparse.eval nodeValue3814 x := by
  norm_num [reducedTerm1435, nodeValue3814, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1436 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1436 x = (-1776998510349189120000 : ℝ) * Sparse.eval nodeValue3816 x := by
  norm_num [reducedTerm1436, nodeValue3816, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1437 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1437 x = (24758844578608250880000 : ℝ) * Sparse.eval nodeValue3817 x := by
  norm_num [reducedTerm1437, nodeValue3817, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1438 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1438 x = (2089015568665804800000 : ℝ) * Sparse.eval nodeValue3819 x := by
  norm_num [reducedTerm1438, nodeValue3819, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1316Check : reducedMerge1316 = Integer.Sparse.mergeBy masterLess reducedTerm1320 reducedTerm1321 := by decide +kernel

theorem reducedMerge1317Check : reducedMerge1317 = Integer.Sparse.mergeBy masterLess reducedTerm1319 reducedMerge1316 := by decide +kernel

theorem reducedMerge1318Check : reducedMerge1318 = Integer.Sparse.mergeBy masterLess reducedTerm1322 reducedTerm1323 := by decide +kernel

theorem reducedMerge1319Check : reducedMerge1319 = Integer.Sparse.mergeBy masterLess reducedTerm1324 reducedTerm1325 := by decide +kernel

theorem reducedMerge1320Check : reducedMerge1320 = Integer.Sparse.mergeBy masterLess reducedMerge1318 reducedMerge1319 := by decide +kernel

theorem reducedMerge1321Check : reducedMerge1321 = Integer.Sparse.mergeBy masterLess reducedMerge1317 reducedMerge1320 := by decide +kernel

theorem reducedMerge1322Check : reducedMerge1322 = Integer.Sparse.mergeBy masterLess reducedTerm1326 reducedTerm1327 := by decide +kernel

theorem reducedMerge1323Check : reducedMerge1323 = Integer.Sparse.mergeBy masterLess reducedTerm1328 reducedTerm1329 := by decide +kernel

theorem reducedMerge1324Check : reducedMerge1324 = Integer.Sparse.mergeBy masterLess reducedMerge1322 reducedMerge1323 := by decide +kernel

theorem reducedMerge1325Check : reducedMerge1325 = Integer.Sparse.mergeBy masterLess reducedTerm1330 reducedTerm1331 := by decide +kernel

theorem reducedMerge1326Check : reducedMerge1326 = Integer.Sparse.mergeBy masterLess reducedTerm1332 reducedTerm1333 := by decide +kernel

theorem reducedMerge1327Check : reducedMerge1327 = Integer.Sparse.mergeBy masterLess reducedMerge1325 reducedMerge1326 := by decide +kernel

theorem reducedMerge1328Check : reducedMerge1328 = Integer.Sparse.mergeBy masterLess reducedMerge1324 reducedMerge1327 := by decide +kernel

theorem reducedMerge1329Check : reducedMerge1329 = Integer.Sparse.mergeBy masterLess reducedMerge1321 reducedMerge1328 := by decide +kernel

theorem reducedMerge1330Check : reducedMerge1330 = Integer.Sparse.mergeBy masterLess reducedTerm1335 reducedTerm1336 := by decide +kernel

theorem reducedMerge1331Check : reducedMerge1331 = Integer.Sparse.mergeBy masterLess reducedTerm1334 reducedMerge1330 := by decide +kernel

theorem reducedMerge1332Check : reducedMerge1332 = Integer.Sparse.mergeBy masterLess reducedTerm1337 reducedTerm1338 := by decide +kernel

theorem reducedMerge1333Check : reducedMerge1333 = Integer.Sparse.mergeBy masterLess reducedTerm1339 reducedTerm1340 := by decide +kernel

theorem reducedMerge1334Check : reducedMerge1334 = Integer.Sparse.mergeBy masterLess reducedMerge1332 reducedMerge1333 := by decide +kernel

theorem reducedMerge1335Check : reducedMerge1335 = Integer.Sparse.mergeBy masterLess reducedMerge1331 reducedMerge1334 := by decide +kernel

theorem reducedMerge1336Check : reducedMerge1336 = Integer.Sparse.mergeBy masterLess reducedTerm1341 reducedTerm1342 := by decide +kernel

theorem reducedMerge1337Check : reducedMerge1337 = Integer.Sparse.mergeBy masterLess reducedTerm1343 reducedTerm1344 := by decide +kernel

theorem reducedMerge1338Check : reducedMerge1338 = Integer.Sparse.mergeBy masterLess reducedMerge1336 reducedMerge1337 := by decide +kernel

theorem reducedMerge1339Check : reducedMerge1339 = Integer.Sparse.mergeBy masterLess reducedTerm1345 reducedTerm1346 := by decide +kernel

theorem reducedMerge1340Check : reducedMerge1340 = Integer.Sparse.mergeBy masterLess reducedTerm1347 reducedTerm1348 := by decide +kernel

theorem reducedMerge1341Check : reducedMerge1341 = Integer.Sparse.mergeBy masterLess reducedMerge1339 reducedMerge1340 := by decide +kernel

theorem reducedMerge1342Check : reducedMerge1342 = Integer.Sparse.mergeBy masterLess reducedMerge1338 reducedMerge1341 := by decide +kernel

theorem reducedMerge1343Check : reducedMerge1343 = Integer.Sparse.mergeBy masterLess reducedMerge1335 reducedMerge1342 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1344Check : reducedMerge1344 = Integer.Sparse.mergeBy masterLess reducedMerge1329 reducedMerge1343 := by decide +kernel

theorem reducedMerge1345Check : reducedMerge1345 = Integer.Sparse.mergeBy masterLess reducedTerm1350 reducedTerm1351 := by decide +kernel

theorem reducedMerge1346Check : reducedMerge1346 = Integer.Sparse.mergeBy masterLess reducedTerm1349 reducedMerge1345 := by decide +kernel

theorem reducedMerge1347Check : reducedMerge1347 = Integer.Sparse.mergeBy masterLess reducedTerm1352 reducedTerm1353 := by decide +kernel

theorem reducedMerge1348Check : reducedMerge1348 = Integer.Sparse.mergeBy masterLess reducedTerm1354 reducedTerm1355 := by decide +kernel

theorem reducedMerge1349Check : reducedMerge1349 = Integer.Sparse.mergeBy masterLess reducedMerge1347 reducedMerge1348 := by decide +kernel

theorem reducedMerge1350Check : reducedMerge1350 = Integer.Sparse.mergeBy masterLess reducedMerge1346 reducedMerge1349 := by decide +kernel

theorem reducedMerge1351Check : reducedMerge1351 = Integer.Sparse.mergeBy masterLess reducedTerm1356 reducedTerm1357 := by decide +kernel

theorem reducedMerge1352Check : reducedMerge1352 = Integer.Sparse.mergeBy masterLess reducedTerm1358 reducedTerm1359 := by decide +kernel

theorem reducedMerge1353Check : reducedMerge1353 = Integer.Sparse.mergeBy masterLess reducedMerge1351 reducedMerge1352 := by decide +kernel

theorem reducedMerge1354Check : reducedMerge1354 = Integer.Sparse.mergeBy masterLess reducedTerm1360 reducedTerm1361 := by decide +kernel

theorem reducedMerge1355Check : reducedMerge1355 = Integer.Sparse.mergeBy masterLess reducedTerm1362 reducedTerm1363 := by decide +kernel

theorem reducedMerge1356Check : reducedMerge1356 = Integer.Sparse.mergeBy masterLess reducedMerge1354 reducedMerge1355 := by decide +kernel

theorem reducedMerge1357Check : reducedMerge1357 = Integer.Sparse.mergeBy masterLess reducedMerge1353 reducedMerge1356 := by decide +kernel

theorem reducedMerge1358Check : reducedMerge1358 = Integer.Sparse.mergeBy masterLess reducedMerge1350 reducedMerge1357 := by decide +kernel

theorem reducedMerge1359Check : reducedMerge1359 = Integer.Sparse.mergeBy masterLess reducedTerm1365 reducedTerm1366 := by decide +kernel

theorem reducedMerge1360Check : reducedMerge1360 = Integer.Sparse.mergeBy masterLess reducedTerm1364 reducedMerge1359 := by decide +kernel

theorem reducedMerge1361Check : reducedMerge1361 = Integer.Sparse.mergeBy masterLess reducedTerm1367 reducedTerm1368 := by decide +kernel

theorem reducedMerge1362Check : reducedMerge1362 = Integer.Sparse.mergeBy masterLess reducedTerm1369 reducedTerm1370 := by decide +kernel

theorem reducedMerge1363Check : reducedMerge1363 = Integer.Sparse.mergeBy masterLess reducedMerge1361 reducedMerge1362 := by decide +kernel

theorem reducedMerge1364Check : reducedMerge1364 = Integer.Sparse.mergeBy masterLess reducedMerge1360 reducedMerge1363 := by decide +kernel

theorem reducedMerge1365Check : reducedMerge1365 = Integer.Sparse.mergeBy masterLess reducedTerm1371 reducedTerm1372 := by decide +kernel

theorem reducedMerge1366Check : reducedMerge1366 = Integer.Sparse.mergeBy masterLess reducedTerm1373 reducedTerm1374 := by decide +kernel

theorem reducedMerge1367Check : reducedMerge1367 = Integer.Sparse.mergeBy masterLess reducedMerge1365 reducedMerge1366 := by decide +kernel

theorem reducedMerge1368Check : reducedMerge1368 = Integer.Sparse.mergeBy masterLess reducedTerm1375 reducedTerm1376 := by decide +kernel

theorem reducedMerge1369Check : reducedMerge1369 = Integer.Sparse.mergeBy masterLess reducedTerm1377 reducedTerm1378 := by decide +kernel

theorem reducedMerge1370Check : reducedMerge1370 = Integer.Sparse.mergeBy masterLess reducedMerge1368 reducedMerge1369 := by decide +kernel

theorem reducedMerge1371Check : reducedMerge1371 = Integer.Sparse.mergeBy masterLess reducedMerge1367 reducedMerge1370 := by decide +kernel

theorem reducedMerge1372Check : reducedMerge1372 = Integer.Sparse.mergeBy masterLess reducedMerge1364 reducedMerge1371 := by decide +kernel

theorem reducedMerge1373Check : reducedMerge1373 = Integer.Sparse.mergeBy masterLess reducedMerge1358 reducedMerge1372 := by decide +kernel

theorem reducedMerge1374Check : reducedMerge1374 = Integer.Sparse.mergeBy masterLess reducedMerge1344 reducedMerge1373 := by decide +kernel

theorem reducedMerge1375Check : reducedMerge1375 = Integer.Sparse.mergeBy masterLess reducedTerm1380 reducedTerm1381 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1376Check : reducedMerge1376 = Integer.Sparse.mergeBy masterLess reducedTerm1379 reducedMerge1375 := by decide +kernel

theorem reducedMerge1377Check : reducedMerge1377 = Integer.Sparse.mergeBy masterLess reducedTerm1382 reducedTerm1383 := by decide +kernel

theorem reducedMerge1378Check : reducedMerge1378 = Integer.Sparse.mergeBy masterLess reducedTerm1384 reducedTerm1385 := by decide +kernel

theorem reducedMerge1379Check : reducedMerge1379 = Integer.Sparse.mergeBy masterLess reducedMerge1377 reducedMerge1378 := by decide +kernel

theorem reducedMerge1380Check : reducedMerge1380 = Integer.Sparse.mergeBy masterLess reducedMerge1376 reducedMerge1379 := by decide +kernel

theorem reducedMerge1381Check : reducedMerge1381 = Integer.Sparse.mergeBy masterLess reducedTerm1386 reducedTerm1387 := by decide +kernel

theorem reducedMerge1382Check : reducedMerge1382 = Integer.Sparse.mergeBy masterLess reducedTerm1388 reducedTerm1389 := by decide +kernel

theorem reducedMerge1383Check : reducedMerge1383 = Integer.Sparse.mergeBy masterLess reducedMerge1381 reducedMerge1382 := by decide +kernel

theorem reducedMerge1384Check : reducedMerge1384 = Integer.Sparse.mergeBy masterLess reducedTerm1390 reducedTerm1391 := by decide +kernel

theorem reducedMerge1385Check : reducedMerge1385 = Integer.Sparse.mergeBy masterLess reducedTerm1392 reducedTerm1393 := by decide +kernel

theorem reducedMerge1386Check : reducedMerge1386 = Integer.Sparse.mergeBy masterLess reducedMerge1384 reducedMerge1385 := by decide +kernel

theorem reducedMerge1387Check : reducedMerge1387 = Integer.Sparse.mergeBy masterLess reducedMerge1383 reducedMerge1386 := by decide +kernel

theorem reducedMerge1388Check : reducedMerge1388 = Integer.Sparse.mergeBy masterLess reducedMerge1380 reducedMerge1387 := by decide +kernel

theorem reducedMerge1389Check : reducedMerge1389 = Integer.Sparse.mergeBy masterLess reducedTerm1395 reducedTerm1396 := by decide +kernel

theorem reducedMerge1390Check : reducedMerge1390 = Integer.Sparse.mergeBy masterLess reducedTerm1394 reducedMerge1389 := by decide +kernel

theorem reducedMerge1391Check : reducedMerge1391 = Integer.Sparse.mergeBy masterLess reducedTerm1397 reducedTerm1398 := by decide +kernel

theorem reducedMerge1392Check : reducedMerge1392 = Integer.Sparse.mergeBy masterLess reducedTerm1399 reducedTerm1400 := by decide +kernel

theorem reducedMerge1393Check : reducedMerge1393 = Integer.Sparse.mergeBy masterLess reducedMerge1391 reducedMerge1392 := by decide +kernel

theorem reducedMerge1394Check : reducedMerge1394 = Integer.Sparse.mergeBy masterLess reducedMerge1390 reducedMerge1393 := by decide +kernel

theorem reducedMerge1395Check : reducedMerge1395 = Integer.Sparse.mergeBy masterLess reducedTerm1401 reducedTerm1402 := by decide +kernel

theorem reducedMerge1396Check : reducedMerge1396 = Integer.Sparse.mergeBy masterLess reducedTerm1403 reducedTerm1404 := by decide +kernel

theorem reducedMerge1397Check : reducedMerge1397 = Integer.Sparse.mergeBy masterLess reducedMerge1395 reducedMerge1396 := by decide +kernel

theorem reducedMerge1398Check : reducedMerge1398 = Integer.Sparse.mergeBy masterLess reducedTerm1405 reducedTerm1406 := by decide +kernel

theorem reducedMerge1399Check : reducedMerge1399 = Integer.Sparse.mergeBy masterLess reducedTerm1407 reducedTerm1408 := by decide +kernel

theorem reducedMerge1400Check : reducedMerge1400 = Integer.Sparse.mergeBy masterLess reducedMerge1398 reducedMerge1399 := by decide +kernel

theorem reducedMerge1401Check : reducedMerge1401 = Integer.Sparse.mergeBy masterLess reducedMerge1397 reducedMerge1400 := by decide +kernel

theorem reducedMerge1402Check : reducedMerge1402 = Integer.Sparse.mergeBy masterLess reducedMerge1394 reducedMerge1401 := by decide +kernel

theorem reducedMerge1403Check : reducedMerge1403 = Integer.Sparse.mergeBy masterLess reducedMerge1388 reducedMerge1402 := by decide +kernel

theorem reducedMerge1404Check : reducedMerge1404 = Integer.Sparse.mergeBy masterLess reducedTerm1410 reducedTerm1411 := by decide +kernel

theorem reducedMerge1405Check : reducedMerge1405 = Integer.Sparse.mergeBy masterLess reducedTerm1409 reducedMerge1404 := by decide +kernel

theorem reducedMerge1406Check : reducedMerge1406 = Integer.Sparse.mergeBy masterLess reducedTerm1412 reducedTerm1413 := by decide +kernel

theorem reducedMerge1407Check : reducedMerge1407 = Integer.Sparse.mergeBy masterLess reducedTerm1414 reducedTerm1415 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1408Check : reducedMerge1408 = Integer.Sparse.mergeBy masterLess reducedMerge1406 reducedMerge1407 := by decide +kernel

theorem reducedMerge1409Check : reducedMerge1409 = Integer.Sparse.mergeBy masterLess reducedMerge1405 reducedMerge1408 := by decide +kernel

theorem reducedMerge1410Check : reducedMerge1410 = Integer.Sparse.mergeBy masterLess reducedTerm1416 reducedTerm1417 := by decide +kernel

theorem reducedMerge1411Check : reducedMerge1411 = Integer.Sparse.mergeBy masterLess reducedTerm1418 reducedTerm1419 := by decide +kernel

theorem reducedMerge1412Check : reducedMerge1412 = Integer.Sparse.mergeBy masterLess reducedMerge1410 reducedMerge1411 := by decide +kernel

theorem reducedMerge1413Check : reducedMerge1413 = Integer.Sparse.mergeBy masterLess reducedTerm1420 reducedTerm1421 := by decide +kernel

theorem reducedMerge1414Check : reducedMerge1414 = Integer.Sparse.mergeBy masterLess reducedTerm1422 reducedTerm1423 := by decide +kernel

theorem reducedMerge1415Check : reducedMerge1415 = Integer.Sparse.mergeBy masterLess reducedMerge1413 reducedMerge1414 := by decide +kernel

theorem reducedMerge1416Check : reducedMerge1416 = Integer.Sparse.mergeBy masterLess reducedMerge1412 reducedMerge1415 := by decide +kernel

theorem reducedMerge1417Check : reducedMerge1417 = Integer.Sparse.mergeBy masterLess reducedMerge1409 reducedMerge1416 := by decide +kernel

theorem reducedMerge1418Check : reducedMerge1418 = Integer.Sparse.mergeBy masterLess reducedTerm1425 reducedTerm1426 := by decide +kernel

theorem reducedMerge1419Check : reducedMerge1419 = Integer.Sparse.mergeBy masterLess reducedTerm1424 reducedMerge1418 := by decide +kernel

theorem reducedMerge1420Check : reducedMerge1420 = Integer.Sparse.mergeBy masterLess reducedTerm1427 reducedTerm1428 := by decide +kernel

theorem reducedMerge1421Check : reducedMerge1421 = Integer.Sparse.mergeBy masterLess reducedTerm1429 reducedTerm1430 := by decide +kernel

theorem reducedMerge1422Check : reducedMerge1422 = Integer.Sparse.mergeBy masterLess reducedMerge1420 reducedMerge1421 := by decide +kernel

theorem reducedMerge1423Check : reducedMerge1423 = Integer.Sparse.mergeBy masterLess reducedMerge1419 reducedMerge1422 := by decide +kernel

theorem reducedMerge1424Check : reducedMerge1424 = Integer.Sparse.mergeBy masterLess reducedTerm1431 reducedTerm1432 := by decide +kernel

theorem reducedMerge1425Check : reducedMerge1425 = Integer.Sparse.mergeBy masterLess reducedTerm1433 reducedTerm1434 := by decide +kernel

theorem reducedMerge1426Check : reducedMerge1426 = Integer.Sparse.mergeBy masterLess reducedMerge1424 reducedMerge1425 := by decide +kernel

theorem reducedMerge1427Check : reducedMerge1427 = Integer.Sparse.mergeBy masterLess reducedTerm1435 reducedTerm1436 := by decide +kernel

theorem reducedMerge1428Check : reducedMerge1428 = Integer.Sparse.mergeBy masterLess reducedTerm1437 reducedTerm1438 := by decide +kernel

theorem reducedMerge1429Check : reducedMerge1429 = Integer.Sparse.mergeBy masterLess reducedMerge1427 reducedMerge1428 := by decide +kernel

theorem reducedMerge1430Check : reducedMerge1430 = Integer.Sparse.mergeBy masterLess reducedMerge1426 reducedMerge1429 := by decide +kernel

theorem reducedMerge1431Check : reducedMerge1431 = Integer.Sparse.mergeBy masterLess reducedMerge1423 reducedMerge1430 := by decide +kernel

theorem reducedMerge1432Check : reducedMerge1432 = Integer.Sparse.mergeBy masterLess reducedMerge1417 reducedMerge1431 := by decide +kernel

theorem reducedMerge1433Check : reducedMerge1433 = Integer.Sparse.mergeBy masterLess reducedMerge1403 reducedMerge1432 := by decide +kernel

theorem reducedMerge1434Check : reducedMerge1434 = Integer.Sparse.mergeBy masterLess reducedMerge1374 reducedMerge1433 := by decide +kernel

theorem reducedMerge1435Check : reducedMerge1435 = Integer.Sparse.mergeBy masterLess reducedMerge1315 reducedMerge1434 := by decide +kernel

theorem reducedMerge1436Check : reducedMerge1436 = Integer.Sparse.mergeBy masterLess reducedMerge1196 reducedMerge1435 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1319 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1319 (originalVector B) := by
  rw [reducedTermArithmetic1319, ← sound3517 B hB hF]
  change (3031883170345451520000 : ℝ) * mixedMoment B node3517 node3517Labels =
    (37623398400 : ℝ) * ((80585042800 : ℝ) * mixedMoment B node3517 node3517Labels + 0)
  ring

theorem reducedTermEval1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1320 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1320 (originalVector B) := by
  rw [reducedTermArithmetic1320, ← sound3519 B hB hF]
  change (-500927005576101888000 : ℝ) * mixedMoment B node3519 node3519Labels =
    (37623398400 : ℝ) * (((-13314241320 : ℤ) : ℝ) * mixedMoment B node3519 node3519Labels + 0)
  ring

theorem reducedTermEval1321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1321 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1321 (originalVector B) := by
  rw [reducedTermArithmetic1321, ← sound3523 B hB hF]
  change (-12294580299389337600000 : ℝ) * mixedMoment B node3523 node3523Labels =
    (37623398400 : ℝ) * (((-326780164000 : ℤ) : ℝ) * mixedMoment B node3523 node3523Labels + 0)
  ring

theorem reducedTermEval1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1322 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1322 (originalVector B) := by
  rw [reducedTermArithmetic1322, ← sound3524 B hB hF]
  change (-1072771597873446912000 : ℝ) * mixedMoment B node3524 node3524Labels =
    (37623398400 : ℝ) * (((-28513415680 : ℤ) : ℝ) * mixedMoment B node3524 node3524Labels + 0)
  ring

theorem reducedTermEval1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1323 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1323 (originalVector B) := by
  rw [reducedTermArithmetic1323, ← sound3525 B hB hF]
  change (-6990515310978662400000 : ℝ) * mixedMoment B node3525 node3525Labels =
    (37623398400 : ℝ) * (((-185802336000 : ℤ) : ℝ) * mixedMoment B node3525 node3525Labels + 0)
  ring

theorem reducedTermEval1324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1324 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1324 (originalVector B) := by
  rw [reducedTermArithmetic1324, ← sound3526 B hB hF]
  change (-8846701964077694976000 : ℝ) * mixedMoment B node3526 node3526Labels =
    (37623398400 : ℝ) * (((-235138300640 : ℤ) : ℝ) * mixedMoment B node3526 node3526Labels + 0)
  ring

theorem reducedTermEval1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1325 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1325 (originalVector B) := by
  rw [reducedTermArithmetic1325, ← sound3529 B hB hF]
  change (2431584286271078400000 : ℝ) * mixedMoment B node3529 node3529Labels =
    (37623398400 : ℝ) * ((64629576000 : ℝ) * mixedMoment B node3529 node3529Labels + 0)
  ring

theorem reducedTermEval1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1326 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1326 (originalVector B) := by
  rw [reducedTermArithmetic1326, ← sound3530 B hB hF]
  change (6558674437762449408000 : ℝ) * mixedMoment B node3530 node3530Labels =
    (37623398400 : ℝ) * ((174324349120 : ℝ) * mixedMoment B node3530 node3530Labels + 0)
  ring

theorem reducedTermEval1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1327 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1327 (originalVector B) := by
  rw [reducedTermArithmetic1327, ← sound3532 B hB hF]
  change (-1598770106249379840000 : ℝ) * mixedMoment B node3532 node3532Labels =
    (37623398400 : ℝ) * (((-42494037600 : ℤ) : ℝ) * mixedMoment B node3532 node3532Labels + 0)
  ring

theorem reducedTermEval1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1328 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1328 (originalVector B) := by
  rw [reducedTermArithmetic1328, ← sound3533 B hB hF]
  change (-1975281871324446720000 : ℝ) * mixedMoment B node3533 node3533Labels =
    (37623398400 : ℝ) * (((-52501420800 : ℤ) : ℝ) * mixedMoment B node3533 node3533Labels + 0)
  ring

theorem reducedTermEval1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1329 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1329 (originalVector B) := by
  rw [reducedTermArithmetic1329, ← sound3534 B hB hF]
  change (26110149656309268480000 : ℝ) * mixedMoment B node3534 node3534Labels =
    (37623398400 : ℝ) * ((693987007200 : ℝ) * mixedMoment B node3534 node3534Labels + 0)
  ring

theorem reducedTermEval1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1330 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1330 (originalVector B) := by
  rw [reducedTermArithmetic1330, ← sound3535 B hB hF]
  change (4491472530225364992000 : ℝ) * mixedMoment B node3535 node3535Labels =
    (37623398400 : ℝ) * ((119379766880 : ℝ) * mixedMoment B node3535 node3535Labels + 0)
  ring

theorem reducedTermEval1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1331 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1331 (originalVector B) := by
  rw [reducedTermArithmetic1331, ← sound3537 B hB hF]
  change (7698731041103413248000 : ℝ) * mixedMoment B node3537 node3537Labels =
    (37623398400 : ℝ) * ((204626146720 : ℝ) * mixedMoment B node3537 node3537Labels + 0)
  ring

theorem reducedTermEval1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1332 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1332 (originalVector B) := by
  rw [reducedTermArithmetic1332, ← sound3538 B hB hF]
  change (1252704393088598016000 : ℝ) * mixedMoment B node3538 node3538Labels =
    (37623398400 : ℝ) * ((33295886240 : ℝ) * mixedMoment B node3538 node3538Labels + 0)
  ring

theorem reducedTermEval1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1333 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1333 (originalVector B) := by
  rw [reducedTermArithmetic1333, ← sound3539 B hB hF]
  change (6590198986965909504000 : ℝ) * mixedMoment B node3539 node3539Labels =
    (37623398400 : ℝ) * ((175162246560 : ℝ) * mixedMoment B node3539 node3539Labels + 0)
  ring

theorem reducedTermEval1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1334 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1334 (originalVector B) := by
  rw [reducedTermArithmetic1334, ← sound3540 B hB hF]
  change (442881254805405696000 : ℝ) * mixedMoment B node3540 node3540Labels =
    (37623398400 : ℝ) * ((11771431440 : ℝ) * mixedMoment B node3540 node3540Labels + 0)
  ring

theorem reducedTermEval1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1335 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1335 (originalVector B) := by
  rw [reducedTermArithmetic1335, ← sound3541 B hB hF]
  change (-2683554743866687488000 : ℝ) * mixedMoment B node3541 node3541Labels =
    (37623398400 : ℝ) * (((-71326750320 : ℤ) : ℝ) * mixedMoment B node3541 node3541Labels + 0)
  ring

theorem reducedTermEval1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1336 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1336 (originalVector B) := by
  rw [reducedTermArithmetic1336, ← sound3542 B hB hF]
  change (-1438088403369590784000 : ℝ) * mixedMoment B node3542 node3542Labels =
    (37623398400 : ℝ) * (((-38223245760 : ℤ) : ℝ) * mixedMoment B node3542 node3542Labels + 0)
  ring

theorem reducedTermEval1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1337 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1337 (originalVector B) := by
  rw [reducedTermArithmetic1337, ← sound3543 B hB hF]
  change (-3946797413223727104000 : ℝ) * mixedMoment B node3543 node3543Labels =
    (37623398400 : ℝ) * (((-104902735560 : ℤ) : ℝ) * mixedMoment B node3543 node3543Labels + 0)
  ring

theorem reducedTermEval1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1338 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1338 (originalVector B) := by
  rw [reducedTermArithmetic1338, ← sound3544 B hB hF]
  change (-2488508247260528640000 : ℝ) * mixedMoment B node3544 node3544Labels =
    (37623398400 : ℝ) * (((-66142569600 : ℤ) : ℝ) * mixedMoment B node3544 node3544Labels + 0)
  ring

theorem reducedTermEval1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1339 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1339 (originalVector B) := by
  rw [reducedTermArithmetic1339, ← sound3547 B hB hF]
  change (-113253321790586880000 : ℝ) * mixedMoment B node3547 node3547Labels =
    (37623398400 : ℝ) * (((-3010183200 : ℤ) : ℝ) * mixedMoment B node3547 node3547Labels + 0)
  ring

theorem reducedTermEval1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1340 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1340 (originalVector B) := by
  rw [reducedTermArithmetic1340, ← sound3548 B hB hF]
  change (-1028860950356951040000 : ℝ) * mixedMoment B node3548 node3548Labels =
    (37623398400 : ℝ) * (((-27346305600 : ℤ) : ℝ) * mixedMoment B node3548 node3548Labels + 0)
  ring

theorem reducedTermEval1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1341 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1341 (originalVector B) := by
  rw [reducedTermArithmetic1341, ← sound3549 B hB hF]
  change (1255758373127946240000 : ℝ) * mixedMoment B node3549 node3549Labels =
    (37623398400 : ℝ) * ((33377058600 : ℝ) * mixedMoment B node3549 node3549Labels + 0)
  ring

theorem reducedTermEval1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1342 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1342 (originalVector B) := by
  rw [reducedTermArithmetic1342, ← sound3553 B hB hF]
  change (-1133832859511095296000 : ℝ) * mixedMoment B node3553 node3553Labels =
    (37623398400 : ℝ) * (((-30136375440 : ℤ) : ℝ) * mixedMoment B node3553 node3553Labels + 0)
  ring

theorem reducedTermEval1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1343 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1343 (originalVector B) := by
  rw [reducedTermArithmetic1343, ← sound3554 B hB hF]
  change (-5933039869919232000000 : ℝ) * mixedMoment B node3554 node3554Labels =
    (37623398400 : ℝ) * (((-157695480000 : ℤ) : ℝ) * mixedMoment B node3554 node3554Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1344 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1344 (originalVector B) := by
  rw [reducedTermArithmetic1344, ← sound3555 B hB hF]
  change (-5743947411554107392000 : ℝ) * mixedMoment B node3555 node3555Labels =
    (37623398400 : ℝ) * (((-152669552880 : ℤ) : ℝ) * mixedMoment B node3555 node3555Labels + 0)
  ring

theorem reducedTermEval1345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1345 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1345 (originalVector B) := by
  rw [reducedTermArithmetic1345, ← sound3556 B hB hF]
  change (-1645301575619444736000 : ℝ) * mixedMoment B node3556 node3556Labels =
    (37623398400 : ℝ) * (((-43730807040 : ℤ) : ℝ) * mixedMoment B node3556 node3556Labels + 0)
  ring

theorem reducedTermEval1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1346 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1346 (originalVector B) := by
  rw [reducedTermArithmetic1346, ← sound3557 B hB hF]
  change (900394580334477312000 : ℝ) * mixedMoment B node3557 node3557Labels =
    (37623398400 : ℝ) * ((23931771680 : ℝ) * mixedMoment B node3557 node3557Labels + 0)
  ring

theorem reducedTermEval1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1347 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1347 (originalVector B) := by
  rw [reducedTermArithmetic1347, ← sound3558 B hB hF]
  change (8704054146298871808000 : ℝ) * mixedMoment B node3558 node3558Labels =
    (37623398400 : ℝ) * ((231346835120 : ℝ) * mixedMoment B node3558 node3558Labels + 0)
  ring

theorem reducedTermEval1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1348 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1348 (originalVector B) := by
  rw [reducedTermArithmetic1348, ← sound3562 B hB hF]
  change (2987270009704415232000 : ℝ) * mixedMoment B node3562 node3562Labels =
    (37623398400 : ℝ) * ((79399260480 : ℝ) * mixedMoment B node3562 node3562Labels + 0)
  ring

theorem reducedTermEval1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1349 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1349 (originalVector B) := by
  rw [reducedTermArithmetic1349, ← sound3565 B hB hF]
  change (5653339486845861888000 : ℝ) * mixedMoment B node3565 node3565Labels =
    (37623398400 : ℝ) * ((150261266320 : ℝ) * mixedMoment B node3565 node3565Labels + 0)
  ring

theorem reducedTermEval1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1350 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1350 (originalVector B) := by
  rw [reducedTermArithmetic1350, ← sound3569 B hB hF]
  change (1962225745433985024000 : ℝ) * mixedMoment B node3569 node3569Labels =
    (37623398400 : ℝ) * ((52154399360 : ℝ) * mixedMoment B node3569 node3569Labels + 0)
  ring

theorem reducedTermEval1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1351 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1351 (originalVector B) := by
  rw [reducedTermArithmetic1351, ← sound3570 B hB hF]
  change (2433073703307706368000 : ℝ) * mixedMoment B node3570 node3570Labels =
    (37623398400 : ℝ) * ((64669163520 : ℝ) * mixedMoment B node3570 node3570Labels + 0)
  ring

theorem reducedTermEval1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1352 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1352 (originalVector B) := by
  rw [reducedTermArithmetic1352, ← sound3571 B hB hF]
  change (12926463385317801984000 : ℝ) * mixedMoment B node3571 node3571Labels =
    (37623398400 : ℝ) * ((343575113760 : ℝ) * mixedMoment B node3571 node3571Labels + 0)
  ring

theorem reducedTermEval1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1353 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1353 (originalVector B) := by
  rw [reducedTermArithmetic1353, ← sound3572 B hB hF]
  change (-16798163909915049984000 : ℝ) * mixedMoment B node3572 node3572Labels =
    (37623398400 : ℝ) * (((-446481833760 : ℤ) : ℝ) * mixedMoment B node3572 node3572Labels + 0)
  ring

theorem reducedTermEval1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1354 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1354 (originalVector B) := by
  rw [reducedTermArithmetic1354, ← sound3573 B hB hF]
  change (19725678159807578112000 : ℝ) * mixedMoment B node3573 node3573Labels =
    (37623398400 : ℝ) * ((524292833680 : ℝ) * mixedMoment B node3573 node3573Labels + 0)
  ring

theorem reducedTermEval1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1355 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1355 (originalVector B) := by
  rw [reducedTermArithmetic1355, ← sound3577 B hB hF]
  change (4629005356695552000000 : ℝ) * mixedMoment B node3577 node3577Labels =
    (37623398400 : ℝ) * ((123035280000 : ℝ) * mixedMoment B node3577 node3577Labels + 0)
  ring

theorem reducedTermEval1356 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1356 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1356 (originalVector B) := by
  rw [reducedTermArithmetic1356, ← sound3578 B hB hF]
  change (13978224602687471616000 : ℝ) * mixedMoment B node3578 node3578Labels =
    (37623398400 : ℝ) * ((371530090240 : ℝ) * mixedMoment B node3578 node3578Labels + 0)
  ring

theorem reducedTermEval1357 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1357 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1357 (originalVector B) := by
  rw [reducedTermArithmetic1357, ← sound3579 B hB hF]
  change (4549640633792593920000 : ℝ) * mixedMoment B node3579 node3579Labels =
    (37623398400 : ℝ) * ((120925828800 : ℝ) * mixedMoment B node3579 node3579Labels + 0)
  ring

theorem reducedTermEval1358 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1358 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1358 (originalVector B) := by
  rw [reducedTermArithmetic1358, ← sound3580 B hB hF]
  change (831414264535056384000 : ℝ) * mixedMoment B node3580 node3580Labels =
    (37623398400 : ℝ) * ((22098329760 : ℝ) * mixedMoment B node3580 node3580Labels + 0)
  ring

theorem reducedTermEval1359 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1359 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1359 (originalVector B) := by
  rw [reducedTermArithmetic1359, ← sound3581 B hB hF]
  change (-220499962681098240000 : ℝ) * mixedMoment B node3581 node3581Labels =
    (37623398400 : ℝ) * (((-5860713600 : ℤ) : ℝ) * mixedMoment B node3581 node3581Labels + 0)
  ring

theorem reducedTermEval1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1360 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1360 (originalVector B) := by
  rw [reducedTermArithmetic1360, ← sound3582 B hB hF]
  change (4158174109630464000000 : ℝ) * mixedMoment B node3582 node3582Labels =
    (37623398400 : ℝ) * ((110520960000 : ℝ) * mixedMoment B node3582 node3582Labels + 0)
  ring

theorem reducedTermEval1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1361 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1361 (originalVector B) := by
  rw [reducedTermArithmetic1361, ← sound3583 B hB hF]
  change (-11906431827880181760000 : ℝ) * mixedMoment B node3583 node3583Labels =
    (37623398400 : ℝ) * (((-316463486400 : ℤ) : ℝ) * mixedMoment B node3583 node3583Labels + 0)
  ring

theorem reducedTermEval1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1362 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1362 (originalVector B) := by
  rw [reducedTermArithmetic1362, ← sound3584 B hB hF]
  change (29008204646800490496000 : ℝ) * mixedMoment B node3584 node3584Labels =
    (37623398400 : ℝ) * ((771015003440 : ℝ) * mixedMoment B node3584 node3584Labels + 0)
  ring

theorem reducedTermEval1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1363 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1363 (originalVector B) := by
  rw [reducedTermArithmetic1363, ← sound3618 B hB hF]
  change (1173233126741114880000 : ℝ) * mixedMoment B node3618 node3618Labels =
    (37623398400 : ℝ) * ((31183603200 : ℝ) * mixedMoment B node3618 node3618Labels + 0)
  ring

theorem reducedTermEval1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1364 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1364 (originalVector B) := by
  rw [reducedTermArithmetic1364, ← sound3619 B hB hF]
  change (-9131775422933237760000 : ℝ) * mixedMoment B node3619 node3619Labels =
    (37623398400 : ℝ) * (((-242715326400 : ℤ) : ℝ) * mixedMoment B node3619 node3619Labels + 0)
  ring

theorem reducedTermEval1365 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1365 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1365 (originalVector B) := by
  rw [reducedTermArithmetic1365, ← sound3622 B hB hF]
  change (13643436319594905600000 : ℝ) * mixedMoment B node3622 node3622Labels =
    (37623398400 : ℝ) * ((362631684000 : ℝ) * mixedMoment B node3622 node3622Labels + 0)
  ring

theorem reducedTermEval1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1366 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1366 (originalVector B) := by
  rw [reducedTermArithmetic1366, ← sound3623 B hB hF]
  change (-6320730118534594560000 : ℝ) * mixedMoment B node3623 node3623Labels =
    (37623398400 : ℝ) * (((-167999978400 : ℤ) : ℝ) * mixedMoment B node3623 node3623Labels + 0)
  ring

theorem reducedTermEval1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1367 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1367 (originalVector B) := by
  rw [reducedTermArithmetic1367, ← sound3625 B hB hF]
  change (3684922744987975680000 : ℝ) * mixedMoment B node3625 node3625Labels =
    (37623398400 : ℝ) * ((97942315200 : ℝ) * mixedMoment B node3625 node3625Labels + 0)
  ring

theorem reducedTermEval1368 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1368 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1368 (originalVector B) := by
  rw [reducedTermArithmetic1368, ← sound3626 B hB hF]
  change (5131131445562572800000 : ℝ) * mixedMoment B node3626 node3626Labels =
    (37623398400 : ℝ) * ((136381392000 : ℝ) * mixedMoment B node3626 node3626Labels + 0)
  ring

theorem reducedTermEval1369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1369 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1369 (originalVector B) := by
  rw [reducedTermArithmetic1369, ← sound3627 B hB hF]
  change (7417776676181114880000 : ℝ) * mixedMoment B node3627 node3627Labels =
    (37623398400 : ℝ) * ((197158603200 : ℝ) * mixedMoment B node3627 node3627Labels + 0)
  ring

theorem reducedTermEval1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1370 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1370 (originalVector B) := by
  rw [reducedTermArithmetic1370, ← sound3628 B hB hF]
  change (-6336028725384314880000 : ℝ) * mixedMoment B node3628 node3628Labels =
    (37623398400 : ℝ) * (((-168406603200 : ℤ) : ℝ) * mixedMoment B node3628 node3628Labels + 0)
  ring

theorem reducedTermEval1371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1371 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1371 (originalVector B) := by
  rw [reducedTermArithmetic1371, ← sound3629 B hB hF]
  change (-14329743722100817920000 : ℝ) * mixedMoment B node3629 node3629Labels =
    (37623398400 : ℝ) * (((-380873188800 : ℤ) : ℝ) * mixedMoment B node3629 node3629Labels + 0)
  ring

theorem reducedTermEval1372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1372 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1372 (originalVector B) := by
  rw [reducedTermArithmetic1372, ← sound3632 B hB hF]
  change (-3609060248797839360000 : ℝ) * mixedMoment B node3632 node3632Labels =
    (37623398400 : ℝ) * (((-95925950400 : ℤ) : ℝ) * mixedMoment B node3632 node3632Labels + 0)
  ring

theorem reducedTermEval1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1373 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1373 (originalVector B) := by
  rw [reducedTermArithmetic1373, ← sound3633 B hB hF]
  change (17665403553650442240000 : ℝ) * mixedMoment B node3633 node3633Labels =
    (37623398400 : ℝ) * ((469532373600 : ℝ) * mixedMoment B node3633 node3633Labels + 0)
  ring

theorem reducedTermEval1374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1374 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1374 (originalVector B) := by
  rw [reducedTermArithmetic1374, ← sound3635 B hB hF]
  change (-6038654768971776000000 : ℝ) * mixedMoment B node3635 node3635Labels =
    (37623398400 : ℝ) * (((-160502640000 : ℤ) : ℝ) * mixedMoment B node3635 node3635Labels + 0)
  ring

theorem reducedTermEval1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1375 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1375 (originalVector B) := by
  rw [reducedTermArithmetic1375, ← sound3636 B hB hF]
  change (-1266335868026880000000 : ℝ) * mixedMoment B node3636 node3636Labels =
    (37623398400 : ℝ) * (((-33658200000 : ℤ) : ℝ) * mixedMoment B node3636 node3636Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1316 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1316 (originalVector B) := by
  rw [reducedMerge1316Check, Integer.Sparse.eval_mergeBy, reducedTermEval1320 B hB hF, reducedTermEval1321 B hB hF]
  rw [originalMerge1316, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1317 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1317 (originalVector B) := by
  rw [reducedMerge1317Check, Integer.Sparse.eval_mergeBy, reducedTermEval1319 B hB hF, reducedMergeEval1316 B hB hF]
  rw [originalMerge1317, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1318 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1318 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1318 (originalVector B) := by
  rw [reducedMerge1318Check, Integer.Sparse.eval_mergeBy, reducedTermEval1322 B hB hF, reducedTermEval1323 B hB hF]
  rw [originalMerge1318, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1319 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1319 (originalVector B) := by
  rw [reducedMerge1319Check, Integer.Sparse.eval_mergeBy, reducedTermEval1324 B hB hF, reducedTermEval1325 B hB hF]
  rw [originalMerge1319, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1320 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1320 (originalVector B) := by
  rw [reducedMerge1320Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1318 B hB hF, reducedMergeEval1319 B hB hF]
  rw [originalMerge1320, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1321 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1321 (originalVector B) := by
  rw [reducedMerge1321Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1317 B hB hF, reducedMergeEval1320 B hB hF]
  rw [originalMerge1321, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1322 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1322 (originalVector B) := by
  rw [reducedMerge1322Check, Integer.Sparse.eval_mergeBy, reducedTermEval1326 B hB hF, reducedTermEval1327 B hB hF]
  rw [originalMerge1322, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1323 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1323 (originalVector B) := by
  rw [reducedMerge1323Check, Integer.Sparse.eval_mergeBy, reducedTermEval1328 B hB hF, reducedTermEval1329 B hB hF]
  rw [originalMerge1323, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1324 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1324 (originalVector B) := by
  rw [reducedMerge1324Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1322 B hB hF, reducedMergeEval1323 B hB hF]
  rw [originalMerge1324, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1325 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1325 (originalVector B) := by
  rw [reducedMerge1325Check, Integer.Sparse.eval_mergeBy, reducedTermEval1330 B hB hF, reducedTermEval1331 B hB hF]
  rw [originalMerge1325, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1326 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1326 (originalVector B) := by
  rw [reducedMerge1326Check, Integer.Sparse.eval_mergeBy, reducedTermEval1332 B hB hF, reducedTermEval1333 B hB hF]
  rw [originalMerge1326, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1327 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1327 (originalVector B) := by
  rw [reducedMerge1327Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1325 B hB hF, reducedMergeEval1326 B hB hF]
  rw [originalMerge1327, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1328 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1328 (originalVector B) := by
  rw [reducedMerge1328Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1324 B hB hF, reducedMergeEval1327 B hB hF]
  rw [originalMerge1328, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1329 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1329 (originalVector B) := by
  rw [reducedMerge1329Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1321 B hB hF, reducedMergeEval1328 B hB hF]
  rw [originalMerge1329, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1330 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1330 (originalVector B) := by
  rw [reducedMerge1330Check, Integer.Sparse.eval_mergeBy, reducedTermEval1335 B hB hF, reducedTermEval1336 B hB hF]
  rw [originalMerge1330, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1331 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1331 (originalVector B) := by
  rw [reducedMerge1331Check, Integer.Sparse.eval_mergeBy, reducedTermEval1334 B hB hF, reducedMergeEval1330 B hB hF]
  rw [originalMerge1331, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1332 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1332 (originalVector B) := by
  rw [reducedMerge1332Check, Integer.Sparse.eval_mergeBy, reducedTermEval1337 B hB hF, reducedTermEval1338 B hB hF]
  rw [originalMerge1332, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1333 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1333 (originalVector B) := by
  rw [reducedMerge1333Check, Integer.Sparse.eval_mergeBy, reducedTermEval1339 B hB hF, reducedTermEval1340 B hB hF]
  rw [originalMerge1333, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1334 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1334 (originalVector B) := by
  rw [reducedMerge1334Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1332 B hB hF, reducedMergeEval1333 B hB hF]
  rw [originalMerge1334, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1335 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1335 (originalVector B) := by
  rw [reducedMerge1335Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1331 B hB hF, reducedMergeEval1334 B hB hF]
  rw [originalMerge1335, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1336 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1336 (originalVector B) := by
  rw [reducedMerge1336Check, Integer.Sparse.eval_mergeBy, reducedTermEval1341 B hB hF, reducedTermEval1342 B hB hF]
  rw [originalMerge1336, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1337 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1337 (originalVector B) := by
  rw [reducedMerge1337Check, Integer.Sparse.eval_mergeBy, reducedTermEval1343 B hB hF, reducedTermEval1344 B hB hF]
  rw [originalMerge1337, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1338 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1338 (originalVector B) := by
  rw [reducedMerge1338Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1336 B hB hF, reducedMergeEval1337 B hB hF]
  rw [originalMerge1338, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1339 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1339 (originalVector B) := by
  rw [reducedMerge1339Check, Integer.Sparse.eval_mergeBy, reducedTermEval1345 B hB hF, reducedTermEval1346 B hB hF]
  rw [originalMerge1339, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1340 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1340 (originalVector B) := by
  rw [reducedMerge1340Check, Integer.Sparse.eval_mergeBy, reducedTermEval1347 B hB hF, reducedTermEval1348 B hB hF]
  rw [originalMerge1340, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1341 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1341 (originalVector B) := by
  rw [reducedMerge1341Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1339 B hB hF, reducedMergeEval1340 B hB hF]
  rw [originalMerge1341, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1342 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1342 (originalVector B) := by
  rw [reducedMerge1342Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1338 B hB hF, reducedMergeEval1341 B hB hF]
  rw [originalMerge1342, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1343 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1343 (originalVector B) := by
  rw [reducedMerge1343Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1335 B hB hF, reducedMergeEval1342 B hB hF]
  rw [originalMerge1343, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1376 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1376 (originalVector B) := by
  rw [reducedTermArithmetic1376, ← sound3670 B hB hF]
  change (-3558260895488409600000 : ℝ) * mixedMoment B node3670 node3670Labels =
    (37623398400 : ℝ) * (((-94575744000 : ℤ) : ℝ) * mixedMoment B node3670 node3670Labels + 0)
  ring

theorem reducedTermEval1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1377 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1377 (originalVector B) := by
  rw [reducedTermArithmetic1377, ← sound3671 B hB hF]
  change (2856821572837048320000 : ℝ) * mixedMoment B node3671 node3671Labels =
    (37623398400 : ℝ) * ((75932044800 : ℝ) * mixedMoment B node3671 node3671Labels + 0)
  ring

theorem reducedTermEval1378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1378 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1378 (originalVector B) := by
  rw [reducedTermArithmetic1378, ← sound3672 B hB hF]
  change (8029997437000089600000 : ℝ) * mixedMoment B node3672 node3672Labels =
    (37623398400 : ℝ) * ((213430944000 : ℝ) * mixedMoment B node3672 node3672Labels + 0)
  ring

theorem reducedTermEval1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1379 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1379 (originalVector B) := by
  rw [reducedTermArithmetic1379, ← sound3673 B hB hF]
  change (-2089015568665804800000 : ℝ) * mixedMoment B node3673 node3673Labels =
    (37623398400 : ℝ) * (((-55524372000 : ℤ) : ℝ) * mixedMoment B node3673 node3673Labels + 0)
  ring

theorem reducedTermEval1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1380 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1380 (originalVector B) := by
  rw [reducedTermArithmetic1380, ← sound3674 B hB hF]
  change (-3375760173907968000000 : ℝ) * mixedMoment B node3674 node3674Labels =
    (37623398400 : ℝ) * (((-89725020000 : ℤ) : ℝ) * mixedMoment B node3674 node3674Labels + 0)
  ring

theorem reducedTermEval1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1381 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1381 (originalVector B) := by
  rw [reducedTermArithmetic1381, ← sound3676 B hB hF]
  change (2139241300593868800000 : ℝ) * mixedMoment B node3676 node3676Labels =
    (37623398400 : ℝ) * ((56859332000 : ℝ) * mixedMoment B node3676 node3676Labels + 0)
  ring

theorem reducedTermEval1382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1382 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1382 (originalVector B) := by
  rw [reducedTermArithmetic1382, ← sound3685 B hB hF]
  change (-669848715789926400000 : ℝ) * mixedMoment B node3685 node3685Labels =
    (37623398400 : ℝ) * (((-17804046000 : ℤ) : ℝ) * mixedMoment B node3685 node3685Labels + 0)
  ring

theorem reducedTermEval1383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1383 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1383 (originalVector B) := by
  rw [reducedTermArithmetic1383, ← sound3689 B hB hF]
  change (5058598529834680320000 : ℝ) * mixedMoment B node3689 node3689Labels =
    (37623398400 : ℝ) * ((134453524800 : ℝ) * mixedMoment B node3689 node3689Labels + 0)
  ring

theorem reducedTermEval1384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1384 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1384 (originalVector B) := by
  rw [reducedTermArithmetic1384, ← sound3690 B hB hF]
  change (-2714220736148275200000 : ℝ) * mixedMoment B node3690 node3690Labels =
    (37623398400 : ℝ) * (((-72141828000 : ℤ) : ℝ) * mixedMoment B node3690 node3690Labels + 0)
  ring

theorem reducedTermEval1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1385 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1385 (originalVector B) := by
  rw [reducedTermArithmetic1385, ← sound3692 B hB hF]
  change (-5214891424162775040000 : ℝ) * mixedMoment B node3692 node3692Labels =
    (37623398400 : ℝ) * (((-138607665600 : ℤ) : ℝ) * mixedMoment B node3692 node3692Labels + 0)
  ring

theorem reducedTermEval1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1386 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1386 (originalVector B) := by
  rw [reducedTermArithmetic1386, ← sound3693 B hB hF]
  change (-1773350590788403200000 : ℝ) * mixedMoment B node3693 node3693Labels =
    (37623398400 : ℝ) * (((-47134248000 : ℤ) : ℝ) * mixedMoment B node3693 node3693Labels + 0)
  ring

theorem reducedTermEval1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1387 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1387 (originalVector B) := by
  rw [reducedTermArithmetic1387, ← sound3694 B hB hF]
  change (-5315776700851814400000 : ℝ) * mixedMoment B node3694 node3694Labels =
    (37623398400 : ℝ) * (((-141289116000 : ℤ) : ℝ) * mixedMoment B node3694 node3694Labels + 0)
  ring

theorem reducedTermEval1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1388 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1388 (originalVector B) := by
  rw [reducedTermArithmetic1388, ← sound3698 B hB hF]
  change (3611345102733312000000 : ℝ) * mixedMoment B node3698 node3698Labels =
    (37623398400 : ℝ) * ((95986680000 : ℝ) * mixedMoment B node3698 node3698Labels + 0)
  ring

theorem reducedTermEval1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1389 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1389 (originalVector B) := by
  rw [reducedTermArithmetic1389, ← sound3699 B hB hF]
  change (3293229788164915200000 : ℝ) * mixedMoment B node3699 node3699Labels =
    (37623398400 : ℝ) * ((87531428000 : ℝ) * mixedMoment B node3699 node3699Labels + 0)
  ring

theorem reducedTermEval1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1390 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1390 (originalVector B) := by
  rw [reducedTermArithmetic1390, ← sound3703 B hB hF]
  change (-6378432071205519360000 : ℝ) * mixedMoment B node3703 node3703Labels =
    (37623398400 : ℝ) * (((-169533650400 : ℤ) : ℝ) * mixedMoment B node3703 node3703Labels + 0)
  ring

theorem reducedTermEval1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1391 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1391 (originalVector B) := by
  rw [reducedTermArithmetic1391, ← sound3705 B hB hF]
  change (8915230341595791360000 : ℝ) * mixedMoment B node3705 node3705Labels =
    (37623398400 : ℝ) * ((236959730400 : ℝ) * mixedMoment B node3705 node3705Labels + 0)
  ring

theorem reducedTermEval1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1392 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1392 (originalVector B) := by
  rw [reducedTermArithmetic1392, ← sound3706 B hB hF]
  change (-10603132867144581120000 : ℝ) * mixedMoment B node3706 node3706Labels =
    (37623398400 : ℝ) * (((-281822836800 : ℤ) : ℝ) * mixedMoment B node3706 node3706Labels + 0)
  ring

theorem reducedTermEval1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1393 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1393 (originalVector B) := by
  rw [reducedTermArithmetic1393, ← sound3708 B hB hF]
  change (23153419811192832000000 : ℝ) * mixedMoment B node3708 node3708Labels =
    (37623398400 : ℝ) * ((615399480000 : ℝ) * mixedMoment B node3708 node3708Labels + 0)
  ring

theorem reducedTermEval1394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1394 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1394 (originalVector B) := by
  rw [reducedTermArithmetic1394, ← sound3709 B hB hF]
  change (7818430382751744000000 : ℝ) * mixedMoment B node3709 node3709Labels =
    (37623398400 : ℝ) * ((207807660000 : ℝ) * mixedMoment B node3709 node3709Labels + 0)
  ring

theorem reducedTermEval1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1395 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1395 (originalVector B) := by
  rw [reducedTermArithmetic1395, ← sound3710 B hB hF]
  change (3622287461825249280000 : ℝ) * mixedMoment B node3710 node3710Labels =
    (37623398400 : ℝ) * ((96277519200 : ℝ) * mixedMoment B node3710 node3710Labels + 0)
  ring

theorem reducedTermEval1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1396 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1396 (originalVector B) := by
  rw [reducedTermArithmetic1396, ← sound3715 B hB hF]
  change (11249654248211742720000 : ℝ) * mixedMoment B node3715 node3715Labels =
    (37623398400 : ℝ) * ((299006860800 : ℝ) * mixedMoment B node3715 node3715Labels + 0)
  ring

theorem reducedTermEval1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1397 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1397 (originalVector B) := by
  rw [reducedTermArithmetic1397, ← sound3719 B hB hF]
  change (7397988905631744000000 : ℝ) * mixedMoment B node3719 node3719Labels =
    (37623398400 : ℝ) * ((196632660000 : ℝ) * mixedMoment B node3719 node3719Labels + 0)
  ring

theorem reducedTermEval1398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1398 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1398 (originalVector B) := by
  rw [reducedTermArithmetic1398, ← sound3720 B hB hF]
  change (6831804330736680960000 : ℝ) * mixedMoment B node3720 node3720Labels =
    (37623398400 : ℝ) * ((181583924400 : ℝ) * mixedMoment B node3720 node3720Labels + 0)
  ring

theorem reducedTermEval1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1399 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1399 (originalVector B) := by
  rw [reducedTermArithmetic1399, ← sound3721 B hB hF]
  change (12949195045327994880000 : ℝ) * mixedMoment B node3721 node3721Labels =
    (37623398400 : ℝ) * ((344179303200 : ℝ) * mixedMoment B node3721 node3721Labels + 0)
  ring

theorem reducedTermEval1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1400 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1400 (originalVector B) := by
  rw [reducedTermArithmetic1400, ← sound3722 B hB hF]
  change (-26217469888567050240000 : ℝ) * mixedMoment B node3722 node3722Labels =
    (37623398400 : ℝ) * (((-696839493600 : ℤ) : ℝ) * mixedMoment B node3722 node3722Labels + 0)
  ring

theorem reducedTermEval1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1401 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1401 (originalVector B) := by
  rw [reducedTermArithmetic1401, ← sound3723 B hB hF]
  change (3090408338022727680000 : ℝ) * mixedMoment B node3723 node3723Labels =
    (37623398400 : ℝ) * ((82140595200 : ℝ) * mixedMoment B node3723 node3723Labels + 0)
  ring

theorem reducedTermEval1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1402 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1402 (originalVector B) := by
  rw [reducedTermArithmetic1402, ← sound3724 B hB hF]
  change (-12931866039110860800000 : ℝ) * mixedMoment B node3724 node3724Labels =
    (37623398400 : ℝ) * (((-343718712000 : ℤ) : ℝ) * mixedMoment B node3724 node3724Labels + 0)
  ring

theorem reducedTermEval1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1403 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1403 (originalVector B) := by
  rw [reducedTermArithmetic1403, ← sound3730 B hB hF]
  change (498588466060984320000 : ℝ) * mixedMoment B node3730 node3730Labels =
    (37623398400 : ℝ) * ((13252084800 : ℝ) * mixedMoment B node3730 node3730Labels + 0)
  ring

theorem reducedTermEval1404 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1404 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1404 (originalVector B) := by
  rw [reducedTermArithmetic1404, ← sound3731 B hB hF]
  change (-4479366205522575360000 : ℝ) * mixedMoment B node3731 node3731Labels =
    (37623398400 : ℝ) * (((-119057990400 : ℤ) : ℝ) * mixedMoment B node3731 node3731Labels + 0)
  ring

theorem reducedTermEval1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1405 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1405 (originalVector B) := by
  rw [reducedTermArithmetic1405, ← sound3732 B hB hF]
  change (-15823981309321543680000 : ℝ) * mixedMoment B node3732 node3732Labels =
    (37623398400 : ℝ) * (((-420588835200 : ℤ) : ℝ) * mixedMoment B node3732 node3732Labels + 0)
  ring

theorem reducedTermEval1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1406 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1406 (originalVector B) := by
  rw [reducedTermArithmetic1406, ← sound3733 B hB hF]
  change (1301788622079590400000 : ℝ) * mixedMoment B node3733 node3733Labels =
    (37623398400 : ℝ) * ((34600506000 : ℝ) * mixedMoment B node3733 node3733Labels + 0)
  ring

theorem reducedTermEval1407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1407 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1407 (originalVector B) := by
  rw [reducedTermArithmetic1407, ← sound3755 B hB hF]
  change (885060905467576320000 : ℝ) * mixedMoment B node3755 node3755Labels =
    (37623398400 : ℝ) * ((23524214800 : ℝ) * mixedMoment B node3755 node3755Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1344 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1344 (originalVector B) := by
  rw [reducedMerge1344Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1329 B hB hF, reducedMergeEval1343 B hB hF]
  rw [originalMerge1344, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1345 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1345 (originalVector B) := by
  rw [reducedMerge1345Check, Integer.Sparse.eval_mergeBy, reducedTermEval1350 B hB hF, reducedTermEval1351 B hB hF]
  rw [originalMerge1345, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1346 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1346 (originalVector B) := by
  rw [reducedMerge1346Check, Integer.Sparse.eval_mergeBy, reducedTermEval1349 B hB hF, reducedMergeEval1345 B hB hF]
  rw [originalMerge1346, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1347 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1347 (originalVector B) := by
  rw [reducedMerge1347Check, Integer.Sparse.eval_mergeBy, reducedTermEval1352 B hB hF, reducedTermEval1353 B hB hF]
  rw [originalMerge1347, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1348 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1348 (originalVector B) := by
  rw [reducedMerge1348Check, Integer.Sparse.eval_mergeBy, reducedTermEval1354 B hB hF, reducedTermEval1355 B hB hF]
  rw [originalMerge1348, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1349 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1349 (originalVector B) := by
  rw [reducedMerge1349Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1347 B hB hF, reducedMergeEval1348 B hB hF]
  rw [originalMerge1349, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1350 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1350 (originalVector B) := by
  rw [reducedMerge1350Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1346 B hB hF, reducedMergeEval1349 B hB hF]
  rw [originalMerge1350, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1351 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1351 (originalVector B) := by
  rw [reducedMerge1351Check, Integer.Sparse.eval_mergeBy, reducedTermEval1356 B hB hF, reducedTermEval1357 B hB hF]
  rw [originalMerge1351, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1352 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1352 (originalVector B) := by
  rw [reducedMerge1352Check, Integer.Sparse.eval_mergeBy, reducedTermEval1358 B hB hF, reducedTermEval1359 B hB hF]
  rw [originalMerge1352, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1353 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1353 (originalVector B) := by
  rw [reducedMerge1353Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1351 B hB hF, reducedMergeEval1352 B hB hF]
  rw [originalMerge1353, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1354 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1354 (originalVector B) := by
  rw [reducedMerge1354Check, Integer.Sparse.eval_mergeBy, reducedTermEval1360 B hB hF, reducedTermEval1361 B hB hF]
  rw [originalMerge1354, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1355 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1355 (originalVector B) := by
  rw [reducedMerge1355Check, Integer.Sparse.eval_mergeBy, reducedTermEval1362 B hB hF, reducedTermEval1363 B hB hF]
  rw [originalMerge1355, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1356 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1356 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1356 (originalVector B) := by
  rw [reducedMerge1356Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1354 B hB hF, reducedMergeEval1355 B hB hF]
  rw [originalMerge1356, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1357 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1357 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1357 (originalVector B) := by
  rw [reducedMerge1357Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1353 B hB hF, reducedMergeEval1356 B hB hF]
  rw [originalMerge1357, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1358 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1358 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1358 (originalVector B) := by
  rw [reducedMerge1358Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1350 B hB hF, reducedMergeEval1357 B hB hF]
  rw [originalMerge1358, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1359 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1359 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1359 (originalVector B) := by
  rw [reducedMerge1359Check, Integer.Sparse.eval_mergeBy, reducedTermEval1365 B hB hF, reducedTermEval1366 B hB hF]
  rw [originalMerge1359, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1360 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1360 (originalVector B) := by
  rw [reducedMerge1360Check, Integer.Sparse.eval_mergeBy, reducedTermEval1364 B hB hF, reducedMergeEval1359 B hB hF]
  rw [originalMerge1360, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1361 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1361 (originalVector B) := by
  rw [reducedMerge1361Check, Integer.Sparse.eval_mergeBy, reducedTermEval1367 B hB hF, reducedTermEval1368 B hB hF]
  rw [originalMerge1361, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1362 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1362 (originalVector B) := by
  rw [reducedMerge1362Check, Integer.Sparse.eval_mergeBy, reducedTermEval1369 B hB hF, reducedTermEval1370 B hB hF]
  rw [originalMerge1362, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1363 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1363 (originalVector B) := by
  rw [reducedMerge1363Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1361 B hB hF, reducedMergeEval1362 B hB hF]
  rw [originalMerge1363, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1364 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1364 (originalVector B) := by
  rw [reducedMerge1364Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1360 B hB hF, reducedMergeEval1363 B hB hF]
  rw [originalMerge1364, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1365 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1365 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1365 (originalVector B) := by
  rw [reducedMerge1365Check, Integer.Sparse.eval_mergeBy, reducedTermEval1371 B hB hF, reducedTermEval1372 B hB hF]
  rw [originalMerge1365, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1366 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1366 (originalVector B) := by
  rw [reducedMerge1366Check, Integer.Sparse.eval_mergeBy, reducedTermEval1373 B hB hF, reducedTermEval1374 B hB hF]
  rw [originalMerge1366, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1367 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1367 (originalVector B) := by
  rw [reducedMerge1367Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1365 B hB hF, reducedMergeEval1366 B hB hF]
  rw [originalMerge1367, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1368 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1368 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1368 (originalVector B) := by
  rw [reducedMerge1368Check, Integer.Sparse.eval_mergeBy, reducedTermEval1375 B hB hF, reducedTermEval1376 B hB hF]
  rw [originalMerge1368, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1369 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1369 (originalVector B) := by
  rw [reducedMerge1369Check, Integer.Sparse.eval_mergeBy, reducedTermEval1377 B hB hF, reducedTermEval1378 B hB hF]
  rw [originalMerge1369, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1370 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1370 (originalVector B) := by
  rw [reducedMerge1370Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1368 B hB hF, reducedMergeEval1369 B hB hF]
  rw [originalMerge1370, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1371 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1371 (originalVector B) := by
  rw [reducedMerge1371Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1367 B hB hF, reducedMergeEval1370 B hB hF]
  rw [originalMerge1371, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1372 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1372 (originalVector B) := by
  rw [reducedMerge1372Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1364 B hB hF, reducedMergeEval1371 B hB hF]
  rw [originalMerge1372, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1373 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1373 (originalVector B) := by
  rw [reducedMerge1373Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1358 B hB hF, reducedMergeEval1372 B hB hF]
  rw [originalMerge1373, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1374 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1374 (originalVector B) := by
  rw [reducedMerge1374Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1344 B hB hF, reducedMergeEval1373 B hB hF]
  rw [originalMerge1374, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

theorem reducedMergeEval1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1375 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1375 (originalVector B) := by
  rw [reducedMerge1375Check, Integer.Sparse.eval_mergeBy, reducedTermEval1380 B hB hF, reducedTermEval1381 B hB hF]
  rw [originalMerge1375, Integer.Sparse.eval_append]
  exact (mul_add _ _ _).symm

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1408 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1408 (originalVector B) := by
  rw [reducedTermArithmetic1408, ← sound3759 B hB hF]
  change (-2229127337632333824000 : ℝ) * mixedMoment B node3759 node3759Labels =
    (37623398400 : ℝ) * (((-59248431360 : ℤ) : ℝ) * mixedMoment B node3759 node3759Labels + 0)
  ring

theorem reducedTermEval1409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1409 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1409 (originalVector B) := by
  rw [reducedTermArithmetic1409, ← sound3760 B hB hF]
  change (7779502517921906688000 : ℝ) * mixedMoment B node3760 node3760Labels =
    (37623398400 : ℝ) * ((206772988320 : ℝ) * mixedMoment B node3760 node3760Labels + 0)
  ring

theorem reducedTermEval1410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1410 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1410 (originalVector B) := by
  rw [reducedTermArithmetic1410, ← sound3761 B hB hF]
  change (-2581778767834054656000 : ℝ) * mixedMoment B node3761 node3761Labels =
    (37623398400 : ℝ) * (((-68621625840 : ℤ) : ℝ) * mixedMoment B node3761 node3761Labels + 0)
  ring

theorem reducedTermEval1411 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1411 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1411 (originalVector B) := by
  rw [reducedTermArithmetic1411, ← sound3762 B hB hF]
  change (-3482485535088967680000 : ℝ) * mixedMoment B node3762 node3762Labels =
    (37623398400 : ℝ) * (((-92561695200 : ℤ) : ℝ) * mixedMoment B node3762 node3762Labels + 0)
  ring

theorem reducedTermEval1412 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1412 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1412 (originalVector B) := by
  rw [reducedTermArithmetic1412, ← sound3763 B hB hF]
  change (722635406229897216000 : ℝ) * mixedMoment B node3763 node3763Labels =
    (37623398400 : ℝ) * ((19207074240 : ℝ) * mixedMoment B node3763 node3763Labels + 0)
  ring

theorem reducedTermEval1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1413 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1413 (originalVector B) := by
  rw [reducedTermArithmetic1413, ← sound3768 B hB hF]
  change (-629877478875660288000 : ℝ) * mixedMoment B node3768 node3768Labels =
    (37623398400 : ℝ) * (((-16741642320 : ℤ) : ℝ) * mixedMoment B node3768 node3768Labels + 0)
  ring

theorem reducedTermEval1414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1414 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1414 (originalVector B) := by
  rw [reducedTermArithmetic1414, ← sound3772 B hB hF]
  change (-1457354951397015552000 : ℝ) * mixedMoment B node3772 node3772Labels =
    (37623398400 : ℝ) * (((-38735335280 : ℤ) : ℝ) * mixedMoment B node3772 node3772Labels + 0)
  ring

theorem reducedTermEval1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1415 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1415 (originalVector B) := by
  rw [reducedTermArithmetic1415, ← sound3779 B hB hF]
  change (-23279727428871782400000 : ℝ) * mixedMoment B node3779 node3779Labels =
    (37623398400 : ℝ) * (((-618756636000 : ℤ) : ℝ) * mixedMoment B node3779 node3779Labels + 0)
  ring

theorem reducedTermEval1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1416 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1416 (originalVector B) := by
  rw [reducedTermArithmetic1416, ← sound3780 B hB hF]
  change (4493455024472064000000 : ℝ) * mixedMoment B node3780 node3780Labels =
    (37623398400 : ℝ) * ((119432460000 : ℝ) * mixedMoment B node3780 node3780Labels + 0)
  ring

theorem reducedTermEval1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1417 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1417 (originalVector B) := by
  rw [reducedTermArithmetic1417, ← sound3781 B hB hF]
  change (1745085365617950720000 : ℝ) * mixedMoment B node3781 node3781Labels =
    (37623398400 : ℝ) * ((46382980800 : ℝ) * mixedMoment B node3781 node3781Labels + 0)
  ring

theorem reducedTermEval1418 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1418 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1418 (originalVector B) := by
  rw [reducedTermArithmetic1418, ← sound3782 B hB hF]
  change (-4452974806184755200000 : ℝ) * mixedMoment B node3782 node3782Labels =
    (37623398400 : ℝ) * (((-118356528000 : ℤ) : ℝ) * mixedMoment B node3782 node3782Labels + 0)
  ring

theorem reducedTermEval1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1419 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1419 (originalVector B) := by
  rw [reducedTermArithmetic1419, ← sound3783 B hB hF]
  change (1278536233166438400000 : ℝ) * mixedMoment B node3783 node3783Labels =
    (37623398400 : ℝ) * ((33982476000 : ℝ) * mixedMoment B node3783 node3783Labels + 0)
  ring

theorem reducedTermEval1420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1420 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1420 (originalVector B) := by
  rw [reducedTermArithmetic1420, ← sound3786 B hB hF]
  change (5625894605263994880000 : ℝ) * mixedMoment B node3786 node3786Labels =
    (37623398400 : ℝ) * ((149531803200 : ℝ) * mixedMoment B node3786 node3786Labels + 0)
  ring

theorem reducedTermEval1421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1421 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1421 (originalVector B) := by
  rw [reducedTermArithmetic1421, ← sound3787 B hB hF]
  change (-16392111811529932800000 : ℝ) * mixedMoment B node3787 node3787Labels =
    (37623398400 : ℝ) * (((-435689292000 : ℤ) : ℝ) * mixedMoment B node3787 node3787Labels + 0)
  ring

theorem reducedTermEval1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1422 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1422 (originalVector B) := by
  rw [reducedTermArithmetic1422, ← sound3788 B hB hF]
  change (2738043209843343360000 : ℝ) * mixedMoment B node3788 node3788Labels =
    (37623398400 : ℝ) * ((72775010400 : ℝ) * mixedMoment B node3788 node3788Labels + 0)
  ring

theorem reducedTermEval1423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1423 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1423 (originalVector B) := by
  rw [reducedTermArithmetic1423, ← sound3789 B hB hF]
  change (1441864010724802560000 : ℝ) * mixedMoment B node3789 node3789Labels =
    (37623398400 : ℝ) * ((38323598400 : ℝ) * mixedMoment B node3789 node3789Labels + 0)
  ring

theorem reducedTermEval1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1424 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1424 (originalVector B) := by
  rw [reducedTermArithmetic1424, ← sound3800 B hB hF]
  change (26650108359770112000000 : ℝ) * mixedMoment B node3800 node3800Labels =
    (37623398400 : ℝ) * ((708338680000 : ℝ) * mixedMoment B node3800 node3800Labels + 0)
  ring

theorem reducedTermEval1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1425 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1425 (originalVector B) := by
  rw [reducedTermArithmetic1425, ← sound3801 B hB hF]
  change (-13178290840890900480000 : ℝ) * mixedMoment B node3801 node3801Labels =
    (37623398400 : ℝ) * (((-350268487200 : ℤ) : ℝ) * mixedMoment B node3801 node3801Labels + 0)
  ring

theorem reducedTermEval1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1426 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1426 (originalVector B) := by
  rw [reducedTermArithmetic1426, ← sound3802 B hB hF]
  change (-5516271414691430400000 : ℝ) * mixedMoment B node3802 node3802Labels =
    (37623398400 : ℝ) * (((-146618106000 : ℤ) : ℝ) * mixedMoment B node3802 node3802Labels + 0)
  ring

theorem reducedTermEval1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1427 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1427 (originalVector B) := by
  rw [reducedTermArithmetic1427, ← sound3803 B hB hF]
  change (-6944207726412988416000 : ℝ) * mixedMoment B node3803 node3803Labels =
    (37623398400 : ℝ) * (((-184571517240 : ℤ) : ℝ) * mixedMoment B node3803 node3803Labels + 0)
  ring

theorem reducedTermEval1428 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1428 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1428 (originalVector B) := by
  rw [reducedTermArithmetic1428, ← sound3805 B hB hF]
  change (5260225873509089280000 : ℝ) * mixedMoment B node3805 node3805Labels =
    (37623398400 : ℝ) * ((139812619200 : ℝ) * mixedMoment B node3805 node3805Labels + 0)
  ring

theorem reducedTermEval1429 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1429 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1429 (originalVector B) := by
  rw [reducedTermArithmetic1429, ← sound3806 B hB hF]
  change (669848715789926400000 : ℝ) * mixedMoment B node3806 node3806Labels =
    (37623398400 : ℝ) * ((17804046000 : ℝ) * mixedMoment B node3806 node3806Labels + 0)
  ring

theorem reducedTermEval1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1430 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1430 (originalVector B) := by
  rw [reducedTermArithmetic1430, ← sound3807 B hB hF]
  change (42601625103803351040000 : ℝ) * mixedMoment B node3807 node3807Labels =
    (37623398400 : ℝ) * ((1132317305600 : ℝ) * mixedMoment B node3807 node3807Labels + 0)
  ring

theorem reducedTermEval1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1431 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1431 (originalVector B) := by
  rw [reducedTermArithmetic1431, ← sound3808 B hB hF]
  change (9955200277551513600000 : ℝ) * mixedMoment B node3808 node3808Labels =
    (37623398400 : ℝ) * ((264601304000 : ℝ) * mixedMoment B node3808 node3808Labels + 0)
  ring

theorem reducedTermEval1432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1432 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1432 (originalVector B) := by
  rw [reducedTermArithmetic1432, ← sound3809 B hB hF]
  change (-28544727109663457280000 : ℝ) * mixedMoment B node3809 node3809Labels =
    (37623398400 : ℝ) * (((-758696139200 : ℤ) : ℝ) * mixedMoment B node3809 node3809Labels + 0)
  ring

theorem reducedTermEval1433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1433 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1433 (originalVector B) := by
  rw [reducedTermArithmetic1433, ← sound3812 B hB hF]
  change (10099373456256860160000 : ℝ) * mixedMoment B node3812 node3812Labels =
    (37623398400 : ℝ) * ((268433312400 : ℝ) * mixedMoment B node3812 node3812Labels + 0)
  ring

theorem reducedTermEval1434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1434 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1434 (originalVector B) := by
  rw [reducedTermArithmetic1434, ← sound3813 B hB hF]
  change (-31930167407745761280000 : ℝ) * mixedMoment B node3813 node3813Labels =
    (37623398400 : ℝ) * (((-848678449200 : ℤ) : ℝ) * mixedMoment B node3813 node3813Labels + 0)
  ring

theorem reducedTermEval1435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1435 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1435 (originalVector B) := by
  rw [reducedTermArithmetic1435, ← sound3814 B hB hF]
  change (-18142276456326758400000 : ℝ) * mixedMoment B node3814 node3814Labels =
    (37623398400 : ℝ) * (((-482207276000 : ℤ) : ℝ) * mixedMoment B node3814 node3814Labels + 0)
  ring

theorem reducedTermEval1436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1436 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1436 (originalVector B) := by
  rw [reducedTermArithmetic1436, ← sound3816 B hB hF]
  change (-1776998510349189120000 : ℝ) * mixedMoment B node3816 node3816Labels =
    (37623398400 : ℝ) * (((-47231206800 : ℤ) : ℝ) * mixedMoment B node3816 node3816Labels + 0)
  ring

theorem reducedTermEval1437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1437 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1437 (originalVector B) := by
  rw [reducedTermArithmetic1437, ← sound3817 B hB hF]
  change (24758844578608250880000 : ℝ) * mixedMoment B node3817 node3817Labels =
    (37623398400 : ℝ) * ((658070393200 : ℝ) * mixedMoment B node3817 node3817Labels + 0)
  ring

theorem reducedTermEval1438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1438 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1438 (originalVector B) := by
  rw [reducedTermArithmetic1438, ← sound3819 B hB hF]
  change (2089015568665804800000 : ℝ) * mixedMoment B node3819 node3819Labels =
    (37623398400 : ℝ) * ((55524372000 : ℝ) * mixedMoment B node3819 node3819Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1376 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1376 (originalVector B) := by
  rw [reducedMerge1376Check, Integer.Sparse.eval_mergeBy, reducedTermEval1379 B hB hF, reducedMergeEval1375 B hB hF]
  rw [originalMerge1376, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1377 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1377 (originalVector B) := by
  rw [reducedMerge1377Check, Integer.Sparse.eval_mergeBy, reducedTermEval1382 B hB hF, reducedTermEval1383 B hB hF]
  rw [originalMerge1377, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1378 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1378 (originalVector B) := by
  rw [reducedMerge1378Check, Integer.Sparse.eval_mergeBy, reducedTermEval1384 B hB hF, reducedTermEval1385 B hB hF]
  rw [originalMerge1378, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1379 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1379 (originalVector B) := by
  rw [reducedMerge1379Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1377 B hB hF, reducedMergeEval1378 B hB hF]
  rw [originalMerge1379, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1380 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1380 (originalVector B) := by
  rw [reducedMerge1380Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1376 B hB hF, reducedMergeEval1379 B hB hF]
  rw [originalMerge1380, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1381 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1381 (originalVector B) := by
  rw [reducedMerge1381Check, Integer.Sparse.eval_mergeBy, reducedTermEval1386 B hB hF, reducedTermEval1387 B hB hF]
  rw [originalMerge1381, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1382 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1382 (originalVector B) := by
  rw [reducedMerge1382Check, Integer.Sparse.eval_mergeBy, reducedTermEval1388 B hB hF, reducedTermEval1389 B hB hF]
  rw [originalMerge1382, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1383 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1383 (originalVector B) := by
  rw [reducedMerge1383Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1381 B hB hF, reducedMergeEval1382 B hB hF]
  rw [originalMerge1383, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1384 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1384 (originalVector B) := by
  rw [reducedMerge1384Check, Integer.Sparse.eval_mergeBy, reducedTermEval1390 B hB hF, reducedTermEval1391 B hB hF]
  rw [originalMerge1384, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1385 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1385 (originalVector B) := by
  rw [reducedMerge1385Check, Integer.Sparse.eval_mergeBy, reducedTermEval1392 B hB hF, reducedTermEval1393 B hB hF]
  rw [originalMerge1385, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1386 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1386 (originalVector B) := by
  rw [reducedMerge1386Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1384 B hB hF, reducedMergeEval1385 B hB hF]
  rw [originalMerge1386, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1387 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1387 (originalVector B) := by
  rw [reducedMerge1387Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1383 B hB hF, reducedMergeEval1386 B hB hF]
  rw [originalMerge1387, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1388 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1388 (originalVector B) := by
  rw [reducedMerge1388Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1380 B hB hF, reducedMergeEval1387 B hB hF]
  rw [originalMerge1388, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1389 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1389 (originalVector B) := by
  rw [reducedMerge1389Check, Integer.Sparse.eval_mergeBy, reducedTermEval1395 B hB hF, reducedTermEval1396 B hB hF]
  rw [originalMerge1389, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1390 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1390 (originalVector B) := by
  rw [reducedMerge1390Check, Integer.Sparse.eval_mergeBy, reducedTermEval1394 B hB hF, reducedMergeEval1389 B hB hF]
  rw [originalMerge1390, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1391 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1391 (originalVector B) := by
  rw [reducedMerge1391Check, Integer.Sparse.eval_mergeBy, reducedTermEval1397 B hB hF, reducedTermEval1398 B hB hF]
  rw [originalMerge1391, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1392 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1392 (originalVector B) := by
  rw [reducedMerge1392Check, Integer.Sparse.eval_mergeBy, reducedTermEval1399 B hB hF, reducedTermEval1400 B hB hF]
  rw [originalMerge1392, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1393 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1393 (originalVector B) := by
  rw [reducedMerge1393Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1391 B hB hF, reducedMergeEval1392 B hB hF]
  rw [originalMerge1393, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1394 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1394 (originalVector B) := by
  rw [reducedMerge1394Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1390 B hB hF, reducedMergeEval1393 B hB hF]
  rw [originalMerge1394, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1395 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1395 (originalVector B) := by
  rw [reducedMerge1395Check, Integer.Sparse.eval_mergeBy, reducedTermEval1401 B hB hF, reducedTermEval1402 B hB hF]
  rw [originalMerge1395, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1396 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1396 (originalVector B) := by
  rw [reducedMerge1396Check, Integer.Sparse.eval_mergeBy, reducedTermEval1403 B hB hF, reducedTermEval1404 B hB hF]
  rw [originalMerge1396, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1397 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1397 (originalVector B) := by
  rw [reducedMerge1397Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1395 B hB hF, reducedMergeEval1396 B hB hF]
  rw [originalMerge1397, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1398 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1398 (originalVector B) := by
  rw [reducedMerge1398Check, Integer.Sparse.eval_mergeBy, reducedTermEval1405 B hB hF, reducedTermEval1406 B hB hF]
  rw [originalMerge1398, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1399 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1399 (originalVector B) := by
  rw [reducedMerge1399Check, Integer.Sparse.eval_mergeBy, reducedTermEval1407 B hB hF, reducedTermEval1408 B hB hF]
  rw [originalMerge1399, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1400 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1400 (originalVector B) := by
  rw [reducedMerge1400Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1398 B hB hF, reducedMergeEval1399 B hB hF]
  rw [originalMerge1400, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1401 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1401 (originalVector B) := by
  rw [reducedMerge1401Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1397 B hB hF, reducedMergeEval1400 B hB hF]
  rw [originalMerge1401, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1402 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1402 (originalVector B) := by
  rw [reducedMerge1402Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1394 B hB hF, reducedMergeEval1401 B hB hF]
  rw [originalMerge1402, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1403 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1403 (originalVector B) := by
  rw [reducedMerge1403Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1388 B hB hF, reducedMergeEval1402 B hB hF]
  rw [originalMerge1403, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1404 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1404 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1404 (originalVector B) := by
  rw [reducedMerge1404Check, Integer.Sparse.eval_mergeBy, reducedTermEval1410 B hB hF, reducedTermEval1411 B hB hF]
  rw [originalMerge1404, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1405 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1405 (originalVector B) := by
  rw [reducedMerge1405Check, Integer.Sparse.eval_mergeBy, reducedTermEval1409 B hB hF, reducedMergeEval1404 B hB hF]
  rw [originalMerge1405, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1406 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1406 (originalVector B) := by
  rw [reducedMerge1406Check, Integer.Sparse.eval_mergeBy, reducedTermEval1412 B hB hF, reducedTermEval1413 B hB hF]
  rw [originalMerge1406, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1407 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1407 (originalVector B) := by
  rw [reducedMerge1407Check, Integer.Sparse.eval_mergeBy, reducedTermEval1414 B hB hF, reducedTermEval1415 B hB hF]
  rw [originalMerge1407, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1408 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1408 (originalVector B) := by
  rw [reducedMerge1408Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1406 B hB hF, reducedMergeEval1407 B hB hF]
  rw [originalMerge1408, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1409 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1409 (originalVector B) := by
  rw [reducedMerge1409Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1405 B hB hF, reducedMergeEval1408 B hB hF]
  rw [originalMerge1409, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1410 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1410 (originalVector B) := by
  rw [reducedMerge1410Check, Integer.Sparse.eval_mergeBy, reducedTermEval1416 B hB hF, reducedTermEval1417 B hB hF]
  rw [originalMerge1410, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1411 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1411 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1411 (originalVector B) := by
  rw [reducedMerge1411Check, Integer.Sparse.eval_mergeBy, reducedTermEval1418 B hB hF, reducedTermEval1419 B hB hF]
  rw [originalMerge1411, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1412 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1412 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1412 (originalVector B) := by
  rw [reducedMerge1412Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1410 B hB hF, reducedMergeEval1411 B hB hF]
  rw [originalMerge1412, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1413 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1413 (originalVector B) := by
  rw [reducedMerge1413Check, Integer.Sparse.eval_mergeBy, reducedTermEval1420 B hB hF, reducedTermEval1421 B hB hF]
  rw [originalMerge1413, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1414 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1414 (originalVector B) := by
  rw [reducedMerge1414Check, Integer.Sparse.eval_mergeBy, reducedTermEval1422 B hB hF, reducedTermEval1423 B hB hF]
  rw [originalMerge1414, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1415 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1415 (originalVector B) := by
  rw [reducedMerge1415Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1413 B hB hF, reducedMergeEval1414 B hB hF]
  rw [originalMerge1415, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1416 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1416 (originalVector B) := by
  rw [reducedMerge1416Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1412 B hB hF, reducedMergeEval1415 B hB hF]
  rw [originalMerge1416, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1417 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1417 (originalVector B) := by
  rw [reducedMerge1417Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1409 B hB hF, reducedMergeEval1416 B hB hF]
  rw [originalMerge1417, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1418 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1418 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1418 (originalVector B) := by
  rw [reducedMerge1418Check, Integer.Sparse.eval_mergeBy, reducedTermEval1425 B hB hF, reducedTermEval1426 B hB hF]
  rw [originalMerge1418, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1419 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1419 (originalVector B) := by
  rw [reducedMerge1419Check, Integer.Sparse.eval_mergeBy, reducedTermEval1424 B hB hF, reducedMergeEval1418 B hB hF]
  rw [originalMerge1419, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1420 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1420 (originalVector B) := by
  rw [reducedMerge1420Check, Integer.Sparse.eval_mergeBy, reducedTermEval1427 B hB hF, reducedTermEval1428 B hB hF]
  rw [originalMerge1420, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1421 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1421 (originalVector B) := by
  rw [reducedMerge1421Check, Integer.Sparse.eval_mergeBy, reducedTermEval1429 B hB hF, reducedTermEval1430 B hB hF]
  rw [originalMerge1421, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1422 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1422 (originalVector B) := by
  rw [reducedMerge1422Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1420 B hB hF, reducedMergeEval1421 B hB hF]
  rw [originalMerge1422, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1423 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1423 (originalVector B) := by
  rw [reducedMerge1423Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1419 B hB hF, reducedMergeEval1422 B hB hF]
  rw [originalMerge1423, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1424 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1424 (originalVector B) := by
  rw [reducedMerge1424Check, Integer.Sparse.eval_mergeBy, reducedTermEval1431 B hB hF, reducedTermEval1432 B hB hF]
  rw [originalMerge1424, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1425 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1425 (originalVector B) := by
  rw [reducedMerge1425Check, Integer.Sparse.eval_mergeBy, reducedTermEval1433 B hB hF, reducedTermEval1434 B hB hF]
  rw [originalMerge1425, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1426 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1426 (originalVector B) := by
  rw [reducedMerge1426Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1424 B hB hF, reducedMergeEval1425 B hB hF]
  rw [originalMerge1426, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1427 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1427 (originalVector B) := by
  rw [reducedMerge1427Check, Integer.Sparse.eval_mergeBy, reducedTermEval1435 B hB hF, reducedTermEval1436 B hB hF]
  rw [originalMerge1427, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1428 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1428 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1428 (originalVector B) := by
  rw [reducedMerge1428Check, Integer.Sparse.eval_mergeBy, reducedTermEval1437 B hB hF, reducedTermEval1438 B hB hF]
  rw [originalMerge1428, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1429 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1429 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1429 (originalVector B) := by
  rw [reducedMerge1429Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1427 B hB hF, reducedMergeEval1428 B hB hF]
  rw [originalMerge1429, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1430 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1430 (originalVector B) := by
  rw [reducedMerge1430Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1426 B hB hF, reducedMergeEval1429 B hB hF]
  rw [originalMerge1430, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1431 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1431 (originalVector B) := by
  rw [reducedMerge1431Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1423 B hB hF, reducedMergeEval1430 B hB hF]
  rw [originalMerge1431, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1432 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1432 (originalVector B) := by
  rw [reducedMerge1432Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1417 B hB hF, reducedMergeEval1431 B hB hF]
  rw [originalMerge1432, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1433 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1433 (originalVector B) := by
  rw [reducedMerge1433Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1403 B hB hF, reducedMergeEval1432 B hB hF]
  rw [originalMerge1433, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1434 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1434 (originalVector B) := by
  rw [reducedMerge1434Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1374 B hB hF, reducedMergeEval1433 B hB hF]
  rw [originalMerge1434, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1435 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1435 (originalVector B) := by
  rw [reducedMerge1435Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1315_e B hB hF, reducedMergeEval1434 B hB hF]
  rw [originalMerge1435, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1436_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1436 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1436 (originalVector B) := by
  rw [reducedMerge1436Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1196_e B hB hF, reducedMergeEval1435 B hB hF]
  rw [originalMerge1436, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e_oai
