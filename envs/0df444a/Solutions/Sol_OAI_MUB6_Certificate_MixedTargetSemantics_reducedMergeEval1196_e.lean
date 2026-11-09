-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:10:58.334479+00:00
-- url     : https://prove2.me/submissions/f5519da6-8490-4dd3-997b-22425b8eb38f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E138
import Definitions.Def_OAIQ106E139
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1075_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1194_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
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

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

theorem sound2557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2557 node2557Labels = Sparse.eval nodeValue2557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2557) = mixedMoment B node2557 node2557Labels := rfl
  simpa [nodeValue2557, Sparse.eval] using hc.symm

theorem sound2558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2558 node2558Labels = Sparse.eval nodeValue2558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2558) = mixedMoment B node2558 node2558Labels := rfl
  simpa [nodeValue2558, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2560 node2560Labels = Sparse.eval nodeValue2560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2560) = mixedMoment B node2560 node2560Labels := rfl
  simpa [nodeValue2560, Sparse.eval] using hc.symm

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

theorem sound2566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2566 node2566Labels = Sparse.eval nodeValue2566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2566) = mixedMoment B node2566 node2566Labels := rfl
  simpa [nodeValue2566, Sparse.eval] using hc.symm

theorem sound2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2569 node2569Labels = Sparse.eval nodeValue2569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2569) = mixedMoment B node2569 node2569Labels := rfl
  simpa [nodeValue2569, Sparse.eval] using hc.symm

theorem sound2573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2573 node2573Labels = Sparse.eval nodeValue2573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2573) = mixedMoment B node2573 node2573Labels := rfl
  simpa [nodeValue2573, Sparse.eval] using hc.symm

theorem sound2575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2575 node2575Labels = Sparse.eval nodeValue2575 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2575) = mixedMoment B node2575 node2575Labels := rfl
  simpa [nodeValue2575, Sparse.eval] using hc.symm

theorem sound2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2587 node2587Labels = Sparse.eval nodeValue2587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2587) = mixedMoment B node2587 node2587Labels := rfl
  simpa [nodeValue2587, Sparse.eval] using hc.symm

theorem sound2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2589 node2589Labels = Sparse.eval nodeValue2589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2589) = mixedMoment B node2589 node2589Labels := rfl
  simpa [nodeValue2589, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

theorem sound2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2591 node2591Labels = Sparse.eval nodeValue2591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2591) = mixedMoment B node2591 node2591Labels := rfl
  simpa [nodeValue2591, Sparse.eval] using hc.symm

theorem sound2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2600 node2600Labels = Sparse.eval nodeValue2600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2600) = mixedMoment B node2600 node2600Labels := rfl
  simpa [nodeValue2600, Sparse.eval] using hc.symm

theorem sound2603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2603 node2603Labels = Sparse.eval nodeValue2603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2603) = mixedMoment B node2603 node2603Labels := rfl
  simpa [nodeValue2603, Sparse.eval] using hc.symm

theorem sound2614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2614 node2614Labels = Sparse.eval nodeValue2614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2614) = mixedMoment B node2614 node2614Labels := rfl
  simpa [nodeValue2614, Sparse.eval] using hc.symm

theorem sound2617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2617 node2617Labels = Sparse.eval nodeValue2617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2617) = mixedMoment B node2617 node2617Labels := rfl
  simpa [nodeValue2617, Sparse.eval] using hc.symm

theorem sound2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2618 node2618Labels = Sparse.eval nodeValue2618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2618) = mixedMoment B node2618 node2618Labels := rfl
  simpa [nodeValue2618, Sparse.eval] using hc.symm

theorem sound2620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2620 node2620Labels = Sparse.eval nodeValue2620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2620) = mixedMoment B node2620 node2620Labels := rfl
  simpa [nodeValue2620, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2631 node2631Labels = Sparse.eval nodeValue2631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2631) = mixedMoment B node2631 node2631Labels := rfl
  simpa [nodeValue2631, Sparse.eval] using hc.symm

theorem sound2632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2632 node2632Labels = Sparse.eval nodeValue2632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2632) = mixedMoment B node2632 node2632Labels := rfl
  simpa [nodeValue2632, Sparse.eval] using hc.symm

theorem sound2633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2633 node2633Labels = Sparse.eval nodeValue2633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2633) = mixedMoment B node2633 node2633Labels := rfl
  simpa [nodeValue2633, Sparse.eval] using hc.symm

theorem sound2635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2635 node2635Labels = Sparse.eval nodeValue2635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2635) = mixedMoment B node2635 node2635Labels := rfl
  simpa [nodeValue2635, Sparse.eval] using hc.symm

theorem sound2641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2641 node2641Labels = Sparse.eval nodeValue2641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2641) = mixedMoment B node2641 node2641Labels := rfl
  simpa [nodeValue2641, Sparse.eval] using hc.symm

theorem sound2643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2643 node2643Labels = Sparse.eval nodeValue2643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2643) = mixedMoment B node2643 node2643Labels := rfl
  simpa [nodeValue2643, Sparse.eval] using hc.symm

theorem sound2652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2652 node2652Labels = Sparse.eval nodeValue2652 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2652) = mixedMoment B node2652 node2652Labels := rfl
  simpa [nodeValue2652, Sparse.eval] using hc.symm

theorem sound2653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2653 node2653Labels = Sparse.eval nodeValue2653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2653) = mixedMoment B node2653 node2653Labels := rfl
  simpa [nodeValue2653, Sparse.eval] using hc.symm

theorem sound2654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2654 node2654Labels = Sparse.eval nodeValue2654 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2654) = mixedMoment B node2654 node2654Labels := rfl
  simpa [nodeValue2654, Sparse.eval] using hc.symm

theorem sound2655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2655 node2655Labels = Sparse.eval nodeValue2655 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2655) = mixedMoment B node2655 node2655Labels := rfl
  simpa [nodeValue2655, Sparse.eval] using hc.symm

theorem sound2656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2656 node2656Labels = Sparse.eval nodeValue2656 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2656) = mixedMoment B node2656 node2656Labels := rfl
  simpa [nodeValue2656, Sparse.eval] using hc.symm

theorem sound2657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2657 node2657Labels = Sparse.eval nodeValue2657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2657) = mixedMoment B node2657 node2657Labels := rfl
  simpa [nodeValue2657, Sparse.eval] using hc.symm

theorem sound2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2658 node2658Labels = Sparse.eval nodeValue2658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2658) = mixedMoment B node2658 node2658Labels := rfl
  simpa [nodeValue2658, Sparse.eval] using hc.symm

theorem sound2659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2659 node2659Labels = Sparse.eval nodeValue2659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2659) = mixedMoment B node2659 node2659Labels := rfl
  simpa [nodeValue2659, Sparse.eval] using hc.symm

theorem sound2661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2661 node2661Labels = Sparse.eval nodeValue2661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2661) = mixedMoment B node2661 node2661Labels := rfl
  simpa [nodeValue2661, Sparse.eval] using hc.symm

theorem sound2662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2662 node2662Labels = Sparse.eval nodeValue2662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2662) = mixedMoment B node2662 node2662Labels := rfl
  simpa [nodeValue2662, Sparse.eval] using hc.symm

theorem sound2664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2664 node2664Labels = Sparse.eval nodeValue2664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2664) = mixedMoment B node2664 node2664Labels := rfl
  simpa [nodeValue2664, Sparse.eval] using hc.symm

theorem sound2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2669 node2669Labels = Sparse.eval nodeValue2669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2669) = mixedMoment B node2669 node2669Labels := rfl
  simpa [nodeValue2669, Sparse.eval] using hc.symm

theorem sound2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2670 node2670Labels = Sparse.eval nodeValue2670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2670) = mixedMoment B node2670 node2670Labels := rfl
  simpa [nodeValue2670, Sparse.eval] using hc.symm

theorem sound2673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2673 node2673Labels = Sparse.eval nodeValue2673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2673) = mixedMoment B node2673 node2673Labels := rfl
  simpa [nodeValue2673, Sparse.eval] using hc.symm

theorem sound2676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2676 node2676Labels = Sparse.eval nodeValue2676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2676) = mixedMoment B node2676 node2676Labels := rfl
  simpa [nodeValue2676, Sparse.eval] using hc.symm

theorem sound2677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2677 node2677Labels = Sparse.eval nodeValue2677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2677) = mixedMoment B node2677 node2677Labels := rfl
  simpa [nodeValue2677, Sparse.eval] using hc.symm

theorem sound2678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2678 node2678Labels = Sparse.eval nodeValue2678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2678) = mixedMoment B node2678 node2678Labels := rfl
  simpa [nodeValue2678, Sparse.eval] using hc.symm

theorem sound2680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2680 node2680Labels = Sparse.eval nodeValue2680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2680) = mixedMoment B node2680 node2680Labels := rfl
  simpa [nodeValue2680, Sparse.eval] using hc.symm

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

theorem sound2682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2682 node2682Labels = Sparse.eval nodeValue2682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2682) = mixedMoment B node2682 node2682Labels := rfl
  simpa [nodeValue2682, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

theorem sound2687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2687 node2687Labels = Sparse.eval nodeValue2687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2687) = mixedMoment B node2687 node2687Labels := rfl
  simpa [nodeValue2687, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = 0 := by
  exact mixedMoment_alpha B hF node2709 node2709Labels 1 permutation200
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2688 node2688Labels = Sparse.eval nodeValue2688 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2688) = mixedMoment B node2688 node2688Labels := rfl
  simpa [nodeValue2688, Sparse.eval] using hc.symm

theorem sound2690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2690 node2690Labels = Sparse.eval nodeValue2690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2690) = mixedMoment B node2690 node2690Labels := rfl
  simpa [nodeValue2690, Sparse.eval] using hc.symm

theorem sound2697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2697 node2697Labels = Sparse.eval nodeValue2697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2697) = mixedMoment B node2697 node2697Labels := rfl
  simpa [nodeValue2697, Sparse.eval] using hc.symm

theorem sound2698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2698 node2698Labels = Sparse.eval nodeValue2698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2698) = mixedMoment B node2698 node2698Labels := rfl
  simpa [nodeValue2698, Sparse.eval] using hc.symm

theorem sound2700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2700 node2700Labels = Sparse.eval nodeValue2700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2700) = mixedMoment B node2700 node2700Labels := rfl
  simpa [nodeValue2700, Sparse.eval] using hc.symm

theorem sound2702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2702 node2702Labels = Sparse.eval nodeValue2702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2702) = mixedMoment B node2702 node2702Labels := rfl
  simpa [nodeValue2702, Sparse.eval] using hc.symm

theorem sound2706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2706 node2706Labels = Sparse.eval nodeValue2706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2706) = mixedMoment B node2706 node2706Labels := rfl
  simpa [nodeValue2706, Sparse.eval] using hc.symm

theorem sound2707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2707 node2707Labels = Sparse.eval nodeValue2707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2707) = mixedMoment B node2707 node2707Labels := rfl
  simpa [nodeValue2707, Sparse.eval] using hc.symm

theorem sound2708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2708 node2708Labels = Sparse.eval nodeValue2708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2708) = mixedMoment B node2708 node2708Labels := rfl
  simpa [nodeValue2708, Sparse.eval] using hc.symm

theorem sound2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = Sparse.eval nodeValue2709 (mixedVector B) := by
  simpa only [nodeValue2709, Sparse.eval_nil] using zero2709 B _hB _hF

theorem sound2710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2710 node2710Labels = Sparse.eval nodeValue2710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2710) = mixedMoment B node2710 node2710Labels := rfl
  simpa [nodeValue2710, Sparse.eval] using hc.symm

theorem sound2712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2712 node2712Labels = Sparse.eval nodeValue2712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2712) = mixedMoment B node2712 node2712Labels := rfl
  simpa [nodeValue2712, Sparse.eval] using hc.symm

theorem sound2714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2714 node2714Labels = Sparse.eval nodeValue2714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2714) = mixedMoment B node2714 node2714Labels := rfl
  simpa [nodeValue2714, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2803 node2803Labels = Sparse.eval nodeValue2803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2803) = mixedMoment B node2803 node2803Labels := rfl
  simpa [nodeValue2803, Sparse.eval] using hc.symm

theorem sound2806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2806 node2806Labels = Sparse.eval nodeValue2806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2806) = mixedMoment B node2806 node2806Labels := rfl
  simpa [nodeValue2806, Sparse.eval] using hc.symm

theorem sound2807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2807 node2807Labels = Sparse.eval nodeValue2807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2807) = mixedMoment B node2807 node2807Labels := rfl
  simpa [nodeValue2807, Sparse.eval] using hc.symm

theorem sound2809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2809 node2809Labels = Sparse.eval nodeValue2809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2809) = mixedMoment B node2809 node2809Labels := rfl
  simpa [nodeValue2809, Sparse.eval] using hc.symm

theorem sound2810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2810 node2810Labels = Sparse.eval nodeValue2810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2810) = mixedMoment B node2810 node2810Labels := rfl
  simpa [nodeValue2810, Sparse.eval] using hc.symm

theorem sound2811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2811 node2811Labels = Sparse.eval nodeValue2811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2811) = mixedMoment B node2811 node2811Labels := rfl
  simpa [nodeValue2811, Sparse.eval] using hc.symm

theorem sound2812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2812 node2812Labels = Sparse.eval nodeValue2812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2812) = mixedMoment B node2812 node2812Labels := rfl
  simpa [nodeValue2812, Sparse.eval] using hc.symm

theorem sound2813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2813 node2813Labels = Sparse.eval nodeValue2813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2813) = mixedMoment B node2813 node2813Labels := rfl
  simpa [nodeValue2813, Sparse.eval] using hc.symm

theorem sound2814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2814 node2814Labels = Sparse.eval nodeValue2814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2814) = mixedMoment B node2814 node2814Labels := rfl
  simpa [nodeValue2814, Sparse.eval] using hc.symm

theorem sound2815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2815 node2815Labels = Sparse.eval nodeValue2815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2815) = mixedMoment B node2815 node2815Labels := rfl
  simpa [nodeValue2815, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2816 node2816Labels = Sparse.eval nodeValue2816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2816) = mixedMoment B node2816 node2816Labels := rfl
  simpa [nodeValue2816, Sparse.eval] using hc.symm

theorem sound2817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2817 node2817Labels = Sparse.eval nodeValue2817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2817) = mixedMoment B node2817 node2817Labels := rfl
  simpa [nodeValue2817, Sparse.eval] using hc.symm

theorem sound2818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2818 node2818Labels = Sparse.eval nodeValue2818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2818) = mixedMoment B node2818 node2818Labels := rfl
  simpa [nodeValue2818, Sparse.eval] using hc.symm

theorem sound2819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2819 node2819Labels = Sparse.eval nodeValue2819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2819) = mixedMoment B node2819 node2819Labels := rfl
  simpa [nodeValue2819, Sparse.eval] using hc.symm

theorem sound2820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2820 node2820Labels = Sparse.eval nodeValue2820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2820) = mixedMoment B node2820 node2820Labels := rfl
  simpa [nodeValue2820, Sparse.eval] using hc.symm

theorem sound2821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2821 node2821Labels = Sparse.eval nodeValue2821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2821) = mixedMoment B node2821 node2821Labels := rfl
  simpa [nodeValue2821, Sparse.eval] using hc.symm

theorem sound2824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2824 node2824Labels = Sparse.eval nodeValue2824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2824) = mixedMoment B node2824 node2824Labels := rfl
  simpa [nodeValue2824, Sparse.eval] using hc.symm

theorem sound2826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2826 node2826Labels = Sparse.eval nodeValue2826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2826) = mixedMoment B node2826 node2826Labels := rfl
  simpa [nodeValue2826, Sparse.eval] using hc.symm

theorem sound2827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2827 node2827Labels = Sparse.eval nodeValue2827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2827) = mixedMoment B node2827 node2827Labels := rfl
  simpa [nodeValue2827, Sparse.eval] using hc.symm

theorem sound2846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2846 node2846Labels = Sparse.eval nodeValue2846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2846) = mixedMoment B node2846 node2846Labels := rfl
  simpa [nodeValue2846, Sparse.eval] using hc.symm

theorem sound2847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2847 node2847Labels = Sparse.eval nodeValue2847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2847) = mixedMoment B node2847 node2847Labels := rfl
  simpa [nodeValue2847, Sparse.eval] using hc.symm

theorem sound2848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2848 node2848Labels = Sparse.eval nodeValue2848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2848) = mixedMoment B node2848 node2848Labels := rfl
  simpa [nodeValue2848, Sparse.eval] using hc.symm

theorem sound2861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2861 node2861Labels = Sparse.eval nodeValue2861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2861) = mixedMoment B node2861 node2861Labels := rfl
  simpa [nodeValue2861, Sparse.eval] using hc.symm

theorem sound2862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2862 node2862Labels = Sparse.eval nodeValue2862 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2862) = mixedMoment B node2862 node2862Labels := rfl
  simpa [nodeValue2862, Sparse.eval] using hc.symm

theorem sound2864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2864 node2864Labels = Sparse.eval nodeValue2864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2864) = mixedMoment B node2864 node2864Labels := rfl
  simpa [nodeValue2864, Sparse.eval] using hc.symm

theorem sound2865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2865 node2865Labels = Sparse.eval nodeValue2865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2865) = mixedMoment B node2865 node2865Labels := rfl
  simpa [nodeValue2865, Sparse.eval] using hc.symm

theorem sound2867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2867 node2867Labels = Sparse.eval nodeValue2867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2867) = mixedMoment B node2867 node2867Labels := rfl
  simpa [nodeValue2867, Sparse.eval] using hc.symm

theorem sound2868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2868 node2868Labels = Sparse.eval nodeValue2868 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2868) = mixedMoment B node2868 node2868Labels := rfl
  simpa [nodeValue2868, Sparse.eval] using hc.symm

theorem sound2878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2878 node2878Labels = Sparse.eval nodeValue2878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2878) = mixedMoment B node2878 node2878Labels := rfl
  simpa [nodeValue2878, Sparse.eval] using hc.symm

theorem sound2879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2879 node2879Labels = Sparse.eval nodeValue2879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2879) = mixedMoment B node2879 node2879Labels := rfl
  simpa [nodeValue2879, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2880 node2880Labels = Sparse.eval nodeValue2880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2880) = mixedMoment B node2880 node2880Labels := rfl
  simpa [nodeValue2880, Sparse.eval] using hc.symm

theorem sound2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2881 node2881Labels = Sparse.eval nodeValue2881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2881) = mixedMoment B node2881 node2881Labels := rfl
  simpa [nodeValue2881, Sparse.eval] using hc.symm

theorem sound2882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2882 node2882Labels = Sparse.eval nodeValue2882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2882) = mixedMoment B node2882 node2882Labels := rfl
  simpa [nodeValue2882, Sparse.eval] using hc.symm

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

theorem sound2885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2885 node2885Labels = Sparse.eval nodeValue2885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2885) = mixedMoment B node2885 node2885Labels := rfl
  simpa [nodeValue2885, Sparse.eval] using hc.symm

theorem sound2886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2886 node2886Labels = Sparse.eval nodeValue2886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2886) = mixedMoment B node2886 node2886Labels := rfl
  simpa [nodeValue2886, Sparse.eval] using hc.symm

theorem sound2888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2888 node2888Labels = Sparse.eval nodeValue2888 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2888) = mixedMoment B node2888 node2888Labels := rfl
  simpa [nodeValue2888, Sparse.eval] using hc.symm

theorem sound2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2889 node2889Labels = Sparse.eval nodeValue2889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2889) = mixedMoment B node2889 node2889Labels := rfl
  simpa [nodeValue2889, Sparse.eval] using hc.symm

theorem sound2890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2890 node2890Labels = Sparse.eval nodeValue2890 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2890) = mixedMoment B node2890 node2890Labels := rfl
  simpa [nodeValue2890, Sparse.eval] using hc.symm

theorem sound2892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2892 node2892Labels = Sparse.eval nodeValue2892 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2892) = mixedMoment B node2892 node2892Labels := rfl
  simpa [nodeValue2892, Sparse.eval] using hc.symm

theorem sound2893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2893 node2893Labels = Sparse.eval nodeValue2893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2893) = mixedMoment B node2893 node2893Labels := rfl
  simpa [nodeValue2893, Sparse.eval] using hc.symm

theorem sound2895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2895 node2895Labels = Sparse.eval nodeValue2895 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2895) = mixedMoment B node2895 node2895Labels := rfl
  simpa [nodeValue2895, Sparse.eval] using hc.symm

theorem sound2896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2896 node2896Labels = Sparse.eval nodeValue2896 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2896) = mixedMoment B node2896 node2896Labels := rfl
  simpa [nodeValue2896, Sparse.eval] using hc.symm

theorem sound2898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2898 node2898Labels = Sparse.eval nodeValue2898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2898) = mixedMoment B node2898 node2898Labels := rfl
  simpa [nodeValue2898, Sparse.eval] using hc.symm

theorem sound2899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2899 node2899Labels = Sparse.eval nodeValue2899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2899) = mixedMoment B node2899 node2899Labels := rfl
  simpa [nodeValue2899, Sparse.eval] using hc.symm

theorem sound2900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2900 node2900Labels = Sparse.eval nodeValue2900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2900) = mixedMoment B node2900 node2900Labels := rfl
  simpa [nodeValue2900, Sparse.eval] using hc.symm

theorem sound2902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2902 node2902Labels = Sparse.eval nodeValue2902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2902) = mixedMoment B node2902 node2902Labels := rfl
  simpa [nodeValue2902, Sparse.eval] using hc.symm

theorem sound2916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2916 node2916Labels = Sparse.eval nodeValue2916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2916) = mixedMoment B node2916 node2916Labels := rfl
  simpa [nodeValue2916, Sparse.eval] using hc.symm

theorem sound2923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2923 node2923Labels = Sparse.eval nodeValue2923 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2923) = mixedMoment B node2923 node2923Labels := rfl
  simpa [nodeValue2923, Sparse.eval] using hc.symm

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

theorem sound2925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2925 node2925Labels = Sparse.eval nodeValue2925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2925) = mixedMoment B node2925 node2925Labels := rfl
  simpa [nodeValue2925, Sparse.eval] using hc.symm

theorem sound2928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2928 node2928Labels = Sparse.eval nodeValue2928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2928) = mixedMoment B node2928 node2928Labels := rfl
  simpa [nodeValue2928, Sparse.eval] using hc.symm

theorem sound2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2930 node2930Labels = Sparse.eval nodeValue2930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2930) = mixedMoment B node2930 node2930Labels := rfl
  simpa [nodeValue2930, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

theorem sound2933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2933 node2933Labels = Sparse.eval nodeValue2933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2933) = mixedMoment B node2933 node2933Labels := rfl
  simpa [nodeValue2933, Sparse.eval] using hc.symm

theorem sound2942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2942 node2942Labels = Sparse.eval nodeValue2942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2942) = mixedMoment B node2942 node2942Labels := rfl
  simpa [nodeValue2942, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2951 node2951Labels = Sparse.eval nodeValue2951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2951) = mixedMoment B node2951 node2951Labels := rfl
  simpa [nodeValue2951, Sparse.eval] using hc.symm

theorem sound2952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2952 node2952Labels = Sparse.eval nodeValue2952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2952) = mixedMoment B node2952 node2952Labels := rfl
  simpa [nodeValue2952, Sparse.eval] using hc.symm

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

theorem sound2955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2955 node2955Labels = Sparse.eval nodeValue2955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2955) = mixedMoment B node2955 node2955Labels := rfl
  simpa [nodeValue2955, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

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

theorem reducedTermArithmetic959 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm959 x = (-762973624782028800000 : ℝ) * Sparse.eval nodeValue2556 x := by
  norm_num [reducedTerm959, nodeValue2556, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic960 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm960 x = (-827530229555527680000 : ℝ) * Sparse.eval nodeValue2557 x := by
  norm_num [reducedTerm960, nodeValue2557, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic961 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm961 x = (3350500907776081920000 : ℝ) * Sparse.eval nodeValue2558 x := by
  norm_num [reducedTerm961, nodeValue2558, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic962 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm962 x = (-1308617765518049280000 : ℝ) * Sparse.eval nodeValue2560 x := by
  norm_num [reducedTerm962, nodeValue2560, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic963 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm963 x = (-8081533245759160320000 : ℝ) * Sparse.eval nodeValue2561 x := by
  norm_num [reducedTerm963, nodeValue2561, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic964 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm964 x = (54778388874854400000 : ℝ) * Sparse.eval nodeValue2566 x := by
  norm_num [reducedTerm964, nodeValue2566, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic965 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm965 x = (-54778388874854400000 : ℝ) * Sparse.eval nodeValue2569 x := by
  norm_num [reducedTerm965, nodeValue2569, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic966 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm966 x = (3475493000755937280000 : ℝ) * Sparse.eval nodeValue2573 x := by
  norm_num [reducedTerm966, nodeValue2573, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic967 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm967 x = (7730575112285061120000 : ℝ) * Sparse.eval nodeValue2575 x := by
  norm_num [reducedTerm967, nodeValue2575, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic968 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm968 x = (2089015568665804800000 : ℝ) * Sparse.eval nodeValue2587 x := by
  norm_num [reducedTerm968, nodeValue2587, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic969 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm969 x = (-878316128737689600000 : ℝ) * Sparse.eval nodeValue2589 x := by
  norm_num [reducedTerm969, nodeValue2589, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic970 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm970 x = (9764819380324270080000 : ℝ) * Sparse.eval nodeValue2590 x := by
  norm_num [reducedTerm970, nodeValue2590, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic971 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm971 x = (-2089015568665804800000 : ℝ) * Sparse.eval nodeValue2591 x := by
  norm_num [reducedTerm971, nodeValue2591, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic972 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm972 x = (6525212987851407360000 : ℝ) * Sparse.eval nodeValue2600 x := by
  norm_num [reducedTerm972, nodeValue2600, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic973 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm973 x = (4404201698619555840000 : ℝ) * Sparse.eval nodeValue2603 x := by
  norm_num [reducedTerm973, nodeValue2603, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic974 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm974 x = (54778388874854400000 : ℝ) * Sparse.eval nodeValue2614 x := by
  norm_num [reducedTerm974, nodeValue2614, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic975 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm975 x = (-9280530725231001600000 : ℝ) * Sparse.eval nodeValue2617 x := by
  norm_num [reducedTerm975, nodeValue2617, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic976 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm976 x = (34864691456596377600000 : ℝ) * Sparse.eval nodeValue2618 x := by
  norm_num [reducedTerm976, nodeValue2618, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic977 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm977 x = (10563661873945313280000 : ℝ) * Sparse.eval nodeValue2620 x := by
  norm_num [reducedTerm977, nodeValue2620, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic978 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm978 x = (-15111984861079142400000 : ℝ) * Sparse.eval nodeValue2631 x := by
  norm_num [reducedTerm978, nodeValue2631, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic979 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm979 x = (-6403063116880281600000 : ℝ) * Sparse.eval nodeValue2632 x := by
  norm_num [reducedTerm979, nodeValue2632, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic980 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm980 x = (15111984861079142400000 : ℝ) * Sparse.eval nodeValue2633 x := by
  norm_num [reducedTerm980, nodeValue2633, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic981 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm981 x = (3201531558440140800000 : ℝ) * Sparse.eval nodeValue2635 x := by
  norm_num [reducedTerm981, nodeValue2635, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic982 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm982 x = (7417350658916352000000 : ℝ) * Sparse.eval nodeValue2641 x := by
  norm_num [reducedTerm982, nodeValue2641, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic983 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm983 x = (7685347844476108800000 : ℝ) * Sparse.eval nodeValue2643 x := by
  norm_num [reducedTerm983, nodeValue2643, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic984 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm984 x = (4097268088154357760000 : ℝ) * Sparse.eval nodeValue2652 x := by
  norm_num [reducedTerm984, nodeValue2652, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic985 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm985 x = (-2900413559198711808000 : ℝ) * Sparse.eval nodeValue2653 x := by
  norm_num [reducedTerm985, nodeValue2653, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic986 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm986 x = (-59568121389514752000 : ℝ) * Sparse.eval nodeValue2654 x := by
  norm_num [reducedTerm986, nodeValue2654, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic987 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm987 x = (414737902356922368000 : ℝ) * Sparse.eval nodeValue2655 x := by
  norm_num [reducedTerm987, nodeValue2655, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic988 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm988 x = (2451504521281536000000 : ℝ) * Sparse.eval nodeValue2656 x := by
  norm_num [reducedTerm988, nodeValue2656, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic989 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm989 x = (3659948525761855488000 : ℝ) * Sparse.eval nodeValue2657 x := by
  norm_num [reducedTerm989, nodeValue2657, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic990 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm990 x = (-31848465594580992000 : ℝ) * Sparse.eval nodeValue2658 x := by
  norm_num [reducedTerm990, nodeValue2658, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic991 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm991 x = (-4218827410224709632000 : ℝ) * Sparse.eval nodeValue2659 x := by
  norm_num [reducedTerm991, nodeValue2659, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic992 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm992 x = (2542985543602667520000 : ℝ) * Sparse.eval nodeValue2661 x := by
  norm_num [reducedTerm992, nodeValue2661, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic993 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm993 x = (-95323232121126912000 : ℝ) * Sparse.eval nodeValue2662 x := by
  norm_num [reducedTerm993, nodeValue2662, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic994 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm994 x = (888215115745198080000 : ℝ) * Sparse.eval nodeValue2664 x := by
  norm_num [reducedTerm994, nodeValue2664, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic995 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm995 x = (1951341470849433600000 : ℝ) * Sparse.eval nodeValue2669 x := by
  norm_num [reducedTerm995, nodeValue2669, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic996 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm996 x = (-4302905736953069568000 : ℝ) * Sparse.eval nodeValue2670 x := by
  norm_num [reducedTerm996, nodeValue2670, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic997 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm997 x = (3169748139186585600000 : ℝ) * Sparse.eval nodeValue2673 x := by
  norm_num [reducedTerm997, nodeValue2673, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic998 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm998 x = (2197036481036156928000 : ℝ) * Sparse.eval nodeValue2676 x := by
  norm_num [reducedTerm998, nodeValue2676, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic999 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm999 x = (3660221256271921152000 : ℝ) * Sparse.eval nodeValue2677 x := by
  norm_num [reducedTerm999, nodeValue2677, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1000 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1000 x = (1249731921884479488000 : ℝ) * Sparse.eval nodeValue2678 x := by
  norm_num [reducedTerm1000, nodeValue2678, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1001 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1001 x = (328270556047343616000 : ℝ) * Sparse.eval nodeValue2680 x := by
  norm_num [reducedTerm1001, nodeValue2680, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1002 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1002 x = (-304877566989434880000 : ℝ) * Sparse.eval nodeValue2681 x := by
  norm_num [reducedTerm1002, nodeValue2681, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1003 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1003 x = (-2451504521281536000000 : ℝ) * Sparse.eval nodeValue2682 x := by
  norm_num [reducedTerm1003, nodeValue2682, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1004 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1004 x = (-2711614482074566656000 : ℝ) * Sparse.eval nodeValue2683 x := by
  norm_num [reducedTerm1004, nodeValue2683, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1005 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1005 x = (2753869669962743808000 : ℝ) * Sparse.eval nodeValue2687 x := by
  norm_num [reducedTerm1005, nodeValue2687, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1006 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1006 x = (2124806707563724800000 : ℝ) * Sparse.eval nodeValue2688 x := by
  norm_num [reducedTerm1006, nodeValue2688, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1007 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1007 x = (-2124806707563724800000 : ℝ) * Sparse.eval nodeValue2690 x := by
  norm_num [reducedTerm1007, nodeValue2690, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1008 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1008 x = (665857147118026752000 : ℝ) * Sparse.eval nodeValue2697 x := by
  norm_num [reducedTerm1008, nodeValue2697, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1009 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1009 x = (-3210049119603916800000 : ℝ) * Sparse.eval nodeValue2698 x := by
  norm_num [reducedTerm1009, nodeValue2698, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1010 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1010 x = (-450757951040323584000 : ℝ) * Sparse.eval nodeValue2700 x := by
  norm_num [reducedTerm1010, nodeValue2700, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1011 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1011 x = (-423147689038577664000 : ℝ) * Sparse.eval nodeValue2702 x := by
  norm_num [reducedTerm1011, nodeValue2702, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1012 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1012 x = (4172340565215019008000 : ℝ) * Sparse.eval nodeValue2706 x := by
  norm_num [reducedTerm1012, nodeValue2706, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1013 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1013 x = (-847409560407244800000 : ℝ) * Sparse.eval nodeValue2707 x := by
  norm_num [reducedTerm1013, nodeValue2707, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1014 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1014 x = (2180351629537837056000 : ℝ) * Sparse.eval nodeValue2708 x := by
  norm_num [reducedTerm1014, nodeValue2708, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1015 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1015 x = (21899673936219340800000 : ℝ) * Sparse.eval nodeValue2709 x := by
  norm_num [reducedTerm1015, nodeValue2709, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1016 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1016 x = (3772583761333911552000 : ℝ) * Sparse.eval nodeValue2710 x := by
  norm_num [reducedTerm1016, nodeValue2710, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1017 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1017 x = (669848715789926400000 : ℝ) * Sparse.eval nodeValue2712 x := by
  norm_num [reducedTerm1017, nodeValue2712, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1018 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1018 x = (-18738707098219315200000 : ℝ) * Sparse.eval nodeValue2714 x := by
  norm_num [reducedTerm1018, nodeValue2714, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1079 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1079 x = (7655273626113146880000 : ℝ) * Sparse.eval nodeValue2803 x := by
  norm_num [reducedTerm1079, nodeValue2803, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1080 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1080 x = (416003421044736000000 : ℝ) * Sparse.eval nodeValue2806 x := by
  norm_num [reducedTerm1080, nodeValue2806, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1081 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1081 x = (9566869889386414080000 : ℝ) * Sparse.eval nodeValue2807 x := by
  norm_num [reducedTerm1081, nodeValue2807, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1082 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1082 x = (-1653558743737958400000 : ℝ) * Sparse.eval nodeValue2809 x := by
  norm_num [reducedTerm1082, nodeValue2809, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1083 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1083 x = (-2050187137963130880000 : ℝ) * Sparse.eval nodeValue2810 x := by
  norm_num [reducedTerm1083, nodeValue2810, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1084 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1084 x = (-3435263414499409920000 : ℝ) * Sparse.eval nodeValue2811 x := by
  norm_num [reducedTerm1084, nodeValue2811, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1085 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1085 x = (7633541508433182720000 : ℝ) * Sparse.eval nodeValue2812 x := by
  norm_num [reducedTerm1085, nodeValue2812, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1086 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1086 x = (-590178927323381760000 : ℝ) * Sparse.eval nodeValue2813 x := by
  norm_num [reducedTerm1086, nodeValue2813, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1087 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1087 x = (-4479366205522575360000 : ℝ) * Sparse.eval nodeValue2814 x := by
  norm_num [reducedTerm1087, nodeValue2814, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1088 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1088 x = (5011857085783080960000 : ℝ) * Sparse.eval nodeValue2815 x := by
  norm_num [reducedTerm1088, nodeValue2815, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1089 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1089 x = (999901708930252800000 : ℝ) * Sparse.eval nodeValue2816 x := by
  norm_num [reducedTerm1089, nodeValue2816, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1090 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1090 x = (-7972461087479562240000 : ℝ) * Sparse.eval nodeValue2817 x := by
  norm_num [reducedTerm1090, nodeValue2817, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1091 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1091 x = (-5777870711254548480000 : ℝ) * Sparse.eval nodeValue2818 x := by
  norm_num [reducedTerm1091, nodeValue2818, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1092 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1092 x = (8961285504761856000000 : ℝ) * Sparse.eval nodeValue2819 x := by
  norm_num [reducedTerm1092, nodeValue2819, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1093 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1093 x = (1274912738715893760000 : ℝ) * Sparse.eval nodeValue2820 x := by
  norm_num [reducedTerm1093, nodeValue2820, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1094 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1094 x = (-2262212174315520000000 : ℝ) * Sparse.eval nodeValue2821 x := by
  norm_num [reducedTerm1094, nodeValue2821, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1095 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1095 x = (-11618393320164556800000 : ℝ) * Sparse.eval nodeValue2824 x := by
  norm_num [reducedTerm1095, nodeValue2824, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1096 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1096 x = (-10406241466564608000000 : ℝ) * Sparse.eval nodeValue2826 x := by
  norm_num [reducedTerm1096, nodeValue2826, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1097 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1097 x = (6238836832370688000000 : ℝ) * Sparse.eval nodeValue2827 x := by
  norm_num [reducedTerm1097, nodeValue2827, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1098 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1098 x = (2089015568665804800000 : ℝ) * Sparse.eval nodeValue2846 x := by
  norm_num [reducedTerm1098, nodeValue2846, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1099 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1099 x = (5660818630174310400000 : ℝ) * Sparse.eval nodeValue2847 x := by
  norm_num [reducedTerm1099, nodeValue2847, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1100 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1100 x = (-5194848837860720640000 : ℝ) * Sparse.eval nodeValue2848 x := by
  norm_num [reducedTerm1100, nodeValue2848, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1101 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1101 x = (-3445367674768588800000 : ℝ) * Sparse.eval nodeValue2861 x := by
  norm_num [reducedTerm1101, nodeValue2861, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1102 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1102 x = (-3526248379837317120000 : ℝ) * Sparse.eval nodeValue2862 x := by
  norm_num [reducedTerm1102, nodeValue2862, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1103 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1103 x = (1340821167243264000000 : ℝ) * Sparse.eval nodeValue2864 x := by
  norm_num [reducedTerm1103, nodeValue2864, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1104 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1104 x = (-21284105174522265600000 : ℝ) * Sparse.eval nodeValue2865 x := by
  norm_num [reducedTerm1104, nodeValue2865, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1105 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1105 x = (-6729430235975516160000 : ℝ) * Sparse.eval nodeValue2867 x := by
  norm_num [reducedTerm1105, nodeValue2867, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1106 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1106 x = (3526248379837317120000 : ℝ) * Sparse.eval nodeValue2868 x := by
  norm_num [reducedTerm1106, nodeValue2868, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1107 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1107 x = (9976743826758696960000 : ℝ) * Sparse.eval nodeValue2878 x := by
  norm_num [reducedTerm1107, nodeValue2878, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1108 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1108 x = (-416003421044736000000 : ℝ) * Sparse.eval nodeValue2879 x := by
  norm_num [reducedTerm1108, nodeValue2879, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1109 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1109 x = (-1781271279310602240000 : ℝ) * Sparse.eval nodeValue2880 x := by
  norm_num [reducedTerm1109, nodeValue2880, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1110 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1110 x = (3469795674486865920000 : ℝ) * Sparse.eval nodeValue2881 x := by
  norm_num [reducedTerm1110, nodeValue2881, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1111 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1111 x = (-9976743826758696960000 : ℝ) * Sparse.eval nodeValue2882 x := by
  norm_num [reducedTerm1111, nodeValue2882, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1112 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1112 x = (9212700734303109120000 : ℝ) * Sparse.eval nodeValue2884 x := by
  norm_num [reducedTerm1112, nodeValue2884, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1113 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1113 x = (-3934716707045376000000 : ℝ) * Sparse.eval nodeValue2885 x := by
  norm_num [reducedTerm1113, nodeValue2885, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1114 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1114 x = (3435263414499409920000 : ℝ) * Sparse.eval nodeValue2886 x := by
  norm_num [reducedTerm1114, nodeValue2886, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1115 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1115 x = (8305600448385515520000 : ℝ) * Sparse.eval nodeValue2888 x := by
  norm_num [reducedTerm1115, nodeValue2888, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1116 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1116 x = (2724268260332666880000 : ℝ) * Sparse.eval nodeValue2889 x := by
  norm_num [reducedTerm1116, nodeValue2889, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1117 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1117 x = (1355923199361024000000 : ℝ) * Sparse.eval nodeValue2890 x := by
  norm_num [reducedTerm1117, nodeValue2890, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1118 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1118 x = (6564939594419404800000 : ℝ) * Sparse.eval nodeValue2892 x := by
  norm_num [reducedTerm1118, nodeValue2892, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1119 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1119 x = (-1057001205647278080000 : ℝ) * Sparse.eval nodeValue2893 x := by
  norm_num [reducedTerm1119, nodeValue2893, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1120 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1120 x = (-5105263763930480640000 : ℝ) * Sparse.eval nodeValue2895 x := by
  norm_num [reducedTerm1120, nodeValue2895, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1121 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1121 x = (3946875325262069760000 : ℝ) * Sparse.eval nodeValue2896 x := by
  norm_num [reducedTerm1121, nodeValue2896, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1122 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1122 x = (-5660818630174310400000 : ℝ) * Sparse.eval nodeValue2898 x := by
  norm_num [reducedTerm1122, nodeValue2898, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1123 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1123 x = (-9762840630358179840000 : ℝ) * Sparse.eval nodeValue2899 x := by
  norm_num [reducedTerm1123, nodeValue2899, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1124 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1124 x = (16607243005555507200000 : ℝ) * Sparse.eval nodeValue2900 x := by
  norm_num [reducedTerm1124, nodeValue2900, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1125 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1125 x = (13705060285808640000000 : ℝ) * Sparse.eval nodeValue2902 x := by
  norm_num [reducedTerm1125, nodeValue2902, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1126 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1126 x = (-2757638739876249600000 : ℝ) * Sparse.eval nodeValue2916 x := by
  norm_num [reducedTerm1126, nodeValue2916, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1127 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1127 x = (-359649951169904640000 : ℝ) * Sparse.eval nodeValue2923 x := by
  norm_num [reducedTerm1127, nodeValue2923, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1128 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1128 x = (19302033754623836160000 : ℝ) * Sparse.eval nodeValue2924 x := by
  norm_num [reducedTerm1128, nodeValue2924, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1129 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1129 x = (6891745041155358720000 : ℝ) * Sparse.eval nodeValue2925 x := by
  norm_num [reducedTerm1129, nodeValue2925, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1130 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1130 x = (20635690283060428800000 : ℝ) * Sparse.eval nodeValue2928 x := by
  norm_num [reducedTerm1130, nodeValue2928, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1131 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1131 x = (6436794359666442240000 : ℝ) * Sparse.eval nodeValue2930 x := by
  norm_num [reducedTerm1131, nodeValue2930, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1132 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1132 x = (829623023566848000000 : ℝ) * Sparse.eval nodeValue2931 x := by
  norm_num [reducedTerm1132, nodeValue2931, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1133 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1133 x = (-16476867997522329600000 : ℝ) * Sparse.eval nodeValue2933 x := by
  norm_num [reducedTerm1133, nodeValue2933, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1134 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1134 x = (-8398043666546688000000 : ℝ) * Sparse.eval nodeValue2942 x := by
  norm_num [reducedTerm1134, nodeValue2942, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1135 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1135 x = (33959038618062028800000 : ℝ) * Sparse.eval nodeValue2951 x := by
  norm_num [reducedTerm1135, nodeValue2951, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1136 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1136 x = (-571357054756454400000 : ℝ) * Sparse.eval nodeValue2952 x := by
  norm_num [reducedTerm1136, nodeValue2952, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1137 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1137 x = (-8958732411045150720000 : ℝ) * Sparse.eval nodeValue2954 x := by
  norm_num [reducedTerm1137, nodeValue2954, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1138 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1138 x = (-39828535728449126400000 : ℝ) * Sparse.eval nodeValue2955 x := by
  norm_num [reducedTerm1138, nodeValue2955, Integer.Sparse.eval, Sparse.eval]

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

theorem reducedMerge958Check : reducedMerge958 = Integer.Sparse.mergeBy masterLess reducedTerm960 reducedTerm961 := by decide +kernel

theorem reducedMerge959Check : reducedMerge959 = Integer.Sparse.mergeBy masterLess reducedTerm959 reducedMerge958 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge960Check : reducedMerge960 = Integer.Sparse.mergeBy masterLess reducedTerm962 reducedTerm963 := by decide +kernel

theorem reducedMerge961Check : reducedMerge961 = Integer.Sparse.mergeBy masterLess reducedTerm964 reducedTerm965 := by decide +kernel

theorem reducedMerge962Check : reducedMerge962 = Integer.Sparse.mergeBy masterLess reducedMerge960 reducedMerge961 := by decide +kernel

theorem reducedMerge963Check : reducedMerge963 = Integer.Sparse.mergeBy masterLess reducedMerge959 reducedMerge962 := by decide +kernel

theorem reducedMerge964Check : reducedMerge964 = Integer.Sparse.mergeBy masterLess reducedTerm966 reducedTerm967 := by decide +kernel

theorem reducedMerge965Check : reducedMerge965 = Integer.Sparse.mergeBy masterLess reducedTerm968 reducedTerm969 := by decide +kernel

theorem reducedMerge966Check : reducedMerge966 = Integer.Sparse.mergeBy masterLess reducedMerge964 reducedMerge965 := by decide +kernel

theorem reducedMerge967Check : reducedMerge967 = Integer.Sparse.mergeBy masterLess reducedTerm970 reducedTerm971 := by decide +kernel

theorem reducedMerge968Check : reducedMerge968 = Integer.Sparse.mergeBy masterLess reducedTerm972 reducedTerm973 := by decide +kernel

theorem reducedMerge969Check : reducedMerge969 = Integer.Sparse.mergeBy masterLess reducedMerge967 reducedMerge968 := by decide +kernel

theorem reducedMerge970Check : reducedMerge970 = Integer.Sparse.mergeBy masterLess reducedMerge966 reducedMerge969 := by decide +kernel

theorem reducedMerge971Check : reducedMerge971 = Integer.Sparse.mergeBy masterLess reducedMerge963 reducedMerge970 := by decide +kernel

theorem reducedMerge972Check : reducedMerge972 = Integer.Sparse.mergeBy masterLess reducedTerm975 reducedTerm976 := by decide +kernel

theorem reducedMerge973Check : reducedMerge973 = Integer.Sparse.mergeBy masterLess reducedTerm974 reducedMerge972 := by decide +kernel

theorem reducedMerge974Check : reducedMerge974 = Integer.Sparse.mergeBy masterLess reducedTerm977 reducedTerm978 := by decide +kernel

theorem reducedMerge975Check : reducedMerge975 = Integer.Sparse.mergeBy masterLess reducedTerm979 reducedTerm980 := by decide +kernel

theorem reducedMerge976Check : reducedMerge976 = Integer.Sparse.mergeBy masterLess reducedMerge974 reducedMerge975 := by decide +kernel

theorem reducedMerge977Check : reducedMerge977 = Integer.Sparse.mergeBy masterLess reducedMerge973 reducedMerge976 := by decide +kernel

theorem reducedMerge978Check : reducedMerge978 = Integer.Sparse.mergeBy masterLess reducedTerm981 reducedTerm982 := by decide +kernel

theorem reducedMerge979Check : reducedMerge979 = Integer.Sparse.mergeBy masterLess reducedTerm983 reducedTerm984 := by decide +kernel

theorem reducedMerge980Check : reducedMerge980 = Integer.Sparse.mergeBy masterLess reducedMerge978 reducedMerge979 := by decide +kernel

theorem reducedMerge981Check : reducedMerge981 = Integer.Sparse.mergeBy masterLess reducedTerm985 reducedTerm986 := by decide +kernel

theorem reducedMerge982Check : reducedMerge982 = Integer.Sparse.mergeBy masterLess reducedTerm987 reducedTerm988 := by decide +kernel

theorem reducedMerge983Check : reducedMerge983 = Integer.Sparse.mergeBy masterLess reducedMerge981 reducedMerge982 := by decide +kernel

theorem reducedMerge984Check : reducedMerge984 = Integer.Sparse.mergeBy masterLess reducedMerge980 reducedMerge983 := by decide +kernel

theorem reducedMerge985Check : reducedMerge985 = Integer.Sparse.mergeBy masterLess reducedMerge977 reducedMerge984 := by decide +kernel

theorem reducedMerge986Check : reducedMerge986 = Integer.Sparse.mergeBy masterLess reducedMerge971 reducedMerge985 := by decide +kernel

theorem reducedMerge987Check : reducedMerge987 = Integer.Sparse.mergeBy masterLess reducedTerm990 reducedTerm991 := by decide +kernel

theorem reducedMerge988Check : reducedMerge988 = Integer.Sparse.mergeBy masterLess reducedTerm989 reducedMerge987 := by decide +kernel

theorem reducedMerge989Check : reducedMerge989 = Integer.Sparse.mergeBy masterLess reducedTerm992 reducedTerm993 := by decide +kernel

theorem reducedMerge990Check : reducedMerge990 = Integer.Sparse.mergeBy masterLess reducedTerm994 reducedTerm995 := by decide +kernel

theorem reducedMerge991Check : reducedMerge991 = Integer.Sparse.mergeBy masterLess reducedMerge989 reducedMerge990 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge992Check : reducedMerge992 = Integer.Sparse.mergeBy masterLess reducedMerge988 reducedMerge991 := by decide +kernel

theorem reducedMerge993Check : reducedMerge993 = Integer.Sparse.mergeBy masterLess reducedTerm996 reducedTerm997 := by decide +kernel

theorem reducedMerge994Check : reducedMerge994 = Integer.Sparse.mergeBy masterLess reducedTerm998 reducedTerm999 := by decide +kernel

theorem reducedMerge995Check : reducedMerge995 = Integer.Sparse.mergeBy masterLess reducedMerge993 reducedMerge994 := by decide +kernel

theorem reducedMerge996Check : reducedMerge996 = Integer.Sparse.mergeBy masterLess reducedTerm1000 reducedTerm1001 := by decide +kernel

theorem reducedMerge997Check : reducedMerge997 = Integer.Sparse.mergeBy masterLess reducedTerm1002 reducedTerm1003 := by decide +kernel

theorem reducedMerge998Check : reducedMerge998 = Integer.Sparse.mergeBy masterLess reducedMerge996 reducedMerge997 := by decide +kernel

theorem reducedMerge999Check : reducedMerge999 = Integer.Sparse.mergeBy masterLess reducedMerge995 reducedMerge998 := by decide +kernel

theorem reducedMerge1000Check : reducedMerge1000 = Integer.Sparse.mergeBy masterLess reducedMerge992 reducedMerge999 := by decide +kernel

theorem reducedMerge1001Check : reducedMerge1001 = Integer.Sparse.mergeBy masterLess reducedTerm1005 reducedTerm1006 := by decide +kernel

theorem reducedMerge1002Check : reducedMerge1002 = Integer.Sparse.mergeBy masterLess reducedTerm1004 reducedMerge1001 := by decide +kernel

theorem reducedMerge1003Check : reducedMerge1003 = Integer.Sparse.mergeBy masterLess reducedTerm1007 reducedTerm1008 := by decide +kernel

theorem reducedMerge1004Check : reducedMerge1004 = Integer.Sparse.mergeBy masterLess reducedTerm1009 reducedTerm1010 := by decide +kernel

theorem reducedMerge1005Check : reducedMerge1005 = Integer.Sparse.mergeBy masterLess reducedMerge1003 reducedMerge1004 := by decide +kernel

theorem reducedMerge1006Check : reducedMerge1006 = Integer.Sparse.mergeBy masterLess reducedMerge1002 reducedMerge1005 := by decide +kernel

theorem reducedMerge1007Check : reducedMerge1007 = Integer.Sparse.mergeBy masterLess reducedTerm1011 reducedTerm1012 := by decide +kernel

theorem reducedMerge1008Check : reducedMerge1008 = Integer.Sparse.mergeBy masterLess reducedTerm1013 reducedTerm1014 := by decide +kernel

theorem reducedMerge1009Check : reducedMerge1009 = Integer.Sparse.mergeBy masterLess reducedMerge1007 reducedMerge1008 := by decide +kernel

theorem reducedMerge1010Check : reducedMerge1010 = Integer.Sparse.mergeBy masterLess reducedTerm1015 reducedTerm1016 := by decide +kernel

theorem reducedMerge1011Check : reducedMerge1011 = Integer.Sparse.mergeBy masterLess reducedTerm1017 reducedTerm1018 := by decide +kernel

theorem reducedMerge1012Check : reducedMerge1012 = Integer.Sparse.mergeBy masterLess reducedMerge1010 reducedMerge1011 := by decide +kernel

theorem reducedMerge1013Check : reducedMerge1013 = Integer.Sparse.mergeBy masterLess reducedMerge1009 reducedMerge1012 := by decide +kernel

theorem reducedMerge1014Check : reducedMerge1014 = Integer.Sparse.mergeBy masterLess reducedMerge1006 reducedMerge1013 := by decide +kernel

theorem reducedMerge1015Check : reducedMerge1015 = Integer.Sparse.mergeBy masterLess reducedMerge1000 reducedMerge1014 := by decide +kernel

theorem reducedMerge1016Check : reducedMerge1016 = Integer.Sparse.mergeBy masterLess reducedMerge986 reducedMerge1015 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1076Check : reducedMerge1076 = Integer.Sparse.mergeBy masterLess reducedMerge1016 reducedMerge1075 := by decide +kernel

theorem reducedMerge1077Check : reducedMerge1077 = Integer.Sparse.mergeBy masterLess reducedTerm1080 reducedTerm1081 := by decide +kernel

theorem reducedMerge1078Check : reducedMerge1078 = Integer.Sparse.mergeBy masterLess reducedTerm1079 reducedMerge1077 := by decide +kernel

theorem reducedMerge1079Check : reducedMerge1079 = Integer.Sparse.mergeBy masterLess reducedTerm1082 reducedTerm1083 := by decide +kernel

theorem reducedMerge1080Check : reducedMerge1080 = Integer.Sparse.mergeBy masterLess reducedTerm1084 reducedTerm1085 := by decide +kernel

theorem reducedMerge1081Check : reducedMerge1081 = Integer.Sparse.mergeBy masterLess reducedMerge1079 reducedMerge1080 := by decide +kernel

theorem reducedMerge1082Check : reducedMerge1082 = Integer.Sparse.mergeBy masterLess reducedMerge1078 reducedMerge1081 := by decide +kernel

theorem reducedMerge1083Check : reducedMerge1083 = Integer.Sparse.mergeBy masterLess reducedTerm1086 reducedTerm1087 := by decide +kernel

theorem reducedMerge1084Check : reducedMerge1084 = Integer.Sparse.mergeBy masterLess reducedTerm1088 reducedTerm1089 := by decide +kernel

theorem reducedMerge1085Check : reducedMerge1085 = Integer.Sparse.mergeBy masterLess reducedMerge1083 reducedMerge1084 := by decide +kernel

theorem reducedMerge1086Check : reducedMerge1086 = Integer.Sparse.mergeBy masterLess reducedTerm1090 reducedTerm1091 := by decide +kernel

theorem reducedMerge1087Check : reducedMerge1087 = Integer.Sparse.mergeBy masterLess reducedTerm1092 reducedTerm1093 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1088Check : reducedMerge1088 = Integer.Sparse.mergeBy masterLess reducedMerge1086 reducedMerge1087 := by decide +kernel

theorem reducedMerge1089Check : reducedMerge1089 = Integer.Sparse.mergeBy masterLess reducedMerge1085 reducedMerge1088 := by decide +kernel

theorem reducedMerge1090Check : reducedMerge1090 = Integer.Sparse.mergeBy masterLess reducedMerge1082 reducedMerge1089 := by decide +kernel

theorem reducedMerge1091Check : reducedMerge1091 = Integer.Sparse.mergeBy masterLess reducedTerm1095 reducedTerm1096 := by decide +kernel

theorem reducedMerge1092Check : reducedMerge1092 = Integer.Sparse.mergeBy masterLess reducedTerm1094 reducedMerge1091 := by decide +kernel

theorem reducedMerge1093Check : reducedMerge1093 = Integer.Sparse.mergeBy masterLess reducedTerm1097 reducedTerm1098 := by decide +kernel

theorem reducedMerge1094Check : reducedMerge1094 = Integer.Sparse.mergeBy masterLess reducedTerm1099 reducedTerm1100 := by decide +kernel

theorem reducedMerge1095Check : reducedMerge1095 = Integer.Sparse.mergeBy masterLess reducedMerge1093 reducedMerge1094 := by decide +kernel

theorem reducedMerge1096Check : reducedMerge1096 = Integer.Sparse.mergeBy masterLess reducedMerge1092 reducedMerge1095 := by decide +kernel

theorem reducedMerge1097Check : reducedMerge1097 = Integer.Sparse.mergeBy masterLess reducedTerm1101 reducedTerm1102 := by decide +kernel

theorem reducedMerge1098Check : reducedMerge1098 = Integer.Sparse.mergeBy masterLess reducedTerm1103 reducedTerm1104 := by decide +kernel

theorem reducedMerge1099Check : reducedMerge1099 = Integer.Sparse.mergeBy masterLess reducedMerge1097 reducedMerge1098 := by decide +kernel

theorem reducedMerge1100Check : reducedMerge1100 = Integer.Sparse.mergeBy masterLess reducedTerm1105 reducedTerm1106 := by decide +kernel

theorem reducedMerge1101Check : reducedMerge1101 = Integer.Sparse.mergeBy masterLess reducedTerm1107 reducedTerm1108 := by decide +kernel

theorem reducedMerge1102Check : reducedMerge1102 = Integer.Sparse.mergeBy masterLess reducedMerge1100 reducedMerge1101 := by decide +kernel

theorem reducedMerge1103Check : reducedMerge1103 = Integer.Sparse.mergeBy masterLess reducedMerge1099 reducedMerge1102 := by decide +kernel

theorem reducedMerge1104Check : reducedMerge1104 = Integer.Sparse.mergeBy masterLess reducedMerge1096 reducedMerge1103 := by decide +kernel

theorem reducedMerge1105Check : reducedMerge1105 = Integer.Sparse.mergeBy masterLess reducedMerge1090 reducedMerge1104 := by decide +kernel

theorem reducedMerge1106Check : reducedMerge1106 = Integer.Sparse.mergeBy masterLess reducedTerm1110 reducedTerm1111 := by decide +kernel

theorem reducedMerge1107Check : reducedMerge1107 = Integer.Sparse.mergeBy masterLess reducedTerm1109 reducedMerge1106 := by decide +kernel

theorem reducedMerge1108Check : reducedMerge1108 = Integer.Sparse.mergeBy masterLess reducedTerm1112 reducedTerm1113 := by decide +kernel

theorem reducedMerge1109Check : reducedMerge1109 = Integer.Sparse.mergeBy masterLess reducedTerm1114 reducedTerm1115 := by decide +kernel

theorem reducedMerge1110Check : reducedMerge1110 = Integer.Sparse.mergeBy masterLess reducedMerge1108 reducedMerge1109 := by decide +kernel

theorem reducedMerge1111Check : reducedMerge1111 = Integer.Sparse.mergeBy masterLess reducedMerge1107 reducedMerge1110 := by decide +kernel

theorem reducedMerge1112Check : reducedMerge1112 = Integer.Sparse.mergeBy masterLess reducedTerm1116 reducedTerm1117 := by decide +kernel

theorem reducedMerge1113Check : reducedMerge1113 = Integer.Sparse.mergeBy masterLess reducedTerm1118 reducedTerm1119 := by decide +kernel

theorem reducedMerge1114Check : reducedMerge1114 = Integer.Sparse.mergeBy masterLess reducedMerge1112 reducedMerge1113 := by decide +kernel

theorem reducedMerge1115Check : reducedMerge1115 = Integer.Sparse.mergeBy masterLess reducedTerm1120 reducedTerm1121 := by decide +kernel

theorem reducedMerge1116Check : reducedMerge1116 = Integer.Sparse.mergeBy masterLess reducedTerm1122 reducedTerm1123 := by decide +kernel

theorem reducedMerge1117Check : reducedMerge1117 = Integer.Sparse.mergeBy masterLess reducedMerge1115 reducedMerge1116 := by decide +kernel

theorem reducedMerge1118Check : reducedMerge1118 = Integer.Sparse.mergeBy masterLess reducedMerge1114 reducedMerge1117 := by decide +kernel

theorem reducedMerge1119Check : reducedMerge1119 = Integer.Sparse.mergeBy masterLess reducedMerge1111 reducedMerge1118 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1120Check : reducedMerge1120 = Integer.Sparse.mergeBy masterLess reducedTerm1125 reducedTerm1126 := by decide +kernel

theorem reducedMerge1121Check : reducedMerge1121 = Integer.Sparse.mergeBy masterLess reducedTerm1124 reducedMerge1120 := by decide +kernel

theorem reducedMerge1122Check : reducedMerge1122 = Integer.Sparse.mergeBy masterLess reducedTerm1127 reducedTerm1128 := by decide +kernel

theorem reducedMerge1123Check : reducedMerge1123 = Integer.Sparse.mergeBy masterLess reducedTerm1129 reducedTerm1130 := by decide +kernel

theorem reducedMerge1124Check : reducedMerge1124 = Integer.Sparse.mergeBy masterLess reducedMerge1122 reducedMerge1123 := by decide +kernel

theorem reducedMerge1125Check : reducedMerge1125 = Integer.Sparse.mergeBy masterLess reducedMerge1121 reducedMerge1124 := by decide +kernel

theorem reducedMerge1126Check : reducedMerge1126 = Integer.Sparse.mergeBy masterLess reducedTerm1131 reducedTerm1132 := by decide +kernel

theorem reducedMerge1127Check : reducedMerge1127 = Integer.Sparse.mergeBy masterLess reducedTerm1133 reducedTerm1134 := by decide +kernel

theorem reducedMerge1128Check : reducedMerge1128 = Integer.Sparse.mergeBy masterLess reducedMerge1126 reducedMerge1127 := by decide +kernel

theorem reducedMerge1129Check : reducedMerge1129 = Integer.Sparse.mergeBy masterLess reducedTerm1135 reducedTerm1136 := by decide +kernel

theorem reducedMerge1130Check : reducedMerge1130 = Integer.Sparse.mergeBy masterLess reducedTerm1137 reducedTerm1138 := by decide +kernel

theorem reducedMerge1131Check : reducedMerge1131 = Integer.Sparse.mergeBy masterLess reducedMerge1129 reducedMerge1130 := by decide +kernel

theorem reducedMerge1132Check : reducedMerge1132 = Integer.Sparse.mergeBy masterLess reducedMerge1128 reducedMerge1131 := by decide +kernel

theorem reducedMerge1133Check : reducedMerge1133 = Integer.Sparse.mergeBy masterLess reducedMerge1125 reducedMerge1132 := by decide +kernel

theorem reducedMerge1134Check : reducedMerge1134 = Integer.Sparse.mergeBy masterLess reducedMerge1119 reducedMerge1133 := by decide +kernel

theorem reducedMerge1135Check : reducedMerge1135 = Integer.Sparse.mergeBy masterLess reducedMerge1105 reducedMerge1134 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1195Check : reducedMerge1195 = Integer.Sparse.mergeBy masterLess reducedMerge1135 reducedMerge1194 := by decide +kernel

theorem reducedMerge1196Check : reducedMerge1196 = Integer.Sparse.mergeBy masterLess reducedMerge1076 reducedMerge1195 := by decide +kernel

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

theorem reducedTermEval959 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm959 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm959 (originalVector B) := by
  rw [reducedTermArithmetic959, ← sound2556 B hB hF]
  change (-762973624782028800000 : ℝ) * mixedMoment B node2556 node2556Labels =
    (37623398400 : ℝ) * (((-20279232000 : ℤ) : ℝ) * mixedMoment B node2556 node2556Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval960 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm960 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm960 (originalVector B) := by
  rw [reducedTermArithmetic960, ← sound2557 B hB hF]
  change (-827530229555527680000 : ℝ) * mixedMoment B node2557 node2557Labels =
    (37623398400 : ℝ) * (((-21995095200 : ℤ) : ℝ) * mixedMoment B node2557 node2557Labels + 0)
  ring

theorem reducedTermEval961 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm961 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm961 (originalVector B) := by
  rw [reducedTermArithmetic961, ← sound2558 B hB hF]
  change (3350500907776081920000 : ℝ) * mixedMoment B node2558 node2558Labels =
    (37623398400 : ℝ) * ((89053648800 : ℝ) * mixedMoment B node2558 node2558Labels + 0)
  ring

theorem reducedTermEval962 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm962 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm962 (originalVector B) := by
  rw [reducedTermArithmetic962, ← sound2560 B hB hF]
  change (-1308617765518049280000 : ℝ) * mixedMoment B node2560 node2560Labels =
    (37623398400 : ℝ) * (((-34782019200 : ℤ) : ℝ) * mixedMoment B node2560 node2560Labels + 0)
  ring

theorem reducedTermEval963 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm963 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm963 (originalVector B) := by
  rw [reducedTermArithmetic963, ← sound2561 B hB hF]
  change (-8081533245759160320000 : ℝ) * mixedMoment B node2561 node2561Labels =
    (37623398400 : ℝ) * (((-214800724800 : ℤ) : ℝ) * mixedMoment B node2561 node2561Labels + 0)
  ring

theorem reducedTermEval964 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm964 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm964 (originalVector B) := by
  rw [reducedTermArithmetic964, ← sound2566 B hB hF]
  change (54778388874854400000 : ℝ) * mixedMoment B node2566 node2566Labels =
    (37623398400 : ℝ) * ((1455966000 : ℝ) * mixedMoment B node2566 node2566Labels + 0)
  ring

theorem reducedTermEval965 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm965 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm965 (originalVector B) := by
  rw [reducedTermArithmetic965, ← sound2569 B hB hF]
  change (-54778388874854400000 : ℝ) * mixedMoment B node2569 node2569Labels =
    (37623398400 : ℝ) * (((-1455966000 : ℤ) : ℝ) * mixedMoment B node2569 node2569Labels + 0)
  ring

theorem reducedTermEval966 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm966 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm966 (originalVector B) := by
  rw [reducedTermArithmetic966, ← sound2573 B hB hF]
  change (3475493000755937280000 : ℝ) * mixedMoment B node2573 node2573Labels =
    (37623398400 : ℝ) * ((92375839200 : ℝ) * mixedMoment B node2573 node2573Labels + 0)
  ring

theorem reducedTermEval967 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm967 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm967 (originalVector B) := by
  rw [reducedTermArithmetic967, ← sound2575 B hB hF]
  change (7730575112285061120000 : ℝ) * mixedMoment B node2575 node2575Labels =
    (37623398400 : ℝ) * ((205472536800 : ℝ) * mixedMoment B node2575 node2575Labels + 0)
  ring

theorem reducedTermEval968 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm968 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm968 (originalVector B) := by
  rw [reducedTermArithmetic968, ← sound2587 B hB hF]
  change (2089015568665804800000 : ℝ) * mixedMoment B node2587 node2587Labels =
    (37623398400 : ℝ) * ((55524372000 : ℝ) * mixedMoment B node2587 node2587Labels + 0)
  ring

theorem reducedTermEval969 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm969 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm969 (originalVector B) := by
  rw [reducedTermArithmetic969, ← sound2589 B hB hF]
  change (-878316128737689600000 : ℝ) * mixedMoment B node2589 node2589Labels =
    (37623398400 : ℝ) * (((-23344944000 : ℤ) : ℝ) * mixedMoment B node2589 node2589Labels + 0)
  ring

theorem reducedTermEval970 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm970 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm970 (originalVector B) := by
  rw [reducedTermArithmetic970, ← sound2590 B hB hF]
  change (9764819380324270080000 : ℝ) * mixedMoment B node2590 node2590Labels =
    (37623398400 : ℝ) * ((259541131200 : ℝ) * mixedMoment B node2590 node2590Labels + 0)
  ring

theorem reducedTermEval971 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm971 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm971 (originalVector B) := by
  rw [reducedTermArithmetic971, ← sound2591 B hB hF]
  change (-2089015568665804800000 : ℝ) * mixedMoment B node2591 node2591Labels =
    (37623398400 : ℝ) * (((-55524372000 : ℤ) : ℝ) * mixedMoment B node2591 node2591Labels + 0)
  ring

theorem reducedTermEval972 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm972 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm972 (originalVector B) := by
  rw [reducedTermArithmetic972, ← sound2600 B hB hF]
  change (6525212987851407360000 : ℝ) * mixedMoment B node2600 node2600Labels =
    (37623398400 : ℝ) * ((173434970400 : ℝ) * mixedMoment B node2600 node2600Labels + 0)
  ring

theorem reducedTermEval973 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm973 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm973 (originalVector B) := by
  rw [reducedTermArithmetic973, ← sound2603 B hB hF]
  change (4404201698619555840000 : ℝ) * mixedMoment B node2603 node2603Labels =
    (37623398400 : ℝ) * ((117060177600 : ℝ) * mixedMoment B node2603 node2603Labels + 0)
  ring

theorem reducedTermEval974 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm974 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm974 (originalVector B) := by
  rw [reducedTermArithmetic974, ← sound2614 B hB hF]
  change (54778388874854400000 : ℝ) * mixedMoment B node2614 node2614Labels =
    (37623398400 : ℝ) * ((1455966000 : ℝ) * mixedMoment B node2614 node2614Labels + 0)
  ring

theorem reducedTermEval975 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm975 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm975 (originalVector B) := by
  rw [reducedTermArithmetic975, ← sound2617 B hB hF]
  change (-9280530725231001600000 : ℝ) * mixedMoment B node2617 node2617Labels =
    (37623398400 : ℝ) * (((-246669124000 : ℤ) : ℝ) * mixedMoment B node2617 node2617Labels + 0)
  ring

theorem reducedTermEval976 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm976 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm976 (originalVector B) := by
  rw [reducedTermArithmetic976, ← sound2618 B hB hF]
  change (34864691456596377600000 : ℝ) * mixedMoment B node2618 node2618Labels =
    (37623398400 : ℝ) * ((926675764000 : ℝ) * mixedMoment B node2618 node2618Labels + 0)
  ring

theorem reducedTermEval977 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm977 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm977 (originalVector B) := by
  rw [reducedTermArithmetic977, ← sound2620 B hB hF]
  change (10563661873945313280000 : ℝ) * mixedMoment B node2620 node2620Labels =
    (37623398400 : ℝ) * ((280773729200 : ℝ) * mixedMoment B node2620 node2620Labels + 0)
  ring

theorem reducedTermEval978 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm978 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm978 (originalVector B) := by
  rw [reducedTermArithmetic978, ← sound2631 B hB hF]
  change (-15111984861079142400000 : ℝ) * mixedMoment B node2631 node2631Labels =
    (37623398400 : ℝ) * (((-401664536000 : ℤ) : ℝ) * mixedMoment B node2631 node2631Labels + 0)
  ring

theorem reducedTermEval979 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm979 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm979 (originalVector B) := by
  rw [reducedTermArithmetic979, ← sound2632 B hB hF]
  change (-6403063116880281600000 : ℝ) * mixedMoment B node2632 node2632Labels =
    (37623398400 : ℝ) * (((-170188324000 : ℤ) : ℝ) * mixedMoment B node2632 node2632Labels + 0)
  ring

theorem reducedTermEval980 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm980 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm980 (originalVector B) := by
  rw [reducedTermArithmetic980, ← sound2633 B hB hF]
  change (15111984861079142400000 : ℝ) * mixedMoment B node2633 node2633Labels =
    (37623398400 : ℝ) * ((401664536000 : ℝ) * mixedMoment B node2633 node2633Labels + 0)
  ring

theorem reducedTermEval981 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm981 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm981 (originalVector B) := by
  rw [reducedTermArithmetic981, ← sound2635 B hB hF]
  change (3201531558440140800000 : ℝ) * mixedMoment B node2635 node2635Labels =
    (37623398400 : ℝ) * ((85094162000 : ℝ) * mixedMoment B node2635 node2635Labels + 0)
  ring

theorem reducedTermEval982 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm982 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm982 (originalVector B) := by
  rw [reducedTermArithmetic982, ← sound2641 B hB hF]
  change (7417350658916352000000 : ℝ) * mixedMoment B node2641 node2641Labels =
    (37623398400 : ℝ) * ((197147280000 : ℝ) * mixedMoment B node2641 node2641Labels + 0)
  ring

theorem reducedTermEval983 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm983 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm983 (originalVector B) := by
  rw [reducedTermArithmetic983, ← sound2643 B hB hF]
  change (7685347844476108800000 : ℝ) * mixedMoment B node2643 node2643Labels =
    (37623398400 : ℝ) * ((204270432000 : ℝ) * mixedMoment B node2643 node2643Labels + 0)
  ring

theorem reducedTermEval984 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm984 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm984 (originalVector B) := by
  rw [reducedTermArithmetic984, ← sound2652 B hB hF]
  change (4097268088154357760000 : ℝ) * mixedMoment B node2652 node2652Labels =
    (37623398400 : ℝ) * ((108902126400 : ℝ) * mixedMoment B node2652 node2652Labels + 0)
  ring

theorem reducedTermEval985 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm985 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm985 (originalVector B) := by
  rw [reducedTermArithmetic985, ← sound2653 B hB hF]
  change (-2900413559198711808000 : ℝ) * mixedMoment B node2653 node2653Labels =
    (37623398400 : ℝ) * (((-77090685120 : ℤ) : ℝ) * mixedMoment B node2653 node2653Labels + 0)
  ring

theorem reducedTermEval986 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm986 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm986 (originalVector B) := by
  rw [reducedTermArithmetic986, ← sound2654 B hB hF]
  change (-59568121389514752000 : ℝ) * mixedMoment B node2654 node2654Labels =
    (37623398400 : ℝ) * (((-1583273280 : ℤ) : ℝ) * mixedMoment B node2654 node2654Labels + 0)
  ring

theorem reducedTermEval987 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm987 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm987 (originalVector B) := by
  rw [reducedTermArithmetic987, ← sound2655 B hB hF]
  change (414737902356922368000 : ℝ) * mixedMoment B node2655 node2655Labels =
    (37623398400 : ℝ) * ((11023403520 : ℝ) * mixedMoment B node2655 node2655Labels + 0)
  ring

theorem reducedTermEval988 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm988 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm988 (originalVector B) := by
  rw [reducedTermArithmetic988, ← sound2656 B hB hF]
  change (2451504521281536000000 : ℝ) * mixedMoment B node2656 node2656Labels =
    (37623398400 : ℝ) * ((65159040000 : ℝ) * mixedMoment B node2656 node2656Labels + 0)
  ring

theorem reducedTermEval989 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm989 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm989 (originalVector B) := by
  rw [reducedTermArithmetic989, ← sound2657 B hB hF]
  change (3659948525761855488000 : ℝ) * mixedMoment B node2657 node2657Labels =
    (37623398400 : ℝ) * ((97278520320 : ℝ) * mixedMoment B node2657 node2657Labels + 0)
  ring

theorem reducedTermEval990 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm990 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm990 (originalVector B) := by
  rw [reducedTermArithmetic990, ← sound2658 B hB hF]
  change (-31848465594580992000 : ℝ) * mixedMoment B node2658 node2658Labels =
    (37623398400 : ℝ) * (((-846506880 : ℤ) : ℝ) * mixedMoment B node2658 node2658Labels + 0)
  ring

theorem reducedTermEval991 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm991 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm991 (originalVector B) := by
  rw [reducedTermArithmetic991, ← sound2659 B hB hF]
  change (-4218827410224709632000 : ℝ) * mixedMoment B node2659 node2659Labels =
    (37623398400 : ℝ) * (((-112133076480 : ℤ) : ℝ) * mixedMoment B node2659 node2659Labels + 0)
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

theorem reducedMergeEval958 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge958 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge958 (originalVector B) := by
  rw [reducedMerge958Check, Integer.Sparse.eval_mergeBy, reducedTermEval960 B hB hF, reducedTermEval961 B hB hF]
  rw [originalMerge958, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval959 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge959 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge959 (originalVector B) := by
  rw [reducedMerge959Check, Integer.Sparse.eval_mergeBy, reducedTermEval959 B hB hF, reducedMergeEval958 B hB hF]
  rw [originalMerge959, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval992 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm992 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm992 (originalVector B) := by
  rw [reducedTermArithmetic992, ← sound2661 B hB hF]
  change (2542985543602667520000 : ℝ) * mixedMoment B node2661 node2661Labels =
    (37623398400 : ℝ) * ((67590532800 : ℝ) * mixedMoment B node2661 node2661Labels + 0)
  ring

theorem reducedTermEval993 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm993 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm993 (originalVector B) := by
  rw [reducedTermArithmetic993, ← sound2662 B hB hF]
  change (-95323232121126912000 : ℝ) * mixedMoment B node2662 node2662Labels =
    (37623398400 : ℝ) * (((-2533615680 : ℤ) : ℝ) * mixedMoment B node2662 node2662Labels + 0)
  ring

theorem reducedTermEval994 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm994 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm994 (originalVector B) := by
  rw [reducedTermArithmetic994, ← sound2664 B hB hF]
  change (888215115745198080000 : ℝ) * mixedMoment B node2664 node2664Labels =
    (37623398400 : ℝ) * ((23608051200 : ℝ) * mixedMoment B node2664 node2664Labels + 0)
  ring

theorem reducedTermEval995 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm995 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm995 (originalVector B) := by
  rw [reducedTermArithmetic995, ← sound2669 B hB hF]
  change (1951341470849433600000 : ℝ) * mixedMoment B node2669 node2669Labels =
    (37623398400 : ℝ) * ((51865104000 : ℝ) * mixedMoment B node2669 node2669Labels + 0)
  ring

theorem reducedTermEval996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm996 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm996 (originalVector B) := by
  rw [reducedTermArithmetic996, ← sound2670 B hB hF]
  change (-4302905736953069568000 : ℝ) * mixedMoment B node2670 node2670Labels =
    (37623398400 : ℝ) * (((-114367811520 : ℤ) : ℝ) * mixedMoment B node2670 node2670Labels + 0)
  ring

theorem reducedTermEval997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm997 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm997 (originalVector B) := by
  rw [reducedTermArithmetic997, ← sound2673 B hB hF]
  change (3169748139186585600000 : ℝ) * mixedMoment B node2673 node2673Labels =
    (37623398400 : ℝ) * ((84249384000 : ℝ) * mixedMoment B node2673 node2673Labels + 0)
  ring

theorem reducedTermEval998 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm998 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm998 (originalVector B) := by
  rw [reducedTermArithmetic998, ← sound2676 B hB hF]
  change (2197036481036156928000 : ℝ) * mixedMoment B node2676 node2676Labels =
    (37623398400 : ℝ) * ((58395481920 : ℝ) * mixedMoment B node2676 node2676Labels + 0)
  ring

theorem reducedTermEval999 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm999 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm999 (originalVector B) := by
  rw [reducedTermArithmetic999, ← sound2677 B hB hF]
  change (3660221256271921152000 : ℝ) * mixedMoment B node2677 node2677Labels =
    (37623398400 : ℝ) * ((97285769280 : ℝ) * mixedMoment B node2677 node2677Labels + 0)
  ring

theorem reducedTermEval1000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1000 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1000 (originalVector B) := by
  rw [reducedTermArithmetic1000, ← sound2678 B hB hF]
  change (1249731921884479488000 : ℝ) * mixedMoment B node2678 node2678Labels =
    (37623398400 : ℝ) * ((33216880320 : ℝ) * mixedMoment B node2678 node2678Labels + 0)
  ring

theorem reducedTermEval1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1001 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1001 (originalVector B) := by
  rw [reducedTermArithmetic1001, ← sound2680 B hB hF]
  change (328270556047343616000 : ℝ) * mixedMoment B node2680 node2680Labels =
    (37623398400 : ℝ) * ((8725170240 : ℝ) * mixedMoment B node2680 node2680Labels + 0)
  ring

theorem reducedTermEval1002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1002 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1002 (originalVector B) := by
  rw [reducedTermArithmetic1002, ← sound2681 B hB hF]
  change (-304877566989434880000 : ℝ) * mixedMoment B node2681 node2681Labels =
    (37623398400 : ℝ) * (((-8103403200 : ℤ) : ℝ) * mixedMoment B node2681 node2681Labels + 0)
  ring

theorem reducedTermEval1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1003 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1003 (originalVector B) := by
  rw [reducedTermArithmetic1003, ← sound2682 B hB hF]
  change (-2451504521281536000000 : ℝ) * mixedMoment B node2682 node2682Labels =
    (37623398400 : ℝ) * (((-65159040000 : ℤ) : ℝ) * mixedMoment B node2682 node2682Labels + 0)
  ring

theorem reducedTermEval1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1004 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1004 (originalVector B) := by
  rw [reducedTermArithmetic1004, ← sound2683 B hB hF]
  change (-2711614482074566656000 : ℝ) * mixedMoment B node2683 node2683Labels =
    (37623398400 : ℝ) * (((-72072555840 : ℤ) : ℝ) * mixedMoment B node2683 node2683Labels + 0)
  ring

theorem reducedTermEval1005 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1005 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1005 (originalVector B) := by
  rw [reducedTermArithmetic1005, ← sound2687 B hB hF]
  change (2753869669962743808000 : ℝ) * mixedMoment B node2687 node2687Labels =
    (37623398400 : ℝ) * ((73195665120 : ℝ) * mixedMoment B node2687 node2687Labels + 0)
  ring

theorem reducedTermEval1006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1006 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1006 (originalVector B) := by
  rw [reducedTermArithmetic1006, ← sound2688 B hB hF]
  change (2124806707563724800000 : ℝ) * mixedMoment B node2688 node2688Labels =
    (37623398400 : ℝ) * ((56475672000 : ℝ) * mixedMoment B node2688 node2688Labels + 0)
  ring

theorem reducedTermEval1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1007 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1007 (originalVector B) := by
  rw [reducedTermArithmetic1007, ← sound2690 B hB hF]
  change (-2124806707563724800000 : ℝ) * mixedMoment B node2690 node2690Labels =
    (37623398400 : ℝ) * (((-56475672000 : ℤ) : ℝ) * mixedMoment B node2690 node2690Labels + 0)
  ring

theorem reducedTermEval1008 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1008 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1008 (originalVector B) := by
  rw [reducedTermArithmetic1008, ← sound2697 B hB hF]
  change (665857147118026752000 : ℝ) * mixedMoment B node2697 node2697Labels =
    (37623398400 : ℝ) * ((17697953280 : ℝ) * mixedMoment B node2697 node2697Labels + 0)
  ring

theorem reducedTermEval1009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1009 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1009 (originalVector B) := by
  rw [reducedTermArithmetic1009, ← sound2698 B hB hF]
  change (-3210049119603916800000 : ℝ) * mixedMoment B node2698 node2698Labels =
    (37623398400 : ℝ) * (((-85320552000 : ℤ) : ℝ) * mixedMoment B node2698 node2698Labels + 0)
  ring

theorem reducedTermEval1010 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1010 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1010 (originalVector B) := by
  rw [reducedTermArithmetic1010, ← sound2700 B hB hF]
  change (-450757951040323584000 : ℝ) * mixedMoment B node2700 node2700Labels =
    (37623398400 : ℝ) * (((-11980787760 : ℤ) : ℝ) * mixedMoment B node2700 node2700Labels + 0)
  ring

theorem reducedTermEval1011 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1011 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1011 (originalVector B) := by
  rw [reducedTermArithmetic1011, ← sound2702 B hB hF]
  change (-423147689038577664000 : ℝ) * mixedMoment B node2702 node2702Labels =
    (37623398400 : ℝ) * (((-11246928960 : ℤ) : ℝ) * mixedMoment B node2702 node2702Labels + 0)
  ring

theorem reducedTermEval1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1012 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1012 (originalVector B) := by
  rw [reducedTermArithmetic1012, ← sound2706 B hB hF]
  change (4172340565215019008000 : ℝ) * mixedMoment B node2706 node2706Labels =
    (37623398400 : ℝ) * ((110897493120 : ℝ) * mixedMoment B node2706 node2706Labels + 0)
  ring

theorem reducedTermEval1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1013 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1013 (originalVector B) := by
  rw [reducedTermArithmetic1013, ← sound2707 B hB hF]
  change (-847409560407244800000 : ℝ) * mixedMoment B node2707 node2707Labels =
    (37623398400 : ℝ) * (((-22523472000 : ℤ) : ℝ) * mixedMoment B node2707 node2707Labels + 0)
  ring

theorem reducedTermEval1014 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1014 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1014 (originalVector B) := by
  rw [reducedTermArithmetic1014, ← sound2708 B hB hF]
  change (2180351629537837056000 : ℝ) * mixedMoment B node2708 node2708Labels =
    (37623398400 : ℝ) * ((57952011840 : ℝ) * mixedMoment B node2708 node2708Labels + 0)
  ring

theorem reducedTermEval1015 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1015 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1015 (originalVector B) := by
  rw [reducedTermArithmetic1015, ← sound2709 B hB hF]
  change (21899673936219340800000 : ℝ) * mixedMoment B node2709 node2709Labels =
    (37623398400 : ℝ) * ((582075912000 : ℝ) * mixedMoment B node2709 node2709Labels + 0)
  ring

theorem reducedTermEval1016 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1016 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1016 (originalVector B) := by
  rw [reducedTermArithmetic1016, ← sound2710 B hB hF]
  change (3772583761333911552000 : ℝ) * mixedMoment B node2710 node2710Labels =
    (37623398400 : ℝ) * ((100272275280 : ℝ) * mixedMoment B node2710 node2710Labels + 0)
  ring

theorem reducedTermEval1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1017 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1017 (originalVector B) := by
  rw [reducedTermArithmetic1017, ← sound2712 B hB hF]
  change (669848715789926400000 : ℝ) * mixedMoment B node2712 node2712Labels =
    (37623398400 : ℝ) * ((17804046000 : ℝ) * mixedMoment B node2712 node2712Labels + 0)
  ring

theorem reducedTermEval1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1018 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1018 (originalVector B) := by
  rw [reducedTermArithmetic1018, ← sound2714 B hB hF]
  change (-18738707098219315200000 : ℝ) * mixedMoment B node2714 node2714Labels =
    (37623398400 : ℝ) * (((-498059928000 : ℤ) : ℝ) * mixedMoment B node2714 node2714Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval960 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge960 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge960 (originalVector B) := by
  rw [reducedMerge960Check, Integer.Sparse.eval_mergeBy, reducedTermEval962 B hB hF, reducedTermEval963 B hB hF]
  rw [originalMerge960, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval961 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge961 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge961 (originalVector B) := by
  rw [reducedMerge961Check, Integer.Sparse.eval_mergeBy, reducedTermEval964 B hB hF, reducedTermEval965 B hB hF]
  rw [originalMerge961, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval962 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge962 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge962 (originalVector B) := by
  rw [reducedMerge962Check, Integer.Sparse.eval_mergeBy, reducedMergeEval960 B hB hF, reducedMergeEval961 B hB hF]
  rw [originalMerge962, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval963 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge963 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge963 (originalVector B) := by
  rw [reducedMerge963Check, Integer.Sparse.eval_mergeBy, reducedMergeEval959 B hB hF, reducedMergeEval962 B hB hF]
  rw [originalMerge963, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval964 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge964 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge964 (originalVector B) := by
  rw [reducedMerge964Check, Integer.Sparse.eval_mergeBy, reducedTermEval966 B hB hF, reducedTermEval967 B hB hF]
  rw [originalMerge964, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval965 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge965 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge965 (originalVector B) := by
  rw [reducedMerge965Check, Integer.Sparse.eval_mergeBy, reducedTermEval968 B hB hF, reducedTermEval969 B hB hF]
  rw [originalMerge965, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval966 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge966 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge966 (originalVector B) := by
  rw [reducedMerge966Check, Integer.Sparse.eval_mergeBy, reducedMergeEval964 B hB hF, reducedMergeEval965 B hB hF]
  rw [originalMerge966, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval967 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge967 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge967 (originalVector B) := by
  rw [reducedMerge967Check, Integer.Sparse.eval_mergeBy, reducedTermEval970 B hB hF, reducedTermEval971 B hB hF]
  rw [originalMerge967, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval968 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge968 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge968 (originalVector B) := by
  rw [reducedMerge968Check, Integer.Sparse.eval_mergeBy, reducedTermEval972 B hB hF, reducedTermEval973 B hB hF]
  rw [originalMerge968, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval969 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge969 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge969 (originalVector B) := by
  rw [reducedMerge969Check, Integer.Sparse.eval_mergeBy, reducedMergeEval967 B hB hF, reducedMergeEval968 B hB hF]
  rw [originalMerge969, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval970 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge970 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge970 (originalVector B) := by
  rw [reducedMerge970Check, Integer.Sparse.eval_mergeBy, reducedMergeEval966 B hB hF, reducedMergeEval969 B hB hF]
  rw [originalMerge970, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval971 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge971 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge971 (originalVector B) := by
  rw [reducedMerge971Check, Integer.Sparse.eval_mergeBy, reducedMergeEval963 B hB hF, reducedMergeEval970 B hB hF]
  rw [originalMerge971, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval972 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge972 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge972 (originalVector B) := by
  rw [reducedMerge972Check, Integer.Sparse.eval_mergeBy, reducedTermEval975 B hB hF, reducedTermEval976 B hB hF]
  rw [originalMerge972, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval973 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge973 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge973 (originalVector B) := by
  rw [reducedMerge973Check, Integer.Sparse.eval_mergeBy, reducedTermEval974 B hB hF, reducedMergeEval972 B hB hF]
  rw [originalMerge973, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval974 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge974 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge974 (originalVector B) := by
  rw [reducedMerge974Check, Integer.Sparse.eval_mergeBy, reducedTermEval977 B hB hF, reducedTermEval978 B hB hF]
  rw [originalMerge974, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval975 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge975 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge975 (originalVector B) := by
  rw [reducedMerge975Check, Integer.Sparse.eval_mergeBy, reducedTermEval979 B hB hF, reducedTermEval980 B hB hF]
  rw [originalMerge975, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval976 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge976 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge976 (originalVector B) := by
  rw [reducedMerge976Check, Integer.Sparse.eval_mergeBy, reducedMergeEval974 B hB hF, reducedMergeEval975 B hB hF]
  rw [originalMerge976, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval977 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge977 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge977 (originalVector B) := by
  rw [reducedMerge977Check, Integer.Sparse.eval_mergeBy, reducedMergeEval973 B hB hF, reducedMergeEval976 B hB hF]
  rw [originalMerge977, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval978 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge978 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge978 (originalVector B) := by
  rw [reducedMerge978Check, Integer.Sparse.eval_mergeBy, reducedTermEval981 B hB hF, reducedTermEval982 B hB hF]
  rw [originalMerge978, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval979 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge979 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge979 (originalVector B) := by
  rw [reducedMerge979Check, Integer.Sparse.eval_mergeBy, reducedTermEval983 B hB hF, reducedTermEval984 B hB hF]
  rw [originalMerge979, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval980 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge980 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge980 (originalVector B) := by
  rw [reducedMerge980Check, Integer.Sparse.eval_mergeBy, reducedMergeEval978 B hB hF, reducedMergeEval979 B hB hF]
  rw [originalMerge980, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval981 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge981 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge981 (originalVector B) := by
  rw [reducedMerge981Check, Integer.Sparse.eval_mergeBy, reducedTermEval985 B hB hF, reducedTermEval986 B hB hF]
  rw [originalMerge981, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval982 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge982 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge982 (originalVector B) := by
  rw [reducedMerge982Check, Integer.Sparse.eval_mergeBy, reducedTermEval987 B hB hF, reducedTermEval988 B hB hF]
  rw [originalMerge982, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval983 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge983 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge983 (originalVector B) := by
  rw [reducedMerge983Check, Integer.Sparse.eval_mergeBy, reducedMergeEval981 B hB hF, reducedMergeEval982 B hB hF]
  rw [originalMerge983, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval984 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge984 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge984 (originalVector B) := by
  rw [reducedMerge984Check, Integer.Sparse.eval_mergeBy, reducedMergeEval980 B hB hF, reducedMergeEval983 B hB hF]
  rw [originalMerge984, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval985 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge985 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge985 (originalVector B) := by
  rw [reducedMerge985Check, Integer.Sparse.eval_mergeBy, reducedMergeEval977 B hB hF, reducedMergeEval984 B hB hF]
  rw [originalMerge985, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval986 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge986 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge986 (originalVector B) := by
  rw [reducedMerge986Check, Integer.Sparse.eval_mergeBy, reducedMergeEval971 B hB hF, reducedMergeEval985 B hB hF]
  rw [originalMerge986, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval987 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge987 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge987 (originalVector B) := by
  rw [reducedMerge987Check, Integer.Sparse.eval_mergeBy, reducedTermEval990 B hB hF, reducedTermEval991 B hB hF]
  rw [originalMerge987, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval988 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge988 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge988 (originalVector B) := by
  rw [reducedMerge988Check, Integer.Sparse.eval_mergeBy, reducedTermEval989 B hB hF, reducedMergeEval987 B hB hF]
  rw [originalMerge988, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval989 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge989 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge989 (originalVector B) := by
  rw [reducedMerge989Check, Integer.Sparse.eval_mergeBy, reducedTermEval992 B hB hF, reducedTermEval993 B hB hF]
  rw [originalMerge989, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval990 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge990 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge990 (originalVector B) := by
  rw [reducedMerge990Check, Integer.Sparse.eval_mergeBy, reducedTermEval994 B hB hF, reducedTermEval995 B hB hF]
  rw [originalMerge990, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval991 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge991 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge991 (originalVector B) := by
  rw [reducedMerge991Check, Integer.Sparse.eval_mergeBy, reducedMergeEval989 B hB hF, reducedMergeEval990 B hB hF]
  rw [originalMerge991, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval992 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge992 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge992 (originalVector B) := by
  rw [reducedMerge992Check, Integer.Sparse.eval_mergeBy, reducedMergeEval988 B hB hF, reducedMergeEval991 B hB hF]
  rw [originalMerge992, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval993 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge993 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge993 (originalVector B) := by
  rw [reducedMerge993Check, Integer.Sparse.eval_mergeBy, reducedTermEval996 B hB hF, reducedTermEval997 B hB hF]
  rw [originalMerge993, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval994 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge994 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge994 (originalVector B) := by
  rw [reducedMerge994Check, Integer.Sparse.eval_mergeBy, reducedTermEval998 B hB hF, reducedTermEval999 B hB hF]
  rw [originalMerge994, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval995 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge995 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge995 (originalVector B) := by
  rw [reducedMerge995Check, Integer.Sparse.eval_mergeBy, reducedMergeEval993 B hB hF, reducedMergeEval994 B hB hF]
  rw [originalMerge995, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge996 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge996 (originalVector B) := by
  rw [reducedMerge996Check, Integer.Sparse.eval_mergeBy, reducedTermEval1000 B hB hF, reducedTermEval1001 B hB hF]
  rw [originalMerge996, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge997 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge997 (originalVector B) := by
  rw [reducedMerge997Check, Integer.Sparse.eval_mergeBy, reducedTermEval1002 B hB hF, reducedTermEval1003 B hB hF]
  rw [originalMerge997, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval998 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge998 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge998 (originalVector B) := by
  rw [reducedMerge998Check, Integer.Sparse.eval_mergeBy, reducedMergeEval996 B hB hF, reducedMergeEval997 B hB hF]
  rw [originalMerge998, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval999 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge999 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge999 (originalVector B) := by
  rw [reducedMerge999Check, Integer.Sparse.eval_mergeBy, reducedMergeEval995 B hB hF, reducedMergeEval998 B hB hF]
  rw [originalMerge999, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1000 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1000 (originalVector B) := by
  rw [reducedMerge1000Check, Integer.Sparse.eval_mergeBy, reducedMergeEval992 B hB hF, reducedMergeEval999 B hB hF]
  rw [originalMerge1000, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1001 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1001 (originalVector B) := by
  rw [reducedMerge1001Check, Integer.Sparse.eval_mergeBy, reducedTermEval1005 B hB hF, reducedTermEval1006 B hB hF]
  rw [originalMerge1001, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1002 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1002 (originalVector B) := by
  rw [reducedMerge1002Check, Integer.Sparse.eval_mergeBy, reducedTermEval1004 B hB hF, reducedMergeEval1001 B hB hF]
  rw [originalMerge1002, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1003 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1003 (originalVector B) := by
  rw [reducedMerge1003Check, Integer.Sparse.eval_mergeBy, reducedTermEval1007 B hB hF, reducedTermEval1008 B hB hF]
  rw [originalMerge1003, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1004 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1004 (originalVector B) := by
  rw [reducedMerge1004Check, Integer.Sparse.eval_mergeBy, reducedTermEval1009 B hB hF, reducedTermEval1010 B hB hF]
  rw [originalMerge1004, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1005 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1005 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1005 (originalVector B) := by
  rw [reducedMerge1005Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1003 B hB hF, reducedMergeEval1004 B hB hF]
  rw [originalMerge1005, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1006 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1006 (originalVector B) := by
  rw [reducedMerge1006Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1002 B hB hF, reducedMergeEval1005 B hB hF]
  rw [originalMerge1006, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1007 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1007 (originalVector B) := by
  rw [reducedMerge1007Check, Integer.Sparse.eval_mergeBy, reducedTermEval1011 B hB hF, reducedTermEval1012 B hB hF]
  rw [originalMerge1007, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1008 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1008 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1008 (originalVector B) := by
  rw [reducedMerge1008Check, Integer.Sparse.eval_mergeBy, reducedTermEval1013 B hB hF, reducedTermEval1014 B hB hF]
  rw [originalMerge1008, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1009 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1009 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1009 (originalVector B) := by
  rw [reducedMerge1009Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1007 B hB hF, reducedMergeEval1008 B hB hF]
  rw [originalMerge1009, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1010 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1010 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1010 (originalVector B) := by
  rw [reducedMerge1010Check, Integer.Sparse.eval_mergeBy, reducedTermEval1015 B hB hF, reducedTermEval1016 B hB hF]
  rw [originalMerge1010, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1011 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1011 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1011 (originalVector B) := by
  rw [reducedMerge1011Check, Integer.Sparse.eval_mergeBy, reducedTermEval1017 B hB hF, reducedTermEval1018 B hB hF]
  rw [originalMerge1011, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1012 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1012 (originalVector B) := by
  rw [reducedMerge1012Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1010 B hB hF, reducedMergeEval1011 B hB hF]
  rw [originalMerge1012, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1013 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1013 (originalVector B) := by
  rw [reducedMerge1013Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1009 B hB hF, reducedMergeEval1012 B hB hF]
  rw [originalMerge1013, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1014 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1014 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1014 (originalVector B) := by
  rw [reducedMerge1014Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1006 B hB hF, reducedMergeEval1013 B hB hF]
  rw [originalMerge1014, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1015 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1015 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1015 (originalVector B) := by
  rw [reducedMerge1015Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1000 B hB hF, reducedMergeEval1014 B hB hF]
  rw [originalMerge1015, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1016 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1016 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1016 (originalVector B) := by
  rw [reducedMerge1016Check, Integer.Sparse.eval_mergeBy, reducedMergeEval986 B hB hF, reducedMergeEval1015 B hB hF]
  rw [originalMerge1016, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1079 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1079 (originalVector B) := by
  rw [reducedTermArithmetic1079, ← sound2803 B hB hF]
  change (7655273626113146880000 : ℝ) * mixedMoment B node2803 node2803Labels =
    (37623398400 : ℝ) * ((203471083200 : ℝ) * mixedMoment B node2803 node2803Labels + 0)
  ring

theorem reducedTermEval1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1080 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1080 (originalVector B) := by
  rw [reducedTermArithmetic1080, ← sound2806 B hB hF]
  change (416003421044736000000 : ℝ) * mixedMoment B node2806 node2806Labels =
    (37623398400 : ℝ) * ((11057040000 : ℝ) * mixedMoment B node2806 node2806Labels + 0)
  ring

theorem reducedTermEval1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1081 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1081 (originalVector B) := by
  rw [reducedTermArithmetic1081, ← sound2807 B hB hF]
  change (9566869889386414080000 : ℝ) * mixedMoment B node2807 node2807Labels =
    (37623398400 : ℝ) * ((254279791200 : ℝ) * mixedMoment B node2807 node2807Labels + 0)
  ring

theorem reducedTermEval1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1082 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1082 (originalVector B) := by
  rw [reducedTermArithmetic1082, ← sound2809 B hB hF]
  change (-1653558743737958400000 : ℝ) * mixedMoment B node2809 node2809Labels =
    (37623398400 : ℝ) * (((-43950276000 : ℤ) : ℝ) * mixedMoment B node2809 node2809Labels + 0)
  ring

theorem reducedTermEval1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1083 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1083 (originalVector B) := by
  rw [reducedTermArithmetic1083, ← sound2810 B hB hF]
  change (-2050187137963130880000 : ℝ) * mixedMoment B node2810 node2810Labels =
    (37623398400 : ℝ) * (((-54492343200 : ℤ) : ℝ) * mixedMoment B node2810 node2810Labels + 0)
  ring

theorem reducedTermEval1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1084 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1084 (originalVector B) := by
  rw [reducedTermArithmetic1084, ← sound2811 B hB hF]
  change (-3435263414499409920000 : ℝ) * mixedMoment B node2811 node2811Labels =
    (37623398400 : ℝ) * (((-91306568800 : ℤ) : ℝ) * mixedMoment B node2811 node2811Labels + 0)
  ring

theorem reducedTermEval1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1085 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1085 (originalVector B) := by
  rw [reducedTermArithmetic1085, ← sound2812 B hB hF]
  change (7633541508433182720000 : ℝ) * mixedMoment B node2812 node2812Labels =
    (37623398400 : ℝ) * ((202893460800 : ℝ) * mixedMoment B node2812 node2812Labels + 0)
  ring

theorem reducedTermEval1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1086 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1086 (originalVector B) := by
  rw [reducedTermArithmetic1086, ← sound2813 B hB hF]
  change (-590178927323381760000 : ℝ) * mixedMoment B node2813 node2813Labels =
    (37623398400 : ℝ) * (((-15686486400 : ℤ) : ℝ) * mixedMoment B node2813 node2813Labels + 0)
  ring

theorem reducedTermEval1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1087 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1087 (originalVector B) := by
  rw [reducedTermArithmetic1087, ← sound2814 B hB hF]
  change (-4479366205522575360000 : ℝ) * mixedMoment B node2814 node2814Labels =
    (37623398400 : ℝ) * (((-119057990400 : ℤ) : ℝ) * mixedMoment B node2814 node2814Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1088 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1088 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1088 (originalVector B) := by
  rw [reducedTermArithmetic1088, ← sound2815 B hB hF]
  change (5011857085783080960000 : ℝ) * mixedMoment B node2815 node2815Labels =
    (37623398400 : ℝ) * ((133211174400 : ℝ) * mixedMoment B node2815 node2815Labels + 0)
  ring

theorem reducedTermEval1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1089 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1089 (originalVector B) := by
  rw [reducedTermArithmetic1089, ← sound2816 B hB hF]
  change (999901708930252800000 : ℝ) * mixedMoment B node2816 node2816Labels =
    (37623398400 : ℝ) * ((26576592000 : ℝ) * mixedMoment B node2816 node2816Labels + 0)
  ring

theorem reducedTermEval1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1090 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1090 (originalVector B) := by
  rw [reducedTermArithmetic1090, ← sound2817 B hB hF]
  change (-7972461087479562240000 : ℝ) * mixedMoment B node2817 node2817Labels =
    (37623398400 : ℝ) * (((-211901673600 : ℤ) : ℝ) * mixedMoment B node2817 node2817Labels + 0)
  ring

theorem reducedTermEval1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1091 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1091 (originalVector B) := by
  rw [reducedTermArithmetic1091, ← sound2818 B hB hF]
  change (-5777870711254548480000 : ℝ) * mixedMoment B node2818 node2818Labels =
    (37623398400 : ℝ) * (((-153571207200 : ℤ) : ℝ) * mixedMoment B node2818 node2818Labels + 0)
  ring

theorem reducedTermEval1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1092 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1092 (originalVector B) := by
  rw [reducedTermArithmetic1092, ← sound2819 B hB hF]
  change (8961285504761856000000 : ℝ) * mixedMoment B node2819 node2819Labels =
    (37623398400 : ℝ) * ((238183840000 : ℝ) * mixedMoment B node2819 node2819Labels + 0)
  ring

theorem reducedTermEval1093 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1093 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1093 (originalVector B) := by
  rw [reducedTermArithmetic1093, ← sound2820 B hB hF]
  change (1274912738715893760000 : ℝ) * mixedMoment B node2820 node2820Labels =
    (37623398400 : ℝ) * ((33886166400 : ℝ) * mixedMoment B node2820 node2820Labels + 0)
  ring

theorem reducedTermEval1094 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1094 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1094 (originalVector B) := by
  rw [reducedTermArithmetic1094, ← sound2821 B hB hF]
  change (-2262212174315520000000 : ℝ) * mixedMoment B node2821 node2821Labels =
    (37623398400 : ℝ) * (((-60127800000 : ℤ) : ℝ) * mixedMoment B node2821 node2821Labels + 0)
  ring

theorem reducedTermEval1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1095 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1095 (originalVector B) := by
  rw [reducedTermArithmetic1095, ← sound2824 B hB hF]
  change (-11618393320164556800000 : ℝ) * mixedMoment B node2824 node2824Labels =
    (37623398400 : ℝ) * (((-308807652000 : ℤ) : ℝ) * mixedMoment B node2824 node2824Labels + 0)
  ring

theorem reducedTermEval1096 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1096 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1096 (originalVector B) := by
  rw [reducedTermArithmetic1096, ← sound2826 B hB hF]
  change (-10406241466564608000000 : ℝ) * mixedMoment B node2826 node2826Labels =
    (37623398400 : ℝ) * (((-276589620000 : ℤ) : ℝ) * mixedMoment B node2826 node2826Labels + 0)
  ring

theorem reducedTermEval1097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1097 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1097 (originalVector B) := by
  rw [reducedTermArithmetic1097, ← sound2827 B hB hF]
  change (6238836832370688000000 : ℝ) * mixedMoment B node2827 node2827Labels =
    (37623398400 : ℝ) * ((165823320000 : ℝ) * mixedMoment B node2827 node2827Labels + 0)
  ring

theorem reducedTermEval1098 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1098 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1098 (originalVector B) := by
  rw [reducedTermArithmetic1098, ← sound2846 B hB hF]
  change (2089015568665804800000 : ℝ) * mixedMoment B node2846 node2846Labels =
    (37623398400 : ℝ) * ((55524372000 : ℝ) * mixedMoment B node2846 node2846Labels + 0)
  ring

theorem reducedTermEval1099 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1099 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1099 (originalVector B) := by
  rw [reducedTermArithmetic1099, ← sound2847 B hB hF]
  change (5660818630174310400000 : ℝ) * mixedMoment B node2847 node2847Labels =
    (37623398400 : ℝ) * ((150460056000 : ℝ) * mixedMoment B node2847 node2847Labels + 0)
  ring

theorem reducedTermEval1100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1100 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1100 (originalVector B) := by
  rw [reducedTermArithmetic1100, ← sound2848 B hB hF]
  change (-5194848837860720640000 : ℝ) * mixedMoment B node2848 node2848Labels =
    (37623398400 : ℝ) * (((-138074949600 : ℤ) : ℝ) * mixedMoment B node2848 node2848Labels + 0)
  ring

theorem reducedTermEval1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1101 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1101 (originalVector B) := by
  rw [reducedTermArithmetic1101, ← sound2861 B hB hF]
  change (-3445367674768588800000 : ℝ) * mixedMoment B node2861 node2861Labels =
    (37623398400 : ℝ) * (((-91575132000 : ℤ) : ℝ) * mixedMoment B node2861 node2861Labels + 0)
  ring

theorem reducedTermEval1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1102 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1102 (originalVector B) := by
  rw [reducedTermArithmetic1102, ← sound2862 B hB hF]
  change (-3526248379837317120000 : ℝ) * mixedMoment B node2862 node2862Labels =
    (37623398400 : ℝ) * (((-93724876800 : ℤ) : ℝ) * mixedMoment B node2862 node2862Labels + 0)
  ring

theorem reducedTermEval1103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1103 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1103 (originalVector B) := by
  rw [reducedTermArithmetic1103, ← sound2864 B hB hF]
  change (1340821167243264000000 : ℝ) * mixedMoment B node2864 node2864Labels =
    (37623398400 : ℝ) * ((35637960000 : ℝ) * mixedMoment B node2864 node2864Labels + 0)
  ring

theorem reducedTermEval1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1104 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1104 (originalVector B) := by
  rw [reducedTermArithmetic1104, ← sound2865 B hB hF]
  change (-21284105174522265600000 : ℝ) * mixedMoment B node2865 node2865Labels =
    (37623398400 : ℝ) * (((-565714584000 : ℤ) : ℝ) * mixedMoment B node2865 node2865Labels + 0)
  ring

theorem reducedTermEval1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1105 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1105 (originalVector B) := by
  rw [reducedTermArithmetic1105, ← sound2867 B hB hF]
  change (-6729430235975516160000 : ℝ) * mixedMoment B node2867 node2867Labels =
    (37623398400 : ℝ) * (((-178862902400 : ℤ) : ℝ) * mixedMoment B node2867 node2867Labels + 0)
  ring

theorem reducedTermEval1106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1106 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1106 (originalVector B) := by
  rw [reducedTermArithmetic1106, ← sound2868 B hB hF]
  change (3526248379837317120000 : ℝ) * mixedMoment B node2868 node2868Labels =
    (37623398400 : ℝ) * ((93724876800 : ℝ) * mixedMoment B node2868 node2868Labels + 0)
  ring

theorem reducedTermEval1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1107 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1107 (originalVector B) := by
  rw [reducedTermArithmetic1107, ← sound2878 B hB hF]
  change (9976743826758696960000 : ℝ) * mixedMoment B node2878 node2878Labels =
    (37623398400 : ℝ) * ((265173914400 : ℝ) * mixedMoment B node2878 node2878Labels + 0)
  ring

theorem reducedTermEval1108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1108 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1108 (originalVector B) := by
  rw [reducedTermArithmetic1108, ← sound2879 B hB hF]
  change (-416003421044736000000 : ℝ) * mixedMoment B node2879 node2879Labels =
    (37623398400 : ℝ) * (((-11057040000 : ℤ) : ℝ) * mixedMoment B node2879 node2879Labels + 0)
  ring

theorem reducedTermEval1109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1109 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1109 (originalVector B) := by
  rw [reducedTermArithmetic1109, ← sound2880 B hB hF]
  change (-1781271279310602240000 : ℝ) * mixedMoment B node2880 node2880Labels =
    (37623398400 : ℝ) * (((-47344773600 : ℤ) : ℝ) * mixedMoment B node2880 node2880Labels + 0)
  ring

theorem reducedTermEval1110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1110 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1110 (originalVector B) := by
  rw [reducedTermArithmetic1110, ← sound2881 B hB hF]
  change (3469795674486865920000 : ℝ) * mixedMoment B node2881 node2881Labels =
    (37623398400 : ℝ) * ((92224408800 : ℝ) * mixedMoment B node2881 node2881Labels + 0)
  ring

theorem reducedTermEval1111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1111 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1111 (originalVector B) := by
  rw [reducedTermArithmetic1111, ← sound2882 B hB hF]
  change (-9976743826758696960000 : ℝ) * mixedMoment B node2882 node2882Labels =
    (37623398400 : ℝ) * (((-265173914400 : ℤ) : ℝ) * mixedMoment B node2882 node2882Labels + 0)
  ring

theorem reducedTermEval1112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1112 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1112 (originalVector B) := by
  rw [reducedTermArithmetic1112, ← sound2884 B hB hF]
  change (9212700734303109120000 : ℝ) * mixedMoment B node2884 node2884Labels =
    (37623398400 : ℝ) * ((244866256800 : ℝ) * mixedMoment B node2884 node2884Labels + 0)
  ring

theorem reducedTermEval1113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1113 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1113 (originalVector B) := by
  rw [reducedTermArithmetic1113, ← sound2885 B hB hF]
  change (-3934716707045376000000 : ℝ) * mixedMoment B node2885 node2885Labels =
    (37623398400 : ℝ) * (((-104581640000 : ℤ) : ℝ) * mixedMoment B node2885 node2885Labels + 0)
  ring

theorem reducedTermEval1114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1114 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1114 (originalVector B) := by
  rw [reducedTermArithmetic1114, ← sound2886 B hB hF]
  change (3435263414499409920000 : ℝ) * mixedMoment B node2886 node2886Labels =
    (37623398400 : ℝ) * ((91306568800 : ℝ) * mixedMoment B node2886 node2886Labels + 0)
  ring

theorem reducedTermEval1115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1115 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1115 (originalVector B) := by
  rw [reducedTermArithmetic1115, ← sound2888 B hB hF]
  change (8305600448385515520000 : ℝ) * mixedMoment B node2888 node2888Labels =
    (37623398400 : ℝ) * ((220756252800 : ℝ) * mixedMoment B node2888 node2888Labels + 0)
  ring

theorem reducedTermEval1116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1116 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1116 (originalVector B) := by
  rw [reducedTermArithmetic1116, ← sound2889 B hB hF]
  change (2724268260332666880000 : ℝ) * mixedMoment B node2889 node2889Labels =
    (37623398400 : ℝ) * ((72408883200 : ℝ) * mixedMoment B node2889 node2889Labels + 0)
  ring

theorem reducedTermEval1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1117 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1117 (originalVector B) := by
  rw [reducedTermArithmetic1117, ← sound2890 B hB hF]
  change (1355923199361024000000 : ℝ) * mixedMoment B node2890 node2890Labels =
    (37623398400 : ℝ) * ((36039360000 : ℝ) * mixedMoment B node2890 node2890Labels + 0)
  ring

theorem reducedTermEval1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1118 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1118 (originalVector B) := by
  rw [reducedTermArithmetic1118, ← sound2892 B hB hF]
  change (6564939594419404800000 : ℝ) * mixedMoment B node2892 node2892Labels =
    (37623398400 : ℝ) * ((174490872000 : ℝ) * mixedMoment B node2892 node2892Labels + 0)
  ring

theorem reducedTermEval1119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1119 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1119 (originalVector B) := by
  rw [reducedTermArithmetic1119, ← sound2893 B hB hF]
  change (-1057001205647278080000 : ℝ) * mixedMoment B node2893 node2893Labels =
    (37623398400 : ℝ) * (((-28094251200 : ℤ) : ℝ) * mixedMoment B node2893 node2893Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1076 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1076 (originalVector B) := by
  rw [reducedMerge1076Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1016 B hB hF, reducedMergeEval1075_e B hB hF]
  rw [originalMerge1076, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1077 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1077 (originalVector B) := by
  rw [reducedMerge1077Check, Integer.Sparse.eval_mergeBy, reducedTermEval1080 B hB hF, reducedTermEval1081 B hB hF]
  rw [originalMerge1077, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1078 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1078 (originalVector B) := by
  rw [reducedMerge1078Check, Integer.Sparse.eval_mergeBy, reducedTermEval1079 B hB hF, reducedMergeEval1077 B hB hF]
  rw [originalMerge1078, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1079 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1079 (originalVector B) := by
  rw [reducedMerge1079Check, Integer.Sparse.eval_mergeBy, reducedTermEval1082 B hB hF, reducedTermEval1083 B hB hF]
  rw [originalMerge1079, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1080 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1080 (originalVector B) := by
  rw [reducedMerge1080Check, Integer.Sparse.eval_mergeBy, reducedTermEval1084 B hB hF, reducedTermEval1085 B hB hF]
  rw [originalMerge1080, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1081 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1081 (originalVector B) := by
  rw [reducedMerge1081Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1079 B hB hF, reducedMergeEval1080 B hB hF]
  rw [originalMerge1081, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1082 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1082 (originalVector B) := by
  rw [reducedMerge1082Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1078 B hB hF, reducedMergeEval1081 B hB hF]
  rw [originalMerge1082, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1083 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1083 (originalVector B) := by
  rw [reducedMerge1083Check, Integer.Sparse.eval_mergeBy, reducedTermEval1086 B hB hF, reducedTermEval1087 B hB hF]
  rw [originalMerge1083, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1084 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1084 (originalVector B) := by
  rw [reducedMerge1084Check, Integer.Sparse.eval_mergeBy, reducedTermEval1088 B hB hF, reducedTermEval1089 B hB hF]
  rw [originalMerge1084, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1085 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1085 (originalVector B) := by
  rw [reducedMerge1085Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1083 B hB hF, reducedMergeEval1084 B hB hF]
  rw [originalMerge1085, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1086 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1086 (originalVector B) := by
  rw [reducedMerge1086Check, Integer.Sparse.eval_mergeBy, reducedTermEval1090 B hB hF, reducedTermEval1091 B hB hF]
  rw [originalMerge1086, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1087 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1087 (originalVector B) := by
  rw [reducedMerge1087Check, Integer.Sparse.eval_mergeBy, reducedTermEval1092 B hB hF, reducedTermEval1093 B hB hF]
  rw [originalMerge1087, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1120 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1120 (originalVector B) := by
  rw [reducedTermArithmetic1120, ← sound2895 B hB hF]
  change (-5105263763930480640000 : ℝ) * mixedMoment B node2895 node2895Labels =
    (37623398400 : ℝ) * (((-135693849600 : ℤ) : ℝ) * mixedMoment B node2895 node2895Labels + 0)
  ring

theorem reducedTermEval1121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1121 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1121 (originalVector B) := by
  rw [reducedTermArithmetic1121, ← sound2896 B hB hF]
  change (3946875325262069760000 : ℝ) * mixedMoment B node2896 node2896Labels =
    (37623398400 : ℝ) * ((104904806400 : ℝ) * mixedMoment B node2896 node2896Labels + 0)
  ring

theorem reducedTermEval1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1122 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1122 (originalVector B) := by
  rw [reducedTermArithmetic1122, ← sound2898 B hB hF]
  change (-5660818630174310400000 : ℝ) * mixedMoment B node2898 node2898Labels =
    (37623398400 : ℝ) * (((-150460056000 : ℤ) : ℝ) * mixedMoment B node2898 node2898Labels + 0)
  ring

theorem reducedTermEval1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1123 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1123 (originalVector B) := by
  rw [reducedTermArithmetic1123, ← sound2899 B hB hF]
  change (-9762840630358179840000 : ℝ) * mixedMoment B node2899 node2899Labels =
    (37623398400 : ℝ) * (((-259488537600 : ℤ) : ℝ) * mixedMoment B node2899 node2899Labels + 0)
  ring

theorem reducedTermEval1124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1124 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1124 (originalVector B) := by
  rw [reducedTermArithmetic1124, ← sound2900 B hB hF]
  change (16607243005555507200000 : ℝ) * mixedMoment B node2900 node2900Labels =
    (37623398400 : ℝ) * ((441407308000 : ℝ) * mixedMoment B node2900 node2900Labels + 0)
  ring

theorem reducedTermEval1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1125 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1125 (originalVector B) := by
  rw [reducedTermArithmetic1125, ← sound2902 B hB hF]
  change (13705060285808640000000 : ℝ) * mixedMoment B node2902 node2902Labels =
    (37623398400 : ℝ) * ((364269600000 : ℝ) * mixedMoment B node2902 node2902Labels + 0)
  ring

theorem reducedTermEval1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1126 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1126 (originalVector B) := by
  rw [reducedTermArithmetic1126, ← sound2916 B hB hF]
  change (-2757638739876249600000 : ℝ) * mixedMoment B node2916 node2916Labels =
    (37623398400 : ℝ) * (((-73295844000 : ℤ) : ℝ) * mixedMoment B node2916 node2916Labels + 0)
  ring

theorem reducedTermEval1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1127 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1127 (originalVector B) := by
  rw [reducedTermArithmetic1127, ← sound2923 B hB hF]
  change (-359649951169904640000 : ℝ) * mixedMoment B node2923 node2923Labels =
    (37623398400 : ℝ) * (((-9559209600 : ℤ) : ℝ) * mixedMoment B node2923 node2923Labels + 0)
  ring

theorem reducedTermEval1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1128 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1128 (originalVector B) := by
  rw [reducedTermArithmetic1128, ← sound2924 B hB hF]
  change (19302033754623836160000 : ℝ) * mixedMoment B node2924 node2924Labels =
    (37623398400 : ℝ) * ((513032702400 : ℝ) * mixedMoment B node2924 node2924Labels + 0)
  ring

theorem reducedTermEval1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1129 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1129 (originalVector B) := by
  rw [reducedTermArithmetic1129, ← sound2925 B hB hF]
  change (6891745041155358720000 : ℝ) * mixedMoment B node2925 node2925Labels =
    (37623398400 : ℝ) * ((183177100800 : ℝ) * mixedMoment B node2925 node2925Labels + 0)
  ring

theorem reducedTermEval1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1130 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1130 (originalVector B) := by
  rw [reducedTermArithmetic1130, ← sound2928 B hB hF]
  change (20635690283060428800000 : ℝ) * mixedMoment B node2928 node2928Labels =
    (37623398400 : ℝ) * ((548480232000 : ℝ) * mixedMoment B node2928 node2928Labels + 0)
  ring

theorem reducedTermEval1131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1131 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1131 (originalVector B) := by
  rw [reducedTermArithmetic1131, ← sound2930 B hB hF]
  change (6436794359666442240000 : ℝ) * mixedMoment B node2930 node2930Labels =
    (37623398400 : ℝ) * ((171084873600 : ℝ) * mixedMoment B node2930 node2930Labels + 0)
  ring

theorem reducedTermEval1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1132 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1132 (originalVector B) := by
  rw [reducedTermArithmetic1132, ← sound2931 B hB hF]
  change (829623023566848000000 : ℝ) * mixedMoment B node2931 node2931Labels =
    (37623398400 : ℝ) * ((22050720000 : ℝ) * mixedMoment B node2931 node2931Labels + 0)
  ring

theorem reducedTermEval1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1133 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1133 (originalVector B) := by
  rw [reducedTermArithmetic1133, ← sound2933 B hB hF]
  change (-16476867997522329600000 : ℝ) * mixedMoment B node2933 node2933Labels =
    (37623398400 : ℝ) * (((-437942044000 : ℤ) : ℝ) * mixedMoment B node2933 node2933Labels + 0)
  ring

theorem reducedTermEval1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1134 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1134 (originalVector B) := by
  rw [reducedTermArithmetic1134, ← sound2942 B hB hF]
  change (-8398043666546688000000 : ℝ) * mixedMoment B node2942 node2942Labels =
    (37623398400 : ℝ) * (((-223213320000 : ℤ) : ℝ) * mixedMoment B node2942 node2942Labels + 0)
  ring

theorem reducedTermEval1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1135 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1135 (originalVector B) := by
  rw [reducedTermArithmetic1135, ← sound2951 B hB hF]
  change (33959038618062028800000 : ℝ) * mixedMoment B node2951 node2951Labels =
    (37623398400 : ℝ) * ((902604232000 : ℝ) * mixedMoment B node2951 node2951Labels + 0)
  ring

theorem reducedTermEval1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1136 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1136 (originalVector B) := by
  rw [reducedTermArithmetic1136, ← sound2952 B hB hF]
  change (-571357054756454400000 : ℝ) * mixedMoment B node2952 node2952Labels =
    (37623398400 : ℝ) * (((-15186216000 : ℤ) : ℝ) * mixedMoment B node2952 node2952Labels + 0)
  ring

theorem reducedTermEval1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1137 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1137 (originalVector B) := by
  rw [reducedTermArithmetic1137, ← sound2954 B hB hF]
  change (-8958732411045150720000 : ℝ) * mixedMoment B node2954 node2954Labels =
    (37623398400 : ℝ) * (((-238115980800 : ℤ) : ℝ) * mixedMoment B node2954 node2954Labels + 0)
  ring

theorem reducedTermEval1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1138 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1138 (originalVector B) := by
  rw [reducedTermArithmetic1138, ← sound2955 B hB hF]
  change (-39828535728449126400000 : ℝ) * mixedMoment B node2955 node2955Labels =
    (37623398400 : ℝ) * (((-1058610796000 : ℤ) : ℝ) * mixedMoment B node2955 node2955Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1088 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1088 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1088 (originalVector B) := by
  rw [reducedMerge1088Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1086 B hB hF, reducedMergeEval1087 B hB hF]
  rw [originalMerge1088, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1089 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1089 (originalVector B) := by
  rw [reducedMerge1089Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1085 B hB hF, reducedMergeEval1088 B hB hF]
  rw [originalMerge1089, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1090 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1090 (originalVector B) := by
  rw [reducedMerge1090Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1082 B hB hF, reducedMergeEval1089 B hB hF]
  rw [originalMerge1090, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1091 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1091 (originalVector B) := by
  rw [reducedMerge1091Check, Integer.Sparse.eval_mergeBy, reducedTermEval1095 B hB hF, reducedTermEval1096 B hB hF]
  rw [originalMerge1091, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1092 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1092 (originalVector B) := by
  rw [reducedMerge1092Check, Integer.Sparse.eval_mergeBy, reducedTermEval1094 B hB hF, reducedMergeEval1091 B hB hF]
  rw [originalMerge1092, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1093 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1093 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1093 (originalVector B) := by
  rw [reducedMerge1093Check, Integer.Sparse.eval_mergeBy, reducedTermEval1097 B hB hF, reducedTermEval1098 B hB hF]
  rw [originalMerge1093, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1094 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1094 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1094 (originalVector B) := by
  rw [reducedMerge1094Check, Integer.Sparse.eval_mergeBy, reducedTermEval1099 B hB hF, reducedTermEval1100 B hB hF]
  rw [originalMerge1094, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1095 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1095 (originalVector B) := by
  rw [reducedMerge1095Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1093 B hB hF, reducedMergeEval1094 B hB hF]
  rw [originalMerge1095, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1096 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1096 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1096 (originalVector B) := by
  rw [reducedMerge1096Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1092 B hB hF, reducedMergeEval1095 B hB hF]
  rw [originalMerge1096, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1097 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1097 (originalVector B) := by
  rw [reducedMerge1097Check, Integer.Sparse.eval_mergeBy, reducedTermEval1101 B hB hF, reducedTermEval1102 B hB hF]
  rw [originalMerge1097, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1098 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1098 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1098 (originalVector B) := by
  rw [reducedMerge1098Check, Integer.Sparse.eval_mergeBy, reducedTermEval1103 B hB hF, reducedTermEval1104 B hB hF]
  rw [originalMerge1098, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1099 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1099 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1099 (originalVector B) := by
  rw [reducedMerge1099Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1097 B hB hF, reducedMergeEval1098 B hB hF]
  rw [originalMerge1099, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1100 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1100 (originalVector B) := by
  rw [reducedMerge1100Check, Integer.Sparse.eval_mergeBy, reducedTermEval1105 B hB hF, reducedTermEval1106 B hB hF]
  rw [originalMerge1100, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1101 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1101 (originalVector B) := by
  rw [reducedMerge1101Check, Integer.Sparse.eval_mergeBy, reducedTermEval1107 B hB hF, reducedTermEval1108 B hB hF]
  rw [originalMerge1101, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1102 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1102 (originalVector B) := by
  rw [reducedMerge1102Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1100 B hB hF, reducedMergeEval1101 B hB hF]
  rw [originalMerge1102, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1103 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1103 (originalVector B) := by
  rw [reducedMerge1103Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1099 B hB hF, reducedMergeEval1102 B hB hF]
  rw [originalMerge1103, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1104 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1104 (originalVector B) := by
  rw [reducedMerge1104Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1096 B hB hF, reducedMergeEval1103 B hB hF]
  rw [originalMerge1104, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1105 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1105 (originalVector B) := by
  rw [reducedMerge1105Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1090 B hB hF, reducedMergeEval1104 B hB hF]
  rw [originalMerge1105, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1106 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1106 (originalVector B) := by
  rw [reducedMerge1106Check, Integer.Sparse.eval_mergeBy, reducedTermEval1110 B hB hF, reducedTermEval1111 B hB hF]
  rw [originalMerge1106, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1107 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1107 (originalVector B) := by
  rw [reducedMerge1107Check, Integer.Sparse.eval_mergeBy, reducedTermEval1109 B hB hF, reducedMergeEval1106 B hB hF]
  rw [originalMerge1107, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1108 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1108 (originalVector B) := by
  rw [reducedMerge1108Check, Integer.Sparse.eval_mergeBy, reducedTermEval1112 B hB hF, reducedTermEval1113 B hB hF]
  rw [originalMerge1108, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1109 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1109 (originalVector B) := by
  rw [reducedMerge1109Check, Integer.Sparse.eval_mergeBy, reducedTermEval1114 B hB hF, reducedTermEval1115 B hB hF]
  rw [originalMerge1109, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1110 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1110 (originalVector B) := by
  rw [reducedMerge1110Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1108 B hB hF, reducedMergeEval1109 B hB hF]
  rw [originalMerge1110, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1111 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1111 (originalVector B) := by
  rw [reducedMerge1111Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1107 B hB hF, reducedMergeEval1110 B hB hF]
  rw [originalMerge1111, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1112 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1112 (originalVector B) := by
  rw [reducedMerge1112Check, Integer.Sparse.eval_mergeBy, reducedTermEval1116 B hB hF, reducedTermEval1117 B hB hF]
  rw [originalMerge1112, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1113 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1113 (originalVector B) := by
  rw [reducedMerge1113Check, Integer.Sparse.eval_mergeBy, reducedTermEval1118 B hB hF, reducedTermEval1119 B hB hF]
  rw [originalMerge1113, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1114 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1114 (originalVector B) := by
  rw [reducedMerge1114Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1112 B hB hF, reducedMergeEval1113 B hB hF]
  rw [originalMerge1114, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1115 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1115 (originalVector B) := by
  rw [reducedMerge1115Check, Integer.Sparse.eval_mergeBy, reducedTermEval1120 B hB hF, reducedTermEval1121 B hB hF]
  rw [originalMerge1115, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1116 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1116 (originalVector B) := by
  rw [reducedMerge1116Check, Integer.Sparse.eval_mergeBy, reducedTermEval1122 B hB hF, reducedTermEval1123 B hB hF]
  rw [originalMerge1116, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1117 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1117 (originalVector B) := by
  rw [reducedMerge1117Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1115 B hB hF, reducedMergeEval1116 B hB hF]
  rw [originalMerge1117, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1118 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1118 (originalVector B) := by
  rw [reducedMerge1118Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1114 B hB hF, reducedMergeEval1117 B hB hF]
  rw [originalMerge1118, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1119 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1119 (originalVector B) := by
  rw [reducedMerge1119Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1111 B hB hF, reducedMergeEval1118 B hB hF]
  rw [originalMerge1119, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1120 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1120 (originalVector B) := by
  rw [reducedMerge1120Check, Integer.Sparse.eval_mergeBy, reducedTermEval1125 B hB hF, reducedTermEval1126 B hB hF]
  rw [originalMerge1120, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1121 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1121 (originalVector B) := by
  rw [reducedMerge1121Check, Integer.Sparse.eval_mergeBy, reducedTermEval1124 B hB hF, reducedMergeEval1120 B hB hF]
  rw [originalMerge1121, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1122 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1122 (originalVector B) := by
  rw [reducedMerge1122Check, Integer.Sparse.eval_mergeBy, reducedTermEval1127 B hB hF, reducedTermEval1128 B hB hF]
  rw [originalMerge1122, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1123 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1123 (originalVector B) := by
  rw [reducedMerge1123Check, Integer.Sparse.eval_mergeBy, reducedTermEval1129 B hB hF, reducedTermEval1130 B hB hF]
  rw [originalMerge1123, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1124 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1124 (originalVector B) := by
  rw [reducedMerge1124Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1122 B hB hF, reducedMergeEval1123 B hB hF]
  rw [originalMerge1124, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1125 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1125 (originalVector B) := by
  rw [reducedMerge1125Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1121 B hB hF, reducedMergeEval1124 B hB hF]
  rw [originalMerge1125, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1126 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1126 (originalVector B) := by
  rw [reducedMerge1126Check, Integer.Sparse.eval_mergeBy, reducedTermEval1131 B hB hF, reducedTermEval1132 B hB hF]
  rw [originalMerge1126, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1127 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1127 (originalVector B) := by
  rw [reducedMerge1127Check, Integer.Sparse.eval_mergeBy, reducedTermEval1133 B hB hF, reducedTermEval1134 B hB hF]
  rw [originalMerge1127, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1128 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1128 (originalVector B) := by
  rw [reducedMerge1128Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1126 B hB hF, reducedMergeEval1127 B hB hF]
  rw [originalMerge1128, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1129 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1129 (originalVector B) := by
  rw [reducedMerge1129Check, Integer.Sparse.eval_mergeBy, reducedTermEval1135 B hB hF, reducedTermEval1136 B hB hF]
  rw [originalMerge1129, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1130 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1130 (originalVector B) := by
  rw [reducedMerge1130Check, Integer.Sparse.eval_mergeBy, reducedTermEval1137 B hB hF, reducedTermEval1138 B hB hF]
  rw [originalMerge1130, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1131 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1131 (originalVector B) := by
  rw [reducedMerge1131Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1129 B hB hF, reducedMergeEval1130 B hB hF]
  rw [originalMerge1131, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1132 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1132 (originalVector B) := by
  rw [reducedMerge1132Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1128 B hB hF, reducedMergeEval1131 B hB hF]
  rw [originalMerge1132, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1133 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1133 (originalVector B) := by
  rw [reducedMerge1133Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1125 B hB hF, reducedMergeEval1132 B hB hF]
  rw [originalMerge1133, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1134 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1134 (originalVector B) := by
  rw [reducedMerge1134Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1119 B hB hF, reducedMergeEval1133 B hB hF]
  rw [originalMerge1134, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1135 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1135 (originalVector B) := by
  rw [reducedMerge1135Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1105 B hB hF, reducedMergeEval1134 B hB hF]
  rw [originalMerge1135, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1195 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1195 (originalVector B) := by
  rw [reducedMerge1195Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1135 B hB hF, reducedMergeEval1194_e B hB hF]
  rw [originalMerge1195, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1196_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1196 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1196 (originalVector B) := by
  rw [reducedMerge1196Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1076 B hB hF, reducedMergeEval1195 B hB hF]
  rw [originalMerge1196, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e_oai
