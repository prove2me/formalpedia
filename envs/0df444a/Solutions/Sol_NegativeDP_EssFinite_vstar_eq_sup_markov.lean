-- Prove2me | solution 1 for NegativeDP.EssFinite.vstar_eq_sup_markov
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:58:35.362376+00:00
-- url     : https://prove2.me/submissions/9c284131-5474-4c42-9473-9651a98ebcdc

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Model
import Theorems.Thm_NegativeDP_OptEq_theorem81

open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary IsGenerated IsGeneratedPlan)

namespace NDP3Aux

/-- If `x ≤ 0` and `x - ε ≤ M` for every real `ε > 0`, then `x ≤ M` in `EReal`. -/
theorem ereal_le_of_forall_sub_le {x M : EReal} (hx : x ≤ 0)
    (h : ∀ ε : ℝ, 0 < ε → x - (ε : EReal) ≤ M) : x ≤ M := by
  induction x using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hx (by simp)
  | coe a =>
    induction M using EReal.rec with
    | bot =>
      exfalso
      have := h 1 one_pos
      rw [← EReal.coe_sub] at this
      exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
    | top => exact le_top
    | coe m =>
      rw [EReal.coe_le_coe_iff]
      by_contra hlt
      push Not at hlt
      have := h ((a - m) / 2) (by linarith)
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at this
      linarith

end NDP3Aux

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem solution (P : NegativeDP.Stationary.Problem S A) (s : S) :
    NegativeDP.Stationary.vstar P s = ⨆ m : MarkovPlan S A, NegativeDP.Stationary.I P m.toPlan s := by
  apply le_antisymm
  · have hx : NegativeDP.Stationary.vstar P s ≤ 0 := by
      refine iSup_le fun σ => ?_
      unfold NegativeDP.Stationary.I
      rw [EReal.neg_le, neg_zero]
      exact EReal.coe_ennreal_nonneg _
    refine NDP3Aux.ereal_le_of_forall_sub_le hx fun ε hε => ?_
    obtain ⟨m, -, hm⟩ := NegativeDP.OptEq.theorem81 P (Measure.dirac s) inferInstance ε hε
    rw [ae_dirac_eq] at hm
    exact (Filter.eventually_pure.mp hm).trans
      (le_iSup (fun m : MarkovPlan S A => NegativeDP.Stationary.I P m.toPlan s) m)
  · exact iSup_le fun m => le_iSup (fun σ => NegativeDP.Stationary.I P σ s) m.toPlan
