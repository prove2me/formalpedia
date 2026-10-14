-- Prove2me | solution 1 for NegativeDP.OptEq.theorem52c
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:34:47.449989+00:00
-- url     : https://prove2.me/submissions/475f769a-8550-4229-b847-18f3a9cd4afb

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)


namespace NegativeDP.OptEq

theorem theorem52a_core {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u v : S → EReal)
    (huv : ∀ s, u s ≤ v s) :
    ∀ s, U P π u s ≤ U P π v s := by
  intro s
  unfold U
  refine iSup_mono fun n => ?_
  unfold NegativeDP.Stationary.T
  rw [EReal.neg_le_neg_iff]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (lintegral_mono fun t =>
    add_le_add le_rfl (EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (huv t))))


theorem theorem52c_core {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : ℕ → S → EReal) :
    ∀ s, ⨆ j, U P π (u j) s ≤ U P π (fun t => ⨆ j, u j t) s := by
  intro s
  exact iSup_le fun j => theorem52a_core P π (u j) _ (fun t => le_iSup (fun j => u j t) j) s

end NegativeDP.OptEq

open NegativeDP.OptEq


variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem solution (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : ℕ → S → EReal)
    (hu : ∀ j, NegativeDP.Stationary.IsNegM (u j)) :
    ∀ s, ⨆ j, U P π (u j) s ≤ U P π (fun t => ⨆ j, u j t) s := by
  exact theorem52c_core P π u
