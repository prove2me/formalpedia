-- Prove2me | solution 1 for NegativeDP.OptEq.theorem52e
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:57:38.014998+00:00
-- url     : https://prove2.me/submissions/50dabbe5-d00e-410f-9da8-2c4dd578b724

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

open NegativeDP.OptEq in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : S → EReal) (hu : NegativeDP.Stationary.IsNegM u) :
    ∀ s, U P π u s ≤ 0 := by
  intro s
  unfold U
  refine iSup_le fun n => ?_
  unfold NegativeDP.Stationary.T
  exact EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _)
