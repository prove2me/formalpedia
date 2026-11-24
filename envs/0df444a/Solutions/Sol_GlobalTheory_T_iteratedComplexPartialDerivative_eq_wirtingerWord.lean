-- Prove2me | solution 1 for GlobalTheory.T.iteratedComplexPartialDerivative_eq_wirtingerWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:16.800802+00:00
-- url     : https://prove2.me/submissions/fe6c874a-e944-431f-b5c0-b130f466fbfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWordStatement
import Theorems.Thm_GlobalTheory_HoloWirt_iterD_eq_wirtWord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U, iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by
  first | exact @GlobalTheory.HoloWirt.iterD_eq_wirtWord | exact GlobalTheory.HoloWirt.iterD_eq_wirtWord | (intros; apply GlobalTheory.HoloWirt.iterD_eq_wirtWord <;> assumption)
end _root_.GlobalTheory.T
