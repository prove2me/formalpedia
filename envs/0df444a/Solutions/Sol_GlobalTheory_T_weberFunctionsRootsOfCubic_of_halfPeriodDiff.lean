-- Prove2me | solution 1 for GlobalTheory.T.weberFunctionsRootsOfCubic_of_halfPeriodDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:45:33.830541+00:00
-- url     : https://prove2.me/submissions/29646921-7a9a-4c3c-9dd1-ace88c1167b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionsRootsOfCubicOfHalfPeriodDiff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionsRootsOfCubicOfHalfPeriodDiffStatement
import Theorems.Thm_GlobalTheory_WeberCubicAlgebra_weberCubic_of_halfPeriodDiff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.WeberCubic τ := by
  first | exact @GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff | exact GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff | (intros; apply GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff <;> assumption)
end _root_.GlobalTheory.T
