-- Prove2me | solution 1 for GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:50.746782+00:00
-- url     : https://prove2.me/submissions/072121d4-d412-4d3e-94df-d21f4224548c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgDvrOfSeparableCharpoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgDvrOfSeparableCharpolyStatement
import Theorems.Thm_GlobalTheory_IntClosureSep_integralClosure_fg_of_separable_charpoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  first | exact @GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly | exact GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly | (intros; apply GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly <;> assumption)
end _root_.GlobalTheory.T
