-- Prove2me | solution 1 for GlobalTheory.T.integralClosure_fg_finiteEtale_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:24:29.476205+00:00
-- url     : https://prove2.me/submissions/3faa3b16-2800-4d43-ad3f-18461f9708d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgFiniteEtaleDvr
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgFiniteEtaleDvrStatement
import Theorems.Thm_GlobalTheory_IntegralClosureFG_integralClosure_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A], (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  first | exact @GlobalTheory.IntegralClosureFG.integralClosure_fg | exact GlobalTheory.IntegralClosureFG.integralClosure_fg | (intros; apply GlobalTheory.IntegralClosureFG.integralClosure_fg <;> assumption)
end _root_.GlobalTheory.T
