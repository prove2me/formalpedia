-- Prove2me | solution 1 for GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:25.769674+00:00
-- url     : https://prove2.me/submissions/81240408-89a0-4ae0-a46f-b4ba40878e96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticeLeIntegralUnitsSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticeLeIntegralUnitsSubgroupStatement
import Theorems.Thm_GlobalTheory_UnitLemma_stabilizer_le_intUnits


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
theorem _root_.solution : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A) (L : stLat O E g), MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  first | exact @GlobalTheory.UnitLemma.stabilizer_le_intUnits | exact GlobalTheory.UnitLemma.stabilizer_le_intUnits | (intros; apply GlobalTheory.UnitLemma.stabilizer_le_intUnits <;> assumption)
end _root_.GlobalTheory.T
