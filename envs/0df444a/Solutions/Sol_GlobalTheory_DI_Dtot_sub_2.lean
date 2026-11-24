-- Prove2me | solution 2 for GlobalTheory.DI.Dtot_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:09.068802+00:00
-- url     : https://prove2.me/submissions/5515cdb2-404f-4a04-8aa8-df04bc030b5e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero
import Theorems.Thm_GlobalTheory_DI_delta_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
namespace GlobalTheory.DI
theorem _root_.solution (d : E →+ E) (c c' : Finset ι → E) : Dtot d (c - c') = Dtot d c - Dtot d c' := by
  funext t
  simp only [Dtot, delta_sub, Pi.sub_apply, map_sub, smul_sub]
  abel
end GlobalTheory.DI
