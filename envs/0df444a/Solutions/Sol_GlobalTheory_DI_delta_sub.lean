-- Prove2me | solution 1 for GlobalTheory.DI.delta_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:40.578381+00:00
-- url     : https://prove2.me/submissions/ca7091c5-dc99-4c14-b36c-6d1d2934a78f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero

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
theorem _root_.solution (c c' : Finset ι → E) : delta (c - c') = delta c - delta c' := by
  funext t
  simp only [delta, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
end GlobalTheory.DI
