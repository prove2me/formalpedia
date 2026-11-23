-- Prove2me | solution 1 for GlobalTheory.Capelli.polar_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:13.804502+00:00
-- url     : https://prove2.me/submissions/2d870417-f16a-4ddc-9e0f-5f60fa08dbb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
namespace GlobalTheory.Capelli
theorem _root_.solution (u v : σ) (P : MvPolynomial σ K) :
    polar K u v P = X u * pderiv v P := rfl
end GlobalTheory.Capelli
