-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.cls_mul_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:40.417686+00:00
-- url     : https://prove2.me/submissions/20259f98-29eb-47c9-80c1-28ff5dda7b02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Mem.RayData
theorem _root_.solution (hM : 2 ≤ M) {I J : Ideal (𝓞 K)} (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)}))
    (hJ : IsCoprime J (Ideal.span {(M : 𝓞 K)})) : D.cls (I * J) = D.cls I * D.cls J := D.cls_mul I J hI hJ (RayCl.ne_bot_of_cop hM hI) (RayCl.ne_bot_of_cop hM hJ)
end GlobalTheory.Mem.RayData
