-- Prove2me | solution 1 for GlobalTheory.thetaHolo_of_domainOpen_of_mTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:44:50.454279+00:00
-- url     : https://prove2.me/submissions/f2a72f70-c9df-4bfd-b057-2578df6b1f84

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal
import Theorems.Thm_GlobalTheory_differentiableOn_theta_prod_of_normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (hopen : DomainOpenStatement)
    (hM : ThetaMTestStatement) : ThetaHoloStatement := by
  intro ι _ a b
  refine differentiableOn_theta_prod_of_normal a b ((hopen ι).preimage continuous_snd) ?_
  intro K hKU hK
  obtain ⟨u, hu, hbd⟩ := hM ι a K hK (fun p hp => hKU hp)
  exact ⟨u, hu, fun l p hp => hbd b p hp l⟩
end GlobalTheory
