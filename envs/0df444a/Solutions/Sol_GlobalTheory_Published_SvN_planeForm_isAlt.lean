-- Prove2me | solution 1 for GlobalTheory.Published.SvN.planeForm_isAlt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:40:01.608663+00:00
-- url     : https://prove2.me/submissions/6666de63-23fe-4d99-8d74-ba0cf46c2071

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
namespace GlobalTheory.Published.SvN
theorem _root_.solution (F : Type) [Field F] : (planeForm F).IsAlt := fun x => by simp [planeForm, mul_comm]
end GlobalTheory.Published.SvN
