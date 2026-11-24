-- Prove2me | solution 1 for GlobalTheory.Published.SvN.planeForm_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:40:02.388823+00:00
-- url     : https://prove2.me/submissions/0a3e8263-8bba-404f-ba25-6b5abc512e02

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
theorem _root_.solution (F : Type) [Field F] : (planeForm F).Nondegenerate := by
  constructor <;> intro x hx <;> have h1 := hx (1, 0) <;> have h2 := hx (0, 1) <;> simp [planeForm] at h1 h2 <;>
    exact Prod.ext (by assumption) (by assumption)
end GlobalTheory.Published.SvN
