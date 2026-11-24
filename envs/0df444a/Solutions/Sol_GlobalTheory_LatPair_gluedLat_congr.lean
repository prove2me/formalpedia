-- Prove2me | solution 1 for GlobalTheory.LatPair.gluedLat_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:49.37746+00:00
-- url     : https://prove2.me/submissions/87118d85-46a7-4312-84e3-dcb99d4167cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {c : ℕ}
namespace GlobalTheory.LatPair
theorem _root_.solution (q : Unif k) (c p : ℕ) {L : Submodule 𝒪[k] (n → k)} {f f' : n → k} (h : f - f' ∈ L) :
    gluedLat q c p L f = gluedLat q c p L f' := by
  ext y
  simp only [mem_gluedLat]
  refine exists_congr fun s => and_congr_left' ?_
  rw [← L.add_mem_iff_left (L.smul_mem s h), smul_sub, sub_add_sub_cancel]
end GlobalTheory.LatPair
