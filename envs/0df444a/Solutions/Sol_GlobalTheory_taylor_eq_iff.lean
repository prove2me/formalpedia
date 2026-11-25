-- Prove2me | solution 1 for GlobalTheory.taylor_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:39.047996+00:00
-- url     : https://prove2.me/submissions/c9fa191c-b82a-40bc-8970-13a652ba72c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_taylorDir_eq_iff
import Theorems.Thm_GlobalTheory_span_range_single_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {f g : (σ → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor f = taylor g ↔ f =ᶠ[𝓝 0] g :=
  taylorDir_eq_iff _ span_range_single_one hf hg
end GlobalTheory
