-- Prove2me | solution 1 for GlobalTheory.taylorDir_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:20.916987+00:00
-- url     : https://prove2.me/submissions/49938aa8-63d0-461f-8cc5-5158cb2e0245

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_taylorDir_eq_zero_iff
import Theorems.Thm_GlobalTheory_taylorDir_sub

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
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (u : σ → W) {f g : W → ℂ}
namespace GlobalTheory
theorem _root_.solution (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorDir u f = taylorDir u g ↔ f =ᶠ[𝓝 0] g := by
  rw [← sub_eq_zero, ← taylorDir_sub u hf hg, taylorDir_eq_zero_iff u hu (hf.sub hg),
    ← Filter.eventuallyEq_iff_sub]
end GlobalTheory
