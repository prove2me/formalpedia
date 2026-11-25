-- Prove2me | solution 1 for GlobalTheory.taylorDir_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:35.230797+00:00
-- url     : https://prove2.me/submissions/33353d1c-ba8c-4eb2-8827-4955c38fdcec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_taylorDir_neg

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
theorem _root_.solution (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorDir u (f - g) = taylorDir u f - taylorDir u g := by
  rw [sub_eq_add_neg, taylorDir_add u hf hg.neg, taylorDir_neg u hg, sub_eq_add_neg]
end GlobalTheory
