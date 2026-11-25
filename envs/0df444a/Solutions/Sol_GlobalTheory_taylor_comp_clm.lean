-- Prove2me | solution 1 for GlobalTheory.taylor_comp_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:40.804717+00:00
-- url     : https://prove2.me/submissions/f7d0b01b-5ae3-4087-b9af-bdc26190e3f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_taylorDir_comp_clm

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
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory
theorem _root_.solution (L : (σ → ℂ) →L[ℂ] W) {F : W → ℂ} (hF : AnalyticAt ℂ F 0) :
    taylor (fun z => F (L z)) = taylorDir (fun i => L (Pi.single i 1)) F :=
  taylorDir_comp_clm L _ hF
end GlobalTheory
