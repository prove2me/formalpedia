-- Prove2me | solution 1 for GlobalTheory.span_range_single_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:20.414941+00:00
-- url     : https://prove2.me/submissions/da9408a0-9d36-43b8-9296-4540601e38b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt

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
theorem _root_.solution :
    Submodule.span ℂ (Set.range fun i : σ => (Pi.single i 1 : σ → ℂ)) = ⊤ := by
  have h := (Pi.basisFun ℂ σ).span_eq
  rwa [show ⇑(Pi.basisFun ℂ σ) = fun i : σ => (Pi.single i 1 : σ → ℂ) from
    funext fun i => Pi.basisFun_apply ℂ σ i] at h
end GlobalTheory
