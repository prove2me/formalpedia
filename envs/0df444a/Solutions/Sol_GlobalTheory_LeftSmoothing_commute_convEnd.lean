-- Prove2me | solution 1 for GlobalTheory.LeftSmoothing.commute_convEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:40.502362+00:00
-- url     : https://prove2.me/submissions/bed453b9-7719-4f9e-8f9c-16206ef4308a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommute
import Theorems.Thm_GlobalTheory_LeftSmoothing_rightDeriv_conv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.LeftSmoothing
open scoped Manifold Topology
open Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
variable (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ)
variable {h X κ}
namespace GlobalTheory.LeftSmoothing
theorem _root_.solution (hκ : Continuous κ) (hκs : HasCompactSupport κ) (Z : 𝔤) :
    h.rightDerivEnd (F := ℂ) Z * convEnd h X hκ hκs = convEnd h X hκ hκs * h.rightDerivEnd Z := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun y => ?_)
  exact rightDeriv_conv hκ hκs f.2 Z y
end GlobalTheory.LeftSmoothing
