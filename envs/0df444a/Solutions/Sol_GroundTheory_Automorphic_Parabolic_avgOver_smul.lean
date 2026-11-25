-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:22.481656+00:00
-- url     : https://prove2.me/submissions/b4af7610-9561-4ac3-8e43-cd4b8b098df1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_linearMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {K : Subgroup G} {f : G → W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (c : ℂ) (hf : AvgFinite K f) : avgOver K (c • f) = c • avgOver K f := by
  funext x
  have := avgOver_comp_linearMap hf (c • LinearMap.id) x
  show avgOver K (fun y => c • f y) x = c • avgOver K f x
  simpa using this
end GroundTheory.Automorphic.Parabolic
