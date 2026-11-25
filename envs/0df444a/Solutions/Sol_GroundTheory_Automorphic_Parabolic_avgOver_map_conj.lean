-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:06:31.908514+00:00
-- url     : https://prove2.me/submissions/e58331c7-a59c-4abb-8627-829669263ff5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_map_mulEquiv

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
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (b : G) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) (x : G) :
    avgOver (K.map (MulAut.conj b).toMonoidHom) (fun y => f (b⁻¹ * y * b)) x =
      avgOver K f (b⁻¹ * x * b) := by
  have := avgOver_map_mulEquiv (MulAut.conj b) hf x
  simp only [MulAut.conj_symm_apply] at this
  exact this
end GroundTheory.Automorphic.Parabolic
