-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.le_rightStab_avgOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:25.086802+00:00
-- url     : https://prove2.me/submissions/3b174b93-50ce-4847-961b-5cbd0c9aecba

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_mul_right

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
variable {K : Subgroup G} {f : G → W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hf : AvgFinite K f) : K ≤ rightStab (avgOver K f) :=
  fun _ hk x => avgOver_mul_right hf hk x
end GroundTheory.Automorphic.Parabolic
