-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_comp_linearMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:47.645006+00:00
-- url     : https://prove2.me/submissions/835acb2c-27ee-456e-9128-ff7e324a6135

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_eq_sum
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_avgSub

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
theorem _root_.solution (hf : AvgFinite K f) {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (T : W →ₗ[ℂ] W') (x : G) :
    avgOver K (fun y => T (f y)) x = T (avgOver K f x) := by
  classical
  have hle : (rightStab f).subgroupOf K ≤ (rightStab fun y => T (f y)).subgroupOf K :=
    fun k hk y => by
      show T (f (y * (k : G))) = T (f y)
      exact congrArg T (hk y)
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  rw [avgOver_eq_avgSub hle hf, avgOver, avgSub_eq_sum, avgSub_eq_sum, map_smul, map_sum]
end GroundTheory.Automorphic.Parabolic
