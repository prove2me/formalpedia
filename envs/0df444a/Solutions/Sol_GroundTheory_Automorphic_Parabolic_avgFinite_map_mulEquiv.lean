-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgFinite_map_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:29.196327+00:00
-- url     : https://prove2.me/submissions/114dac57-4650-4dee-8d74-da87dec631de

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_rightStab


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
omit [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (φ : G ≃* G) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) :
    AvgFinite (K.map φ.toMonoidHom) (fun y => f (φ.symm y)) := by
  have hst : rightStab (fun y => f (φ.symm y)) = (rightStab f).map φ.toMonoidHom := by
    ext g
    rw [Subgroup.mem_map_equiv, mem_rightStab, mem_rightStab]
    constructor
    · intro H y
      have := H (φ y)
      rwa [map_mul, MulEquiv.symm_apply_apply] at this
    · intro H y
      rw [map_mul]
      exact H _
  show (rightStab fun y => f (φ.symm y)).relIndex (K.map φ.toMonoidHom) ≠ 0
  rw [hst, Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
  exact hf
end GroundTheory.Automorphic.Parabolic
