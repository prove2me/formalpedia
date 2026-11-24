-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:46:32.535315+00:00
-- url     : https://prove2.me/submissions/5ea0c796-bb30-4c8a-90e7-121d88637020

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_sum_translates

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
theorem _root_.solution (hf : AvgFinite K f) {V : Submodule ℂ (G → W)}
    (hV : ∀ k ∈ K, (fun y => f (y * k)) ∈ V) : avgOver K f ∈ V := by
  classical
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  rw [avgOver_eq_sum_translates]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => hV _ (Quotient.out q).2)
end GroundTheory.Automorphic.Parabolic
