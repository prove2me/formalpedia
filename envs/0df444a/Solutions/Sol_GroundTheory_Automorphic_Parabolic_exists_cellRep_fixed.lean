-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_cellRep_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:55.704864+00:00
-- url     : https://prove2.me/submissions/db317404-e460-4930-a512-7f14dbebe226

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRep_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_leviProj_mem_congruenceSubgroup__c7c7a3a01a19
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_congruence_fixed
import Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_sqrtModular_of_mem_integralGL__ab04268b5096
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_le


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hσ : IsSmooth σ) (v : W) :
    ∃ j : ℕ, ∀ x : blockUpper F n (β ∘ w),
      permGL F w * x * (permGL F w)⁻¹ ∈ congruenceSubgroup F n j → cellRep β w σ x v = v := by
  obtain ⟨j, hj⟩ := exists_congruence_fixed hσ v
  refine ⟨j, fun x hx => ?_⟩
  rw [cellRep_apply, inflateTwist_apply,
    sqrtModular_of_mem_integralGL' (p := permConj F β w x) (congruenceSubgroup_le F n j hx),
    one_smul]
  exact hj _ (leviProj_mem_congruenceSubgroup' (p := permConj F β w x) hx)
end GroundTheory.Automorphic.Parabolic
