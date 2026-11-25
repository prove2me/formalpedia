-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_conj_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:25.826895+00:00
-- url     : https://prove2.me/submissions/29d2313b-f071-441d-90bb-361acde05270

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_inv_conj_apply_facts
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {C : Set (GL (Fin n) F)} (hC : IsCompact C) (t : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z ∈ C, z ∈ oppositeUnipotentRadical F n β → z⁻¹ ∈ C →
      (rankTorus F n β m)⁻¹ * z * rankTorus F n β m ∈ congruenceSubgroup F n t := by
  obtain ⟨k, hk⟩ := exists_pow_mul_mem_of_isCompact F n hC
  refine ⟨k + t, fun m hm z hzC hz hz' => ?_⟩
  have hfz := rankTorus_inv_conj_apply_facts hm hz (hk z hzC)
  have hfz' := rankTorus_inv_conj_apply_facts hm
    ((oppositeUnipotentRadical F n β).inv_mem hz) (hk _ hz')
  rw [mem_congruenceSubgroup_iff, mem_integralGL_iff]
  refine ⟨⟨fun i j => (hfz i j).1, fun i j => ?_⟩, fun i j => (hfz i j).2⟩
  have : ((rankTorus F n β m)⁻¹ * z * rankTorus F n β m)⁻¹ =
      (rankTorus F n β m)⁻¹ * z⁻¹ * rankTorus F n β m := by group
  rw [this]
  exact (hfz' i j).1
end GroundTheory.Automorphic.Parabolic
