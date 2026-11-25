-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_comp_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:44.070215+00:00
-- url     : https://prove2.me/submissions/61b8803a-5bca-4698-b372-c11ee32418ee

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_avgSub
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_comp_mul_right_of_normal

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
theorem _root_.solution (hf : AvgFinite K f) {k : G} (hk : k ∈ K) :
    avgOver K (fun y => f (y * k)) = avgOver K f := by
  set S := (rightStab f).subgroupOf K
  have : S.FiniteIndex := ⟨hf⟩
  set N := S.normalCore
  have hNi : N.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hN1 : N ≤ S := Subgroup.normalCore_le S
  have hN2 : N ≤ (rightStab fun y => f (y * k)).subgroupOf K := by
    intro n hn y
    show f (y * (n : G) * k) = f (y * k)
    let k' : K := ⟨k, hk⟩
    have hc : k'⁻¹ * n * k' ∈ N := by
      have := (Subgroup.normalCore_normal S).conj_mem n hn k'⁻¹
      simpa using this
    have hc' : ((k'⁻¹ * n * k' : K) : G) ∈ rightStab f := hN1 hc
    have := hc' (y * k)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    congr 1
    simp only [k']
    group
  funext x
  rw [avgOver_eq_avgSub hN2 hNi, avgOver_eq_avgSub hN1 hNi]
  exact avgSub_comp_mul_right_of_normal hNi hN1 hk x
end GroundTheory.Automorphic.Parabolic
