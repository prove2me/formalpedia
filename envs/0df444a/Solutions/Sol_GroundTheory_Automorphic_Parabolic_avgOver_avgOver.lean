-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_avgOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:48.8328+00:00
-- url     : https://prove2.me/submissions/adc4e194-9ab4-44fb-a3a1-d7921829ab16

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_eq_sum
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_avgSub
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_sum
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_comp_mul_right_of_normal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_ne_zero_of_le_right

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
theorem _root_.solution {K' : Subgroup G} (hKK' : K ≤ K') (hf' : AvgFinite K' f) :
    avgOver K' (avgOver K f) = avgOver K' f := by
  classical
  have hf : AvgFinite K f := relIndex_ne_zero_of_le_right hKK' hf'
  set S' := (rightStab f).subgroupOf K'
  have : S'.FiniteIndex := ⟨hf'⟩
  set N := S'.normalCore
  have hNi : N.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hN1 : N ≤ S' := Subgroup.normalCore_le S'
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  have : N.FiniteIndex := ⟨hNi⟩
  let _ := Fintype.ofFinite (K' ⧸ N)

  have hN2 : N ≤ (rightStab (avgOver K f)).subgroupOf K' := by
    intro n hn y
    show avgOver K f (y * (n : G)) = avgOver K f y
    rw [avgOver_eq_sum, avgOver_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    set k : K := Quotient.out q
    let k' : K' := ⟨k, hKK' k.2⟩
    have hc : k'⁻¹ * n * k' ∈ N := by
      have := (Subgroup.normalCore_normal S').conj_mem n hn k'⁻¹
      simpa using this
    have hc' : ((k'⁻¹ * n * k' : K') : G) ∈ rightStab f := hN1 hc
    have := hc' (y * (k : G))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, k'] at this
    rw [← this]
    congr 1
    group
  funext x
  rw [avgOver_eq_avgSub hN2 hNi, avgOver_eq_avgSub hN1 hNi, avgSub_eq_sum, avgSub_eq_sum]
  simp only [avgOver_eq_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ q : K ⧸ (rightStab f).subgroupOf K,
      ∑ q' : K' ⧸ N, ((N.index : ℂ)⁻¹) • ((((rightStab f).relIndex K : ℂ)⁻¹) •
        f (x * ((Quotient.out q' : K') : G) * ((Quotient.out q : K) : G))) =
      (((rightStab f).relIndex K : ℂ)⁻¹) • avgSub K' N f x := by
    intro q
    have := avgSub_comp_mul_right_of_normal hNi hN1 (hKK' (Quotient.out q).2) x
    rw [avgSub_eq_sum, avgSub_eq_sum] at this
    rw [avgSub_eq_sum, ← this, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    rw [smul_smul, smul_smul, mul_comm]
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, avgSub_eq_sum]
  have hcard : (Fintype.card (K ⧸ (rightStab f).subgroupOf K) : ℂ) = (rightStab f).relIndex K := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hcard, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hf), one_smul, Finset.smul_sum]
end GroundTheory.Automorphic.Parabolic
