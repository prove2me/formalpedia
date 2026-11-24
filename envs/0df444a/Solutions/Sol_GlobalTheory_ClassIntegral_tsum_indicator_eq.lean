-- Prove2me | solution 1 for GlobalTheory.ClassIntegral.tsum_indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:10.394247+00:00
-- url     : https://prove2.me/submissions/fc88b425-7efb-418a-a806-3b6612ca914e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFundamentalDomainEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.ClassIntegral
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
omit [MeasurableSpace G] [MeasurableMul G]
namespace GlobalTheory.ClassIntegral
theorem _root_.solution (Γ K : Subgroup G) (g x : G) :
    ∑' γ : Γ, ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) =
      (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * (dcoset Γ K g).indicator 1 x := by
  classical
  by_cases hx : x ∈ dcoset Γ K g
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨δ, hδ, k, hk, rfl⟩ := hx
    rw [← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)⁻¹).tsum_eq]
    have := tsum_subtype {γ : Γ | g⁻¹ * (γ : G) * g ∈ K} (fun _ => (1 : ENNReal))
    refine Eq.trans ?_ this.symm
    refine tsum_congr fun γ => ?_
    have e : g⁻¹ * ((γ : G) * δ⁻¹ * (δ * g * k)) = g⁻¹ * γ * g * k := by group
    simp only [Set.indicator, Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Equiv.coe_mulRight,
      Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe, Pi.one_apply, Set.mem_setOf_eq, e,
      K.mul_mem_cancel_right hk]
  · rw [Set.indicator_of_notMem hx, mul_zero, ENNReal.tsum_eq_zero]
    intro γ
    apply Set.indicator_of_notMem
    intro h
    apply hx
    refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, h, ?_⟩
    simp only [Subgroup.smul_def, smul_eq_mul]
    group
end GlobalTheory.ClassIntegral
