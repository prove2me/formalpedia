-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacLoc.GoodInh.goodChar_of_hasConductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:21.083624+00:00
-- url     : https://prove2.me/submissions/655ab1e2-a395-4c90-a585-d2b977ca3171

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc ValuativeRel GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.GoodInh
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.VacLoc.GoodInh
theorem _root_.solution (χ : AddChar k Circle) (c : kˣ) (hχ : HasConductor χ c) :
    GoodChar (Circle.coeHom.compAddChar χ) 𝒪[k] c := by
  have hcoe : ∀ z, (Circle.coeHom.compAddChar χ) z = 1 ↔ χ z = 1 := fun z => by
    show ((χ z : Circle) : ℂ) = 1 ↔ _
    exact Circle.coe_eq_one
  refine ⟨fun x => ?_, IsNonarchimedeanLocalField.isCompact_closedBall k 1, Valuation.isOpen_integer,
    fun x => ?_, fun U hU => ?_, fun x => ?_⟩
  · show ‖((χ x : Circle) : ℂ)‖ = 1
    exact Circle.norm_coe _
  · have key : (∀ y ∈ 𝒪[k], (Circle.coeHom.compAddChar χ) (x * y) = 1) ↔
        ∀ y, ValuativeRel.valuation k y ≤ ValuativeRel.valuation k x → χ y = 1 := by
      simp only [hcoe]
      constructor
      · intro H y hy
        by_cases hx : x = 0
        · have h0 : ValuativeRel.valuation k y = 0 := by
            rw [hx, map_zero] at hy
            exact le_antisymm hy zero_le'
          rw [(Valuation.zero_iff _).1 h0, AddChar.map_zero_eq_one]
        · have hmem : x⁻¹ * y ∈ 𝒪[k] := by
            rw [Valuation.mem_integer_iff, map_mul]
            calc ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k y
                ≤ ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k x :=
                  mul_le_mul_of_nonneg_left hy zero_le'
              _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
          have h1 := H _ hmem
          rwa [mul_inv_cancel_left₀ hx] at h1
      · intro H y hy
        apply H
        rw [map_mul]
        calc ValuativeRel.valuation k x * ValuativeRel.valuation k y
            ≤ ValuativeRel.valuation k x * 1 :=
              mul_le_mul_of_nonneg_left ((Valuation.mem_integer_iff _ _).1 hy) zero_le'
          _ = ValuativeRel.valuation k x := mul_one _
    rw [key, hχ x, Valuation.mem_integer_iff, map_mul]
    constructor
    · intro hle
      calc ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k x
          ≤ ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k (c : k) :=
            mul_le_mul_of_nonneg_left hle zero_le'
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    · intro hle
      calc ValuativeRel.valuation k x
          = ValuativeRel.valuation k ((c : k) * (((c⁻¹ : kˣ) : k) * x)) := by
            rw [← mul_assoc, Units.mul_inv, one_mul]
        _ = ValuativeRel.valuation k (c : k) *
            ValuativeRel.valuation k (((c⁻¹ : kˣ) : k) * x) := map_mul _ _ _
        _ ≤ ValuativeRel.valuation k (c : k) * 1 := by
            rw [map_mul]
            exact mul_le_mul_of_nonneg_left hle zero_le'
        _ = ValuativeRel.valuation k (c : k) := mul_one _
  · obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).1 hU
    obtain ⟨δ, hδ0, hδ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
    obtain ⟨ϖ, hϖ⟩ := ValuativeRel.valuation_surjective (K := k) δ
    obtain ⟨z, hz⟩ := ValuativeRel.valuation_surjective (K := k)
      (γ : ValuativeRel.ValueGroupWithZero k)
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hz
      exact γ.ne_zero hz.symm
    have hϖ0 : ϖ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hϖ
      exact hδ0.ne hϖ
    refine ⟨Units.mk0 (z * ϖ) (mul_ne_zero hz0 hϖ0), fun y hy => hγ ?_⟩
    have hy' : ValuativeRel.valuation k y ≤ 1 := (Valuation.mem_integer_iff _ _).1 hy
    show ValuativeRel.valuation k (z * ϖ * y) < γ
    rw [map_mul, map_mul, hz, hϖ]
    calc (γ : ValuativeRel.ValueGroupWithZero k) * δ * ValuativeRel.valuation k y
        ≤ γ * δ * 1 := mul_le_mul_of_nonneg_left hy' zero_le'
      _ = γ * δ := mul_one _
      _ < γ * 1 := mul_lt_mul_of_pos_left hδ1 (zero_lt_iff.2 γ.ne_zero)
      _ = γ := mul_one _
  · by_cases hx : ValuativeRel.valuation k x ≤ 1
    · exact ⟨1, by simp, by simpa [Valuation.mem_integer_iff] using hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      refine ⟨(Units.mk0 x hx0)⁻¹, ?_, ?_⟩
      · rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, Units.val_mk0, Valuation.map_inv]
        exact (inv_le_one₀ ((Valuation.pos_iff _).2 hx0)).2 (le_of_lt (not_le.1 hx))
      · rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hx0]
        exact one_mem _
end GlobalTheory.CompanionTheory.VacLoc.GoodInh
