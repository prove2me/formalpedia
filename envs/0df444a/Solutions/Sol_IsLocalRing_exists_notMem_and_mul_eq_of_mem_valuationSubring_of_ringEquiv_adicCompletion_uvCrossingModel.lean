-- Prove2me | solution 1 for IsLocalRing.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/458c9311-1955-53d9-ac81-e4a4691b53b4

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W (π ^ E))
    {F : Type*} [Field F] (emb : B →+* F) (hemb : Function.Injective emb)
    (V : ValuationSubring F) (hBV : ∀ b : B, emb b ∈ V)
    (P : Ideal B) (hP : ∀ b : B, b ∈ P ↔ emb b ∈ V.nonunits) (hPm : P ≠ IsLocalRing.maximalIdeal B) :
    ∀ x : F, x ∈ V → (∃ r₀ s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r₀) → ∃ r s : B, s ∉ P ∧ x * emb s = emb r := by
  classical

  let embV : B →+* ↥V := emb.codRestrict V hBV
  have hPeq : P = Ideal.comap embV (IsLocalRing.maximalIdeal ↥V) := by
    ext b
    rw [hP, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  haveI hPprime : P.IsPrime := by rw [hPeq]; infer_instance
  intro x hxV hfrac
  obtain ⟨r₀, s₀, hs₀, hx⟩ := hfrac

  by_cases hP0 : P = ⊥
  · exact ⟨r₀, s₀, by rw [hP0]; exact hs₀, hx⟩

  have hdim : ringKrullDim B ≤ 2 := by
    rw [← IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq B, ringKrullDim_eq_of_ringEquiv ι]
    exact ModularCurve.UVCrossingModel.ringKrullDim_le_two π hπ E hE
  have hnotmax : ¬ P.IsMaximal := fun hmax => hPm (IsLocalRing.eq_maximalIdeal hmax)
  have hht : P.height = 1 := Ideal.height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two hdim P hP0 hnotmax
  haveI : IsIntegrallyClosed B :=
    IsLocalRing.isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel π hπ E hE ι

  obtain ⟨V₁, hmem, hBV₁, hnon, -, -⟩ :=
    IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (K := FractionRing B) P hht

  let j : FractionRing B →+* F := IsFractionRing.lift hemb
  have hj : ∀ b : B, j (algebraMap B (FractionRing B) b) = emb b := fun b => IsFractionRing.lift_algebraMap hemb b
  have hes₀ : emb s₀ ≠ 0 := (map_ne_zero_iff emb hemb).mpr hs₀
  set y : FractionRing B := algebraMap B (FractionRing B) r₀ / algebraMap B (FractionRing B) s₀ with hy
  have hjy : j y = x := by
    rw [hy, map_div₀, hj, hj, div_eq_iff hes₀]
    exact hx.symm

  have hyV₁ : y ∈ V₁ := by
    by_contra hyn
    have hy0 : y ≠ 0 := fun h => hyn (h ▸ V₁.zero_mem)
    have hyinv : y⁻¹ ∈ V₁ := (V₁.mem_or_inv_mem y).resolve_left hyn
    have hx0 : x ≠ 0 := by rw [← hjy]; exact (map_ne_zero_iff j j.injective).mpr hy0
    obtain ⟨c, s, hsP, hcs⟩ := (hmem y⁻¹).mp hyinv
    have hcP : c ∈ P := by
      by_contra hcP
      apply hyn
      rw [hmem]
      refine ⟨s, c, hcP, ?_⟩
      rw [← hcs, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
    have hc' : emb c ∈ V.nonunits := (hP c).mp hcP
    have hs' : emb s ∉ V.nonunits := fun h => hsP ((hP s).mpr h)

    have hxc : emb s = x * emb c := by
      have h := congrArg j hcs
      rw [map_mul, map_inv₀, hjy, hj, hj] at h
      rw [← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    apply hs'
    rw [ValuationSubring.mem_nonunits_iff, hxc, map_mul]
    have h1 : V.valuation x ≤ 1 := (V.valuation_le_one_iff x).mpr hxV
    have h2 : V.valuation (emb c) < 1 := (ValuationSubring.mem_nonunits_iff (A := V)).mp hc'
    calc V.valuation x * V.valuation (emb c) ≤ 1 * V.valuation (emb c) := mul_le_mul_left h1 _
      _ = V.valuation (emb c) := one_mul _
      _ < 1 := h2
  obtain ⟨c, s, hsP, hcs⟩ := (hmem y).mp hyV₁
  refine ⟨c, s, hsP, ?_⟩
  have h := congrArg j hcs
  rwa [map_mul, hjy, hj, hj] at h

end S_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
end P2MW
export P2MW.S_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel (solution)
