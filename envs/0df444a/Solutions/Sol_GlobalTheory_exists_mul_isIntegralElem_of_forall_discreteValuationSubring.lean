-- Prove2me | solution 1 for GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:54:30.532557+00:00
-- url     : https://prove2.me/submissions/1ffb92dd-e60c-429e-ba54-6e2b5349b7d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulIsIntegralElemOfForallDiscreteValuation
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating_notMem
import Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B),
      Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) →
      ∀ (p : Ideal C), p.IsPrime → ∀ f : B,
        (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V →
          (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) →
        ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by
  intro C B _ _ _ _ e he hloc p hp f hf
  haveI : Nontrivial B := ⟨⟨e 0, e 1, fun h => zero_ne_one (he h)⟩⟩
  haveI : NoZeroDivisors B := ⟨fun {a b} hab => by
    obtain ⟨c₁, s₁, u₁, h₁⟩ := hloc a
    obtain ⟨c₂, s₂, u₂, h₂⟩ := hloc b
    have hc : c₁ * c₂ = 0 := he (by
      rw [map_mul, ← h₁, ← h₂, map_zero,
        show a * e s₁ * (b * e s₂) = (a * b) * (e s₁ * e s₂) by ring, hab, zero_mul])
    rcases mul_eq_zero.1 hc with h | h
    · left
      rw [h, map_zero] at h₁
      exact u₁.mul_left_eq_zero.1 h₁
    · right
      rw [h, map_zero] at h₂
      exact u₂.mul_left_eq_zero.1 h₂⟩
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  let L := FractionRing B
  let β : B →+* L := algebraMap B L
  have hβ : Function.Injective β := IsFractionRing.injective B L
  letI : Algebra C L := (β.comp e).toAlgebra
  have hCL : ∀ c, algebraMap C L c = β (e c) := fun _ => rfl
  have hinj : Function.Injective (algebraMap C L) := hβ.comp he
  haveI : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).2 hinj
  have hne : ∀ s : C, IsUnit (e s) → β (e s) ≠ 0 := fun s hs => ((hs.map β).ne_zero)
  haveI : IsFractionRing C L := IsFractionRing.of_field C L fun z => by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    obtain ⟨cx, sx, ux, hx⟩ := hloc x
    obtain ⟨cy, sy, uy, hy'⟩ := hloc y
    refine ⟨cx * sy, cy * sx, ?_⟩
    have hy0 : β y ≠ 0 := by
      rw [map_ne_zero_iff _ hβ]; exact nonZeroDivisors.ne_zero hy
    show β x / β y = _
    simp only [hCL, map_mul]
    rw [← hx, ← hy']
    simp only [map_mul]
    rw [div_eq_div_iff hy0 (mul_ne_zero (mul_ne_zero hy0 (hne sy uy)) (hne sx ux))]
    ring
  let Cp := Localization.AtPrime p
  haveI : IsNoetherianRing Cp := IsLocalization.isNoetherianRing p.primeCompl Cp inferInstance
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap C L y) := fun y => by
    refine isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinj).2 ?_)
    intro h0
    exact y.2 (h0 ▸ p.zero_mem)
  letI : Algebra Cp L := (IsLocalization.lift (M := p.primeCompl) (S := Cp) hunit).toAlgebra
  haveI : IsScalarTower C Cp L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
  haveI : IsFractionRing Cp L := IsFractionRing.isFractionRing_of_isLocalization p.primeCompl Cp L
    p.primeCompl_le_nonZeroDivisors
  haveI : Algebra.EssFiniteType Cp L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors Cp)
  have hint : IsIntegral Cp (β f) := by
    by_contra hn
    obtain ⟨V, hV, hd, hfV⟩ := exists_discreteValuationSubring_dominating_notMem hn
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff _ V).1 hd
    apply hfV
    refine hf L β V hV (fun c => ?_) (fun c hc => ?_)
    · have := h1 (algebraMap C Cp c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    · have := h2 (algebraMap C Cp c)
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Cp p c).2 hc)
      rwa [← IsScalarTower.algebraMap_apply] at this
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl (β f) hint
  refine ⟨d, hd, ?_⟩
  obtain ⟨q, hq, hq0⟩ := hdi
  refine ⟨q, hq, hβ ?_⟩
  rw [Polynomial.hom_eval₂, map_zero, ← hq0, Submonoid.smul_def, Algebra.smul_def, hCL, map_mul]
  rfl
end GlobalTheory
