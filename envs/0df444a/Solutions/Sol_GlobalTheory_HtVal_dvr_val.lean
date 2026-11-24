-- Prove2me | solution 1 for GlobalTheory.HtVal.dvr_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:23.395811+00:00
-- url     : https://prove2.me/submissions/a228db55-bff4-4eae-b2c0-572a1912cdb0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHeightOneValuationsControlSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HtVal
namespace GlobalTheory.HtVal
theorem _root_.solution (S : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (K : Type) [Field K]
    [Algebra S K] [IsFractionRing S K] :
    ∃ w : Kˣ →* Multiplicative ℤ, ∀ x : Kˣ,
      0 ≤ Multiplicative.toAdd (w x) ↔ (x : K) ∈ (algebraMap S K).range := by
  let v0 : IsDedekindDomain.HeightOneSpectrum S :=
    ⟨IsLocalRing.maximalIdeal S, inferInstance, IsDiscreteValuationRing.not_a_field S⟩
  refine ⟨(WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹, fun x => ?_⟩
  have key : 0 ≤ Multiplicative.toAdd ((WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom))⁻¹ x) ↔ v0.valuation K x ≤ 1 := by
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, toAdd_inv, Left.nonneg_neg_iff]
    generalize hu : WithZero.unitsWithZeroEquiv.toMonoidHom
      ((Units.map (v0.valuation K).toMonoidWithZeroHom.toMonoidHom) x) = u
    have hc : v0.valuation K x = (u : WithZero (Multiplicative ℤ)) := by
      rw [← hu, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, WithZero.coe_unitsWithZeroEquiv_eq_units_val]
      rfl
    rw [hc, ← WithZero.coe_one (α := Multiplicative ℤ), WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one]
  rw [key]
  constructor
  · intro h
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => ?_
    have : v = v0 := by
      ext1
      exact IsLocalRing.eq_maximalIdeal v.isMaximal
    rw [this]; exact h
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact v0.valuation_le_one y
end GlobalTheory.HtVal
