-- Prove2me | solution 1 for NumberField.LevelArith.selmerStable_eq_selmer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e4ebeb19-8d5b-5687-81c1-7f1b8939c1e9

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_KummerCharacter
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_selmerStable_eq_selmer

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

open scoped NumberField.PlaceTransport

namespace CycBaseF4

open IsDedekindDomain

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]

omit [NumberField E] [NumberField F] in

lemma under_smul (σ : F ≃ₐ[E] F) (v : HeightOneSpectrum (𝓞 F)) : (σ • v).under (𝓞 E) = v.under (𝓞 E) := by
  apply HeightOneSpectrum.ext
  ext e
  show algebraMap (𝓞 E) (𝓞 F) e ∈ (σ • v).asIdeal ↔ algebraMap (𝓞 E) (𝓞 F) e ∈ v.asIdeal
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have h : σ⁻¹ • algebraMap (𝓞 E) (𝓞 F) e = algebraMap (𝓞 E) (𝓞 F) e := by
    apply NumberField.RingOfIntegers.coe_injective
    show σ⁻¹ (algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) e)) = algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) e)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 E) E F, AlgEquiv.commutes]
  rw [h]

omit [NumberField E] in

lemma valuationOfNeZeroMod_mk_eq (p : ℕ) {w w' : HeightOneSpectrum (𝓞 F)} {y y' : Fˣ}
    (h : w.valuationOfNeZero y = w'.valuationOfNeZero y') :
    w.valuationOfNeZeroMod p (QuotientGroup.mk y : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) =
      w'.valuationOfNeZeroMod p (QuotientGroup.mk y' : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) := by
  simp only [HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.coe_comp, Function.comp_apply]
  erw [QuotientGroup.map_mk, QuotientGroup.map_mk]
  rw [h]

omit [NumberField E] in

lemma valuationOfNeZero_smul (σ : F ≃ₐ[E] F) (v : HeightOneSpectrum (𝓞 F)) (u : Fˣ) :
    v.valuationOfNeZero (σ • u) = (σ⁻¹ • v).valuationOfNeZero u := by
  apply WithZero.coe_injective
  rw [HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq]
  conv_lhs => rw [← smul_inv_smul σ v]
  exact NumberField.PlaceTransport.valuation_smul_apply σ (σ⁻¹ • v) (u : F)

end CycBaseF4

theorem solution
    (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (p : ℕ) :
    selmerStable E F S p = selmer E F S p := by
  apply le_antisymm
  · intro x hx
    have h := (mem_selmerStable_iff E F S p x).1 hx 1
    rwa [one_smul] at h
  · intro x hx
    rw [mem_selmerStable_iff]
    intro σ
    obtain ⟨u, rfl⟩ := unitsModPow.mk_surjective F p x
    rw [smul_mk, mem_selmer_iff]
    rw [mem_selmer_iff] at hx
    intro v hv
    have hw : σ⁻¹ • v ∉ NumberField.SUnits.placesAbove E F S := by
      rwa [NumberField.SUnits.mem_placesAbove, CycBaseF4.under_smul, ← NumberField.SUnits.mem_placesAbove]
    have h := hx (σ⁻¹ • v) hw
    rw [CycBaseF4.valuationOfNeZeroMod_mk_eq F p (CycBaseF4.valuationOfNeZero_smul E F σ v u)]
    exact h

end S_NumberField_LevelArith_selmerStable_eq_selmer
end P2MW
export P2MW.S_NumberField_LevelArith_selmerStable_eq_selmer (solution)
