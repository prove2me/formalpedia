-- Prove2me | solution 1 for NumberField.AdeleRing.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c4a53485-e672-5fc4-865b-d2839d336aa1

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_M4aHerbrand_GenuineDescent

import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_adeleBaseChange_local_rigidity
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation NumberField P2MW.S_NumberField_AdeleRing_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower.NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith"
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp
open scoped NumberField.PlaceTransport

namespace NumberField
p2m_export "NumberField" "place AdeleRing SUnits.sUnits SUnits.mem_sUnits_iff SUnits.sUnitsRep SUnits.val SUnits.val_mem AdeleRing.unitIdelesOutside AdeleRing.mem_unitIdelesOutside_iff PlaceTransport.valuation_smul_apply PlaceTransport.under_smul"
namespace BetaUnitsOutsideProof
p2m_open "NumberField"

open IsDedekindDomain.HeightOneSpectrum

variable {E K K'' : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
  [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K'']

private theorem _root_.NumberField.BetaUnitsOutsideProof.under_under (w : HeightOneSpectrum (𝓞 K'')) : (w.under (𝓞 K)).under (𝓞 E) = w.under (𝓞 E) := by
  ext1
  rw [under_asIdeal, under_asIdeal, under_asIdeal, Ideal.under_under]

p2m_export "NumberField.BetaUnitsOutsideProof" "under_under"

theorem valuation_algebraMap_eq_one (w : HeightOneSpectrum (𝓞 K'')) (x : K) (h : (w.under (𝓞 K)).valuation K x = 1) :
    w.valuation K'' (algebraMap K K'' x) = 1 := by
  rw [← valuation_comap (𝓞 K) K K'' (𝓞 K'') w x, h, one_pow]

theorem semialgHom_mem_integers (w : HeightOneSpectrum (𝓞 K'')) (y : (w.under (𝓞 K)).adicCompletion K)
    (hy : y ∈ (w.under (𝓞 K)).adicCompletionIntegers K) :
    Extension.adicCompletionSemialgHom K K'' (⟨w, rfl⟩ : (w.under (𝓞 K)).Extension (𝓞 K'')) y ∈ w.adicCompletionIntegers K'' :=
  Extension.adicCompletionSemialgHom_image_adicCompletionIntegers K K'' (⟨w, rfl⟩ : (w.under (𝓞 K)).Extension (𝓞 K'')) ⟨y, hy, rfl⟩

end NumberField.BetaUnitsOutsideProof

open NumberField.BetaUnitsOutsideProof in

theorem solution
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K'']
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ x : (AdeleRing (𝓞 K) K)ˣ,
      x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} →
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K K'').β.toMonoidHom x ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 K'') K'' {w | w.under (𝓞 E) ∈ S}) ∧
    (∀ x : NumberField.SUnits.sUnitsRep E K S, ∃ x'' : NumberField.SUnits.sUnitsRep E K'' S,
      NumberField.SUnits.val E K'' S x'' = Units.map (algebraMap K K'' : K →* K'') (NumberField.SUnits.val E K S x)) := by
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  ·
    rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff] at hx ⊢
    intro w hw
    have hu : (w.under (𝓞 K)) ∉ {v : HeightOneSpectrum (𝓞 K) | v.under (𝓞 E) ∈ S} := fun h => by
      apply hw
      change w.under (𝓞 E) ∈ S
      rw [← under_under (K := K) w]
      exact h
    obtain ⟨h1, h2⟩ := hx _ hu
    have key := (M4aHerbrand.adeleBaseChange_local_rigidity K K''
        (M4aHerbrand.GenuineDescent.genuineBaseChange K K'')).1
    refine ⟨?_, ?_⟩
    · change (((M4aHerbrand.GenuineDescent.genuineBaseChange K K'').β
          ((x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 : IsDedekindDomain.FiniteAdeleRing (𝓞 K'') K'') w ∈ _
      rw [key]
      exact semialgHom_mem_integers w _ h1
    · change (((M4aHerbrand.GenuineDescent.genuineBaseChange K K'').β
          ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 : IsDedekindDomain.FiniteAdeleRing (𝓞 K'') K'') w ∈ _
      rw [key]
      exact semialgHom_mem_integers w _ h2
  ·
    refine ⟨⟨Additive.ofMul (Units.map (algebraMap K K'' : K →* K'') (NumberField.SUnits.val E K S x)), ?_⟩, rfl⟩
    change Units.map (algebraMap K K'' : K →* K'') (NumberField.SUnits.val E K S x) ∈ NumberField.SUnits.sUnits E K'' S
    rw [NumberField.SUnits.mem_sUnits_iff]
    intro σ w hw
    change w.valuation K'' (σ (algebraMap K K'' (NumberField.SUnits.val E K S x : K))) = 1
    have hsw : (σ⁻¹ • w).under (𝓞 E) ∉ S := by
      rw [NumberField.PlaceTransport.under_smul]; exact hw
    conv_lhs => rw [← smul_inv_smul σ w]
    rw [NumberField.PlaceTransport.valuation_smul_apply]
    apply valuation_algebraMap_eq_one
    have hnot : ((σ⁻¹ • w).under (𝓞 K)).under (𝓞 E) ∉ S := by
      rw [under_under]; exact hsw
    have := (NumberField.SUnits.mem_sUnits_iff E K S _).1 (NumberField.SUnits.val_mem E K S x) 1 _ hnot
    simpa using this

end S_NumberField_AdeleRing_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower
end P2MW
export P2MW.S_NumberField_AdeleRing_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower (solution)
