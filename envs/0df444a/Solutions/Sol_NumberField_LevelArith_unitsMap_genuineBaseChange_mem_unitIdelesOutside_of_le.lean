-- Prove2me | solution 1 for NumberField.LevelArith.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/30ee5df9-7134-549c-934a-d88be34d9f3e

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

namespace P2MW.S_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation NumberField P2MW.S_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le.NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith"
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp
open scoped NumberField.PlaceTransport

namespace NumberField
p2m_export "NumberField" "place AdeleRing SUnits.sUnits SUnits.mem_sUnits_iff SUnits.sUnitsRep SUnits.val SUnits.val_mem AdeleRing.unitIdelesOutside AdeleRing.mem_unitIdelesOutside_iff PlaceTransport.valuation_smul_apply PlaceTransport.under_smul"
namespace SIdelePresProof
p2m_open "NumberField"

open IsDedekindDomain.HeightOneSpectrum

variable {E K' : Type} [Field E] [NumberField E] [Field K'] [NumberField K'] [Algebra E K']

theorem exists_natCast_mem_under_iff (S : Finset Nat.Primes) (w : HeightOneSpectrum (𝓞 K')) :
    (∃ p ∈ S, ((p : ℕ) : 𝓞 E) ∈ (w.under (𝓞 E)).asIdeal) ↔ ∃ p ∈ S, ((p : ℕ) : 𝓞 K') ∈ w.asIdeal := by
  refine exists_congr fun p => and_congr_right fun _ => ?_
  rw [under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]

theorem under_mem_placesOverPrimesFinset_iff (S : Finset Nat.Primes) (w : HeightOneSpectrum (𝓞 K')) :
    w.under (𝓞 E) ∈ placesOverPrimesFinset E S ↔ ∃ p ∈ S, ((p : ℕ) : 𝓞 K') ∈ w.asIdeal := by
  rw [mem_placesOverPrimesFinset]
  change (∃ p ∈ (S : Set Nat.Primes), ((p : ℕ) : 𝓞 E) ∈ (w.under (𝓞 E)).asIdeal) ↔ _
  simp only [Finset.mem_coe]
  exact exists_natCast_mem_under_iff S w

theorem valuation_algebraMap_eq_one (w : HeightOneSpectrum (𝓞 K')) (x : E) (h : (w.under (𝓞 E)).valuation E x = 1) :
    w.valuation K' (algebraMap E K' x) = 1 := by
  rw [← valuation_comap (𝓞 E) E K' (𝓞 K') w x, h, one_pow]

theorem semialgHom_mem_integers (w : HeightOneSpectrum (𝓞 K')) (y : (w.under (𝓞 E)).adicCompletion E)
    (hy : y ∈ (w.under (𝓞 E)).adicCompletionIntegers E) :
    Extension.adicCompletionSemialgHom E K' (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 K')) y ∈ w.adicCompletionIntegers K' :=
  Extension.adicCompletionSemialgHom_image_adicCompletionIntegers E K' (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 K')) ⟨y, hy, rfl⟩

end NumberField.SIdelePresProof

open NumberField.SIdelePresProof in

theorem solution
    (S : Finset Nat.Primes)
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F]
    (L₁ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F₁ : L₁ ≤ F₁) (hFF₁ : F ≤ F₁)
    [FiniteDimensional ℚ ↥L₁] [FiniteDimensional ℚ ↥F₁]
    [Algebra ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)]
    (halg : ∀ x : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) x : ↥(levelField L₁ F₁ hL₁F₁)) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) :
    (∀ x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ,
      x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)} →
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)).β.toMonoidHom x ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁) {w | w.under (𝓞 ↥L₁) ∈ (placesOverPrimesFinset ↥L₁ S)}) ∧
    (∀ x : (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), ∃ x' : (NumberField.SUnits.sUnitsRep ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)),
      NumberField.SUnits.val ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S) x' = Units.map (algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) : ↥(levelField L F hLF) →* ↥(levelField L₁ F₁ hL₁F₁)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x))  := by
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  ·
    rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff] at hx ⊢
    intro v hv
    have hv' : ¬ ∃ p ∈ S, ((p : ℕ) : 𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ∈ v.asIdeal := fun h =>
      hv ((under_mem_placesOverPrimesFinset_iff S v).2 h)
    have hu : (v.under (𝓞 ↥(levelField L F hLF))) ∉
        {w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)) | w.under (𝓞 ↥L) ∈ placesOverPrimesFinset ↥L S} := fun h =>
      hv' ((exists_natCast_mem_under_iff S v).1 ((under_mem_placesOverPrimesFinset_iff S _).1 h))
    obtain ⟨h1, h2⟩ := hx _ hu
    have key := (M4aHerbrand.adeleBaseChange_local_rigidity ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)
        (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁))).1
    refine ⟨?_, ?_⟩
    · change (((M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)).β
          ((x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) : AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))).2 : IsDedekindDomain.FiniteAdeleRing (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁)) v ∈ _
      rw [key]
      exact semialgHom_mem_integers v _ h1
    · change (((M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)).β
          ((x⁻¹ : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) : AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))).2 : IsDedekindDomain.FiniteAdeleRing (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁)) v ∈ _
      rw [key]
      exact semialgHom_mem_integers v _ h2
  ·
    refine ⟨⟨Additive.ofMul (Units.map (algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) : ↥(levelField L F hLF) →* ↥(levelField L₁ F₁ hL₁F₁))
        (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x)), ?_⟩, rfl⟩
    change Units.map (algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) : ↥(levelField L F hLF) →* ↥(levelField L₁ F₁ hL₁F₁)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x) ∈
      NumberField.SUnits.sUnits ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)
    rw [NumberField.SUnits.mem_sUnits_iff]
    intro σ w hw
    change w.valuation ↥(levelField L₁ F₁ hL₁F₁) (σ (algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x : ↥(levelField L F hLF)))) = 1

    have hsw : (σ⁻¹ • w).under (𝓞 ↥L₁) ∉ placesOverPrimesFinset ↥L₁ S := by
      rw [NumberField.PlaceTransport.under_smul]; exact hw
    conv_lhs => rw [← smul_inv_smul σ w]
    rw [NumberField.PlaceTransport.valuation_smul_apply]

    apply valuation_algebraMap_eq_one
    have hnot : ((σ⁻¹ • w).under (𝓞 ↥(levelField L F hLF))).under (𝓞 ↥L) ∉ placesOverPrimesFinset ↥L S := fun h =>
      hsw ((under_mem_placesOverPrimesFinset_iff S _).2
        ((exists_natCast_mem_under_iff S (σ⁻¹ • w)).1 ((under_mem_placesOverPrimesFinset_iff S _).1 h)))
    have := (NumberField.SUnits.mem_sUnits_iff ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) _).1
      (NumberField.SUnits.val_mem ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x) 1 _ hnot
    simpa using this

end S_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
end P2MW
export P2MW.S_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le (solution)
