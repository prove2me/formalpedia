-- Prove2me | solution 1 for NumberField.LevelArith.exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ee4bc5da-d3f3-50c0-9cf0-0f60ceac2d79

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
import Theorems.Thm_NumberField_exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem
p2m_attr_erase "instance" "NumberField.LevelArith.instCommGroupUnitsModPow"
p2m_attr_erase "simp" "groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation NumberField P2MW.S_NumberField_LevelArith_exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem.NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem.NumberField.LevelArith"
p2m_open_scoped "NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem.NumberField.LevelArith NumberField.PlaceDecomp"
open scoped NumberField.InfPlaceDecomp

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing to_finiteDimensional AdeleRing LevelArith.mem_placesOverPrimes_iff placesOverPrimes mem_placesOverPrimes_iff AdeleRing.unitIdelesOutside exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField placesOverPrimes mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset"
namespace CapIdeleLevel
p2m_open "NumberField.LevelArith NumberField"

open scoped nonZeroDivisors

section GlueA
variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable abbrev finitePart : (AdeleRing R K)ˣ →* (FiniteAdeleRing R K)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K)).toMonoidHom

theorem finitePart_principal (k : Kˣ) :
    finitePart R K (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) k) =
      Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) k := by
  apply Units.ext; rfl

theorem mem_principalIdeles_sup_unitIdelesOutside_iff (T : Set (HeightOneSpectrum R)) (z : (AdeleRing R K)ˣ) :
    z ∈ M4aHerbrand.principalIdeles R K ⊔ NumberField.AdeleRing.unitIdelesOutside R K T ↔
      finitePart R K z ∈ (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range ⊔
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K T := by
  constructor
  · intro hz
    obtain ⟨a, ha, u, hu, rfl⟩ := Subgroup.mem_sup.1 hz
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 ha
    rw [map_mul, finitePart_principal]
    exact Subgroup.mul_mem_sup ⟨k, rfl⟩ hu
  · intro hz
    obtain ⟨a, ha, u, hu, hau⟩ := Subgroup.mem_sup.1 hz
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 ha
    refine Subgroup.mem_sup.2 ⟨Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) k, ⟨k, rfl⟩,
      (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) k)⁻¹ * z, ?_, mul_inv_cancel_left _ _⟩
    show finitePart R K ((Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) k)⁻¹ * z) ∈
      IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K T
    rw [map_mul, map_inv, finitePart_principal, ← hau, inv_mul_cancel_left]
    exact hu

end GlueA

section GlueB
variable (E K' : Type) [Field E] [NumberField E] [Field K'] [NumberField K'] [Algebra E K']

theorem setOf_under_mem_placesOverPrimesFinset_eq (S : Finset Nat.Primes) :
    {w : HeightOneSpectrum (𝓞 K') | w.under (𝓞 E) ∈ placesOverPrimesFinset E S} =
      NumberField.placesOverPrimes K' (S : Set Nat.Primes) := by
  ext w
  rw [Set.mem_setOf_eq, mem_placesOverPrimesFinset, NumberField.LevelArith.mem_placesOverPrimes_iff,
    NumberField.mem_placesOverPrimes_iff]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  rw [show ((q : ℕ) : 𝓞 K') = algebraMap (𝓞 E) (𝓞 K') ((q : ℕ) : 𝓞 E) from (map_natCast _ _).symm]
  exact Iff.rfl

end GlueB

end NumberField.LevelArith.CapIdeleLevel

open NumberField.LevelArith.CapIdeleLevel

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S) :
    ∃ (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hfd : FiniteDimensional ℚ ↥F₂) (_ : F₂.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F₂)
      (hFF₂ : F ≤ F₂),
      haveI := hfd
      ∀ [Algebra ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))],
        (∀ x : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) x : ↥(levelField L F₂ (hLF.trans hFF₂))) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) →
        ∀ z : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ,
          (∃ k : ℕ, z ^ p ^ k ∈ ((M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)})) →
          Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β.toMonoidHom z ∈ ((M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}) := by
  obtain ⟨F₂, hFF₂, hNF₂, hun, hgal, H⟩ :=
    NumberField.exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem S hpS F hF
  refine ⟨F₂, hNF₂.to_finiteDimensional, hun, hgal, hFF₂, ?_⟩
  intro _ halg z hz

  have hΨ : ∀ a : ↥F, (M4aHerbrand.Bridge.finiteConorm (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂)))) (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) a) =
      algebraMap ↥F₂ (FiniteAdeleRing (𝓞 ↥F₂) ↥F₂) (IntermediateField.inclusion hFF₂ a) := by
    intro a
    have e1 := M4aHerbrand.Bridge.finiteConorm_algebraMap (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) a
    have e2 : algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) a = IntermediateField.inclusion hFF₂ a := Subtype.ext (halg a)
    rw [e2] at e1
    exact e1

  have step1 : ∃ k : ℕ, finitePart (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) z ^ p ^ k ∈
      (Units.map (algebraMap ↥(levelField L F hLF) (FiniteAdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* FiniteAdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))).range ⊔
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) (NumberField.placesOverPrimes ↥(levelField L F hLF) (S : Set Nat.Primes)) := by
    obtain ⟨k, hk⟩ := hz
    refine ⟨k, ?_⟩
    rw [← map_pow, ← setOf_under_mem_placesOverPrimesFinset_eq ↥L ↥(levelField L F hLF) S]
    exact (mem_principalIdeles_sup_unitIdelesOutside_iff (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) _ _).1 hk

  have key := H (M4aHerbrand.Bridge.finiteConorm (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂)))) (M4aHerbrand.Bridge.continuous_finiteConorm _ _ _ _) hΨ (finitePart (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) z) step1

  rw [setOf_under_mem_placesOverPrimesFinset_eq ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) S,
    mem_principalIdeles_sup_unitIdelesOutside_iff (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))]
  have hfin : finitePart (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))
      (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β.toMonoidHom z) =
        Units.map ((M4aHerbrand.Bridge.finiteConorm (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂)))) : FiniteAdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) →* FiniteAdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))) (finitePart (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) z) := by
    apply Units.ext
    show ((M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β (z : AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))).2 =
      (M4aHerbrand.Bridge.finiteConorm (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂)))) ((z : AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)).2)
    rw [M4aHerbrand.GenuineDescent.genuineBaseChange_β, M4aHerbrand.Bridge.genuineβ_snd]
  rw [hfin]
  exact key

end S_NumberField_LevelArith_exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem
end P2MW
export P2MW.S_NumberField_LevelArith_exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem (solution)
