-- Prove2me | solution 1 for NumberField.LevelArith.exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b50dfddb-2cc9-59f4-b8a4-39e3d41ee5d7

import Mathlib
import Theorems.Thm_NumberField_LevelArith_exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_LevelArith_isGalois_levelField
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

set_option maxHeartbeats 4000000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S) (k : ℕ) :
    ∃ (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF₁ : L ≤ F₁) (_ : F ≤ F₁) (hfd : FiniteDimensional ℚ ↥F₁)
      (_ : F₁.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F₁),
      haveI := hfd
      ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(levelField L F₁ hLF₁))),
        w ∈ NumberField.LevelArith.placesOverPrimes ↥(levelField L F₁ hLF₁) (S : Set Nat.Primes) →
        p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F₁ hLF₁) w) := by
  classical
  obtain ⟨F₀, hLF₀, hF₀S, hF₀gal, hF₀⟩ :=
    NumberField.LevelArith.exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp S hpS L hL k
  haveI hfd₀ : FiniteDimensional ℚ ↥F₀ := hF₀S.1
  haveI hnF₀ : Normal ℚ ↥F₀ := hF₀gal.to_normal

  have hFN : F ≤ IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) := IntermediateField.le_normalClosure F
  have hNS : (IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)).IsUnramifiedOutside S := hF.normalClosure
  haveI : FiniteDimensional ℚ ↥(IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)) := hNS.1
  have hFF₁ : F ≤ IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) ⊔ F₀ := hFN.trans le_sup_left
  have hLF₁ : L ≤ IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) ⊔ F₀ := hLF.trans hFF₁
  have hF₀F₁ : F₀ ≤ IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) ⊔ F₀ := le_sup_right
  have hF₁S : (IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) ⊔ F₀).IsUnramifiedOutside S := hNS.sup hF₀S
  haveI hfd₁ : FiniteDimensional ℚ ↥(IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) ⊔ F₀) := hF₁S.1
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI hnN : Normal ℚ ↥(IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)) :=
    normalClosure.normal ℚ ↥F (AlgebraicClosure ℚ)
  haveI : Normal ℚ ↥(IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) ⊔ F₀) :=
    @IntermediateField.normal_sup ℚ (AlgebraicClosure ℚ) _ _ _ (IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)) F₀ hnN hnF₀
  haveI hgal₁ : IsGalois ℚ ↥(IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) ⊔ F₀) := ⟨⟩
  refine ⟨IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) ⊔ F₀, hLF₁, hFF₁, hfd₁, hF₁S, hgal₁, ?_⟩
  intro w hw
  set F₁ := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) ⊔ F₀ with hF₁def
  have hK : levelField L F₀ hLF₀ ≤ levelField L F₁ hLF₁ :=
    (IntermediateField.extendScalars_le_extendScalars_iff _ _).2 hF₀F₁
  letI : Algebra ↥(levelField L F₀ hLF₀) ↥(levelField L F₁ hLF₁) := (IntermediateField.inclusion hK).toRingHom.toAlgebra
  haveI : IsScalarTower ↥L ↥(levelField L F₀ hLF₀) ↥(levelField L F₁ hLF₁) :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsGalois ↥L ↥(levelField L F₁ hLF₁) := NumberField.LevelArith.isGalois_levelField L F₁ hLF₁
  haveI : Normal ↥L ↥(levelField L F₀ hLF₀) := (NumberField.LevelArith.isGalois_levelField L F₀ hLF₀).to_normal
  obtain ⟨r, hr, -⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower
    ↥L ↥(levelField L F₀ hLF₀) ↥(levelField L F₁ hLF₁) w
  have h0 := hF₀ (IsDedekindDomain.HeightOneSpectrum.under (𝓞 ↥(levelField L F₀ hLF₀)) w) ?_
  · exact h0.trans (Subgroup.card_dvd_of_surjective r hr)
  · obtain ⟨q, hqS, hq⟩ := hw
    refine ⟨q, hqS, ?_⟩
    show ((q : ℕ) : 𝓞 ↥(levelField L F₀ hLF₀)) ∈ Ideal.comap (algebraMap (𝓞 ↥(levelField L F₀ hLF₀)) (𝓞 ↥(levelField L F₁ hLF₁))) w.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hq

end S_NumberField_LevelArith_exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
end P2MW
export P2MW.S_NumberField_LevelArith_exists_le_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp (solution)
