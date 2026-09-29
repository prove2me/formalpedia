-- Prove2me | solution 1 for NumberField.LevelArith.ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f236065a-6c43-5890-9da5-8377c56ba2fb

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
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem solution
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (hw : w.under (𝓞 ↥L) ∉ placesOverPrimesFinset ↥L S) :
    (w.under (𝓞 ↥L)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : NumberField ↥L := @NumberField.mk _ _ inferInstance inferInstance

  set 𝔭 := w.under (𝓞 ↥L) with h𝔭
  let ℓ : ℕ := ringChar (𝓞 ↥L ⧸ 𝔭.asIdeal)
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  letI : Field (𝓞 ↥L ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
  have hℓ : ℓ.Prime := CharP.char_is_prime (𝓞 ↥L ⧸ 𝔭.asIdeal) ℓ
  have hℓ𝔭 : ((ℓ : ℕ) : 𝓞 ↥L) ∈ 𝔭.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (𝓞 ↥L ⧸ 𝔭.asIdeal) ℓ
  have hℓS : (⟨ℓ, hℓ⟩ : Nat.Primes) ∉ S := fun hmem =>
    hw ((mem_placesOverPrimesFinset ↥L S 𝔭).2 ⟨⟨ℓ, hℓ⟩, hmem, hℓ𝔭⟩)

  let N : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)
  have hN : N.IsUnramifiedOutside S := hF.normalClosure
  haveI : FiniteDimensional ℚ ↥N := hN.1
  haveI : Normal ℚ ↥N := normalClosure.normal ℚ ↥F (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ ↥N := ⟨⟩
  have hFN : F ≤ N := IntermediateField.le_normalClosure F
  let ψ : ↥(levelField L F hLF) →ₐ[ℚ] ↥N :=
    { toFun := fun x => ⟨(x : AlgebraicClosure ℚ), hFN ((IntermediateField.mem_extendScalars hLF).1 x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let φL : ↥L →ₐ[ℚ] ↥N :=
    { toFun := fun x => ⟨(x : AlgebraicClosure ℚ), hFN (hLF x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  letI algLN : Algebra ↥L ↥N := φL.toRingHom.toAlgebra
  letI algFN : Algebra ↥(levelField L F hLF) ↥N := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower ↥L ↥(levelField L F hLF) ↥N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ ↥(levelField L F hLF) ↥N := IsScalarTower.of_algebraMap_eq fun q => (ψ.commutes q).symm

  have hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ → P.inertiaSubgroupIn ℚ ≤ N.fixingSubgroup :=
    fun P hP => hN.2 ⟨ℓ, hℓ⟩ hℓS P hP
  have hbb := NumberField.ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
    ↥L N φL ℓ hℓ hHin

  haveI : NumberField ↥N := @NumberField.mk _ _ inferInstance inferInstance
  haveI : IsScalarTower (𝓞 ↥L) (𝓞 ↥(levelField L F hLF)) (𝓞 ↥N) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (𝓞 ↥(levelField L F hLF)) (𝓞 ↥N) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Algebra.IsIntegral (𝓞 ↥(levelField L F hLF)) (𝓞 ↥N) := Algebra.IsIntegral.of_finite _ _

  have hℓw : ((ℓ : ℕ) : 𝓞 ↥(levelField L F hLF)) ∈ w.asIdeal := by
    have h0 : algebraMap (𝓞 ↥L) (𝓞 ↥(levelField L F hLF)) (ℓ : 𝓞 ↥L) ∈ w.asIdeal := Ideal.mem_comap.1 hℓ𝔭
    rwa [map_natCast] at h0
  obtain ⟨Q, hQmax, hQw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 ↥N) w.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (RingOfIntegers.algebraMap.injective ↥(levelField L F hLF) ↥N)]
    exact bot_le)
  have hℓQ : ((ℓ : ℕ) : 𝓞 ↥N) ∈ Q := by
    have h0 : algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥N) (ℓ : 𝓞 ↥(levelField L F hLF)) ∈ Q := by
      rw [← Ideal.mem_comap, hQw]; exact hℓw
    rwa [map_natCast] at h0
  have h1 := hbb Q hQmax hℓQ

  haveI := hQmax.isPrime
  have hmapP : Ideal.map (algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥N)) w.asIdeal ≠ ⊥ := fun h =>
    w.ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective ↥(levelField L F hLF) ↥N)).1 h)
  have hmapp : Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥N)) 𝔭.asIdeal ≠ ⊥ := fun h =>
    𝔭.ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective ↥L ↥N)).1 h)
  have hle : Ideal.map (algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥N)) w.asIdeal ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, hQw]
  have htower := Ideal.ramificationIdx_algebra_tower (p := 𝔭.asIdeal) (P := w.asIdeal) (Q := Q) hmapP hmapp hle
  have hunder : Q.under (𝓞 ↥L) = 𝔭.asIdeal := by
    have h2 : Q.under (𝓞 ↥(levelField L F hLF)) = w.asIdeal := hQw
    rw [← Ideal.under_under (B := 𝓞 ↥(levelField L F hLF)) Q, h2, h𝔭]
    rfl
  rw [hunder, htower] at h1
  exact Nat.eq_one_of_mul_eq_one_right h1

end S_NumberField_LevelArith_ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset
end P2MW
export P2MW.S_NumberField_LevelArith_ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset (solution)
