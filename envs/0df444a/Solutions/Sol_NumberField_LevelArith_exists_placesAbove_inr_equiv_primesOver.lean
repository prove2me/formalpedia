-- Prove2me | solution 1 for NumberField.LevelArith.exists_placesAbove_inr_equiv_primesOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4918d417-a426-5e46-b7ae-9cd477743c63

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Theorems.Thm_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_equiv_primesOver
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain NumberField"
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise NumberField.PlaceTransport

namespace PlacesFin

lemma smul_asIdeal_eq_map_ringOfIntegersAut (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]
    (σ : F ≃ₐ[E] F) (w : HeightOneSpectrum (𝓞 F)) :
    (σ • w).asIdeal = w.asIdeal.map (ringOfIntegersAut E F σ) := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map]
  have : ((MulSemiringAction.toRingEquiv (F ≃ₐ[E] F) (𝓞 F) σ : 𝓞 F ≃+* 𝓞 F) : 𝓞 F →+* 𝓞 F) =
      ((ringOfIntegersAut E F σ : 𝓞 F ≃+* 𝓞 F) : 𝓞 F →+* 𝓞 F) := by
    apply RingHom.ext; intro x
    apply Subtype.ext
    rfl
  rw [this]
  rfl

end PlacesFin

theorem solution
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (q : ↥S) :
    ∃ e : placesAbove L S (Sum.inr q) ≃
        {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) // ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)) ∈ w.asIdeal)},
      ∀ (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inr q)),
        ((e ((orbitQuotientAction K L hnorm ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inr q)).range)).smul γ x)).1).asIdeal =
          ((e x).1).asIdeal.map (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ)) := by
  letI : MulAction ↥K.fixingSubgroup (placesAbove L S (Sum.inr q)) :=
    orbitQuotientAction K L hnorm ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inr q)).range)
  obtain ⟨e, hinj, hrange, he⟩ := NumberField.LevelArith.exists_placesAbove_inr_embedding_heightOneSpectrum K L hKL hnorm S q
  refine ⟨(Equiv.ofInjective e hinj).trans (Equiv.setCongr hrange), fun γ x => ?_⟩
  show (e ((orbitQuotientAction K L hnorm _).smul γ x)).asIdeal = (e x).asIdeal.map _
  rw [he γ x]
  exact PlacesFin.smul_asIdeal_eq_map_ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ) (e x)

end S_NumberField_LevelArith_exists_placesAbove_inr_equiv_primesOver
end P2MW
export P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_equiv_primesOver (solution)
