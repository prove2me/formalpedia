-- Prove2me | solution 1 for N25.GlobalKummer.psi_cocycle_class_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:09:11.963778+00:00
-- url     : https://prove2.me/submissions/120ff750-651a-4a44-9a6a-67b6451d77d6

import Mathlib
import Theorems.Thm_N25_GlobalKummer_psi_cocycle_restricted_character
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic
import Theorems.Thm_NumberField_unramified_character_eq_one_of_classNumber_le_seven
import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq
import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
import Theorems.Thm_groupCohomology_restriction_injective_of_index_five
import Theorems.Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
import Theorems.Thm_N25_psi_kernel_index
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_groupCohomology_H1pi_map_of_values

set_option autoImplicit false

noncomputable section

open CategoryTheory groupCohomology

namespace N25.GlobalKummer

local instance psiClassZeroPrimeSeventyOne_s3bcc05 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- A finite-level psi cocycle vanishes in cohomology if its restriction to the
quintic field is unramified at every finite place. -/
theorem _root_.solution
    (c : cocycles₁ psiRep)
    (hc : IsLevelConstant₁ (MonoidHom.id Gal) c)
    (hur : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ →
      psi σ = 1 → c σ = 0) : H1π psiRep c = 0 := by
  classical
  obtain ⟨j, hgal, hpsi, hj, f, hf, hlevel, hclass⟩ :=
    psi_cocycle_restricted_character c hc
  letI : Algebra characterField (AlgebraicClosure ℚ) := j.toRingHom.toAlgebra
  letI : IsScalarTower ℚ characterField (AlgebraicClosure ℚ) := IsScalarTower.of_algHom j
  letI : IsGalois characterField (AlgebraicClosure ℚ) := hgal
  have hfzero : f = 1 := by
    apply NumberField.unramified_character_eq_one_of_classNumber_le_seven
      characterField f hlevel ?_ hclass
    intro q hq A hA σ hσ
    rw [hf σ, hur q hq A hA (σ.restrictScalars ℚ) ?_ (hpsi σ)]
    · rfl
    · rcases hσ with ⟨τ, hτ, rfl⟩
      let τQ : A.decompositionSubgroup ℚ := ⟨τ.val.restrictScalars ℚ, τ.property⟩
      exact ⟨τQ, hτ, rfl⟩
  have hcker (σ : Gal) (hσ : psi σ = 1) : c σ = 0 := by
    let τ : AlgebraicClosure ℚ ≃ₐ[characterField] AlgebraicClosure ℚ :=
      { σ with commutes' := hj σ hσ }
    have h := congrArg (fun f => f τ) hfzero
    rw [hf τ] at h
    exact Multiplicative.ofAdd.injective h
  haveI : psi.ker.FiniteIndex := ⟨by rw [psi_kernel_index]; decide⟩
  apply restriction_injective_of_index_five psi.ker psi_kernel_index psiRep 1
  rw [map_zero]
  let d : cocycles₁ (Rep.res psi.ker.subtype psiRep) :=
    ⟨fun σ => c σ, by
      apply (mem_cocycles₁_iff _).mpr
      intro σ τ
      exact (mem_cocycles₁_iff _).mp c.property σ τ⟩
  have hd : d = 0 := by
    apply Subtype.ext
    funext σ
    exact hcker σ σ.property
  have hmap : (groupCohomology.map psi.ker.subtype
      (𝟙 (Rep.res psi.ker.subtype psiRep)) 1).hom (H1π psiRep c) =
      H1π (Rep.res psi.ker.subtype psiRep) d := by
    exact H1pi_map_of_values _ _ _ _ c d (fun _ => rfl)
  rw [hmap, hd, map_zero]

end N25.GlobalKummer
