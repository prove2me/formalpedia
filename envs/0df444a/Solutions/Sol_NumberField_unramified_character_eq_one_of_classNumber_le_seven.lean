-- Prove2me | solution 1 for NumberField.unramified_character_eq_one_of_classNumber_le_seven
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:05.312948+00:00
-- url     : https://prove2.me/submissions/1ac9613f-fa36-4b1c-b1b6-fd06d183ccee

import Mathlib
import Theorems.Thm_IntermediateField_fixedField_of_finite_level_cyclic_character
import Theorems.Thm_NumberField_inertia_eq_bot_of_absolute_inertia_restrict_eq_one
import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq
import Theorems.Thm_NumberField_not_finrank_seventyOne_of_unramified_cyclic_of_classNumber_le_seven
import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber

set_option autoImplicit false

namespace NumberField

/-- The class-field obstruction for a literal finite-level degree-71 character.
The inertia hypothesis is quantified over valuation subrings of the algebraic
closure, and is transported to the finite extension cut out by the character. -/
theorem _root_.solution
    (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
    [IsGalois K (AlgebraicClosure ℚ)]
    (f : (AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ) →* Multiplicative (ZMod 71))
    (hlevel : ∃ E : IntermediateField K (AlgebraicClosure ℚ),
      FiniteDimensional K E ∧ E.fixingSubgroup ≤ f.ker)
    (hur : ∀ (q : ℕ), q.Prime → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime q → ∀
      (σ : AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ),
      σ ∈ A.inertiaSubgroupIn K → f σ = 1)
    (hclass : classNumber K ≤ 7) : f = 1 := by
  by_contra hnontrivial
  have hcard : Nat.card (Multiplicative (ZMod 71)) = 71 := by
    simp [Nat.card_eq_fintype_card]
  haveI : Fact (Nat.Prime (Nat.card (Multiplicative (ZMod 71)))) :=
    ⟨by rw [hcard]; decide⟩
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rcases f.range.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exfalso
      apply hnontrivial
      ext σ
      exact Subgroup.mem_bot.mp (hbot ▸ (show f σ ∈ f.range from ⟨σ, rfl⟩))
    · exact htop
  obtain ⟨hfinite, hgalois, hcyclic, hdegree⟩ :=
    IntermediateField.fixedField_of_finite_level_cyclic_character f hsurj hlevel
  let M := IntermediateField.fixedField f.ker
  letI : FiniteDimensional K M := hfinite
  letI : IsGalois K M := hgalois
  letI : IsCyclic (M ≃ₐ[K] M) := hcyclic
  letI : NumberField M := NumberField.of_module_finite K M
  have hrestrict : ∀ (q : ℕ), q.Prime → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime q → ∀
      (σ : AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ),
      σ ∈ A.inertiaSubgroupIn K → σ.restrictNormal M = 1 := by
    intro q hq A hA σ hσ
    ext x
    have hx := x.property
    rw [IntermediateField.mem_fixedField_iff] at hx
    change algebraMap M (AlgebraicClosure ℚ) ((σ.restrictNormal M) x) =
      algebraMap M (AlgebraicClosure ℚ) x
    rw [AlgEquiv.restrictNormal_commutes]
    exact hx σ (hur q hq A hA σ hσ)
  have hfinite_inertia : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (LanglandsTunnell.P2.Artin.primeAbove K M v).inertia (M ≃ₐ[K] M) = ⊥ := by
    intro v
    exact inertia_eq_bot_of_absolute_inertia_restrict_eq_one K M hrestrict
      ⟨LanglandsTunnell.P2.Artin.primeAbove K M v, inferInstance,
        LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩
  apply not_finrank_seventyOne_of_unramified_cyclic_of_classNumber_le_seven
    K M hfinite_inertia hclass
  exact hdegree.trans hcard

end NumberField
