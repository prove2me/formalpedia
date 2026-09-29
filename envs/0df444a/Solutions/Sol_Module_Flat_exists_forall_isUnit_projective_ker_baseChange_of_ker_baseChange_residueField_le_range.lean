-- Prove2me | solution 1 for Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6b286b77-ba79-5f0d-8b4f-5927b0ea3633

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
import Theorems.Thm_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
import Theorems.Thm_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range

set_option autoImplicit false

universe u

open TensorProduct

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (𝔭 : PrimeSpectrum R)
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange 𝔭.asIdeal.ResidueField) ≤
        LinearMap.range ((d i).baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        Module.Finite A (LinearMap.ker ((d 0).baseChange A)) ∧
        Module.Projective A (LinearMap.ker ((d 0).baseChange A)) ∧
        (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)) ∧
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A) ∧
        (∀ 𝔮 : PrimeSpectrum A,
          Module.rankAtStalk (LinearMap.ker ((d 0).baseChange A)) 𝔮 =
            Module.finrank 𝔭.asIdeal.ResidueField (LinearMap.ker ((d 0).baseChange 𝔭.asIdeal.ResidueField))) := by
  classical
  obtain ⟨g, hg, hexS⟩ :=
    Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
      C d hdd n hbd hfin 𝔭 hfib
  have hB2 := fun (A : Type u) [CommRing A] [Algebra R A] (hA : IsUnit (algebraMap R A g)) =>
    Module.Flat.projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
      C d hdd n hbd hfin0 g (Localization.Away g) (hexS (Localization.Away g)) A hA
  haveI := hfin0
  have hproj : ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
      Module.Projective A (A ⊗[R] LinearMap.ker (d 0)) := by
    intro A _ _ hA
    obtain ⟨-, hP, -, hbij⟩ := hB2 A hA
    exact Module.Projective.of_equiv (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (d 0) A) hbij).symm
  obtain ⟨g', hg', hunit, hrank⟩ :=
    Module.exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor
      (LinearMap.ker (d 0)) 𝔭 g hg hproj
  refine ⟨g', hg', fun A _ _ hA => ?_⟩
  obtain ⟨hf, hP, hex, hbij⟩ := hB2 A (hunit A hA)
  refine ⟨hf, hP, hex, hbij, fun 𝔮 => ?_⟩

  have hκ : IsUnit (algebraMap R 𝔭.asIdeal.ResidueField g) := by
    rw [isUnit_iff_ne_zero, ne_eq, Ideal.algebraMap_residueField_eq_zero]
    exact hg
  obtain ⟨-, -, -, hbijκ⟩ := hB2 𝔭.asIdeal.ResidueField hκ
  rw [← Module.rankAtStalk_eq_of_equiv (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (d 0) A) hbij),
    hrank A hA 𝔮,
    ← (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (d 0) 𝔭.asIdeal.ResidueField) hbijκ).finrank_eq]

end S_Module_Flat_exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range
end P2MW
export P2MW.S_Module_Flat_exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range (solution)
