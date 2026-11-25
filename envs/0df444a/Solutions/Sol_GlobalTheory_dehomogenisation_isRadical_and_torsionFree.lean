-- Prove2me | solution 1 for GlobalTheory.dehomogenisation_isRadical_and_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:17.229795+00:00
-- url     : https://prove2.me/submissions/e7e09cd3-e94b-425b-9ae8-77af58089515

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DehomogenisationIsRadicalAndTorsionFree
import Theorems.Thm_GlobalTheory_exists_ker_eq_dehomogenisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (o σ : Type) [CommRing o] (I : Ideal (MvPolynomial σ o)) (i : σ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (I.IsRadical → (I ⊔ Ideal.span {MvPolynomial.X i - 1}).IsRadical) ∧ ((∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1} → F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1}) := by
  intro o σ _ I i hI
  obtain ⟨ψ, hC, hker⟩ := exists_ker_eq_dehomogenisation I i hI
  rw [← hker]
  refine ⟨fun hrad => ?_, fun htf c F hc hF => ?_⟩
  ·
    have : IsReduced (MvPolynomial σ o ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hrad
    rintro F ⟨n, hn⟩
    rw [RingHom.mem_ker] at hn ⊢
    rw [map_pow] at hn
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  ·
    rw [RingHom.mem_ker, map_mul] at hF
    rw [RingHom.mem_ker]
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective
      (S := Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X i)))
      (Submonoid.powers (Ideal.Quotient.mk I (MvPolynomial.X i))) (ψ F)
    simp only at hs
    rw [← hs, hC, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hF
    obtain ⟨⟨_, k, rfl⟩, hm⟩ := hF
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hIG : MvPolynomial.C c * (MvPolynomial.X i ^ k * G) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hm]
      simp only [map_mul, map_pow]
      ring
    have hG : MvPolynomial.X i ^ k * G ∈ I := htf c _ hc hIG
    rw [← hs, IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    change Ideal.Quotient.mk I (MvPolynomial.X i) ^ k * Ideal.Quotient.mk I G = 0
    rw [← map_pow, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hG
end GlobalTheory
