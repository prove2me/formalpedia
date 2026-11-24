-- Prove2me | solution 1 for GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:47.507972+00:00
-- url     : https://prove2.me/submissions/1d97707c-d39d-4d2e-8ee6-e7c7ed6d77e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionDescendsEtaleCover
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmoothDescent
open TensorProduct KaehlerDifferential
namespace GlobalTheory.SmoothDescent
theorem _root_.solution (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Algebra.EssFiniteType R B] [Algebra.FormallySmooth R B] :
    Module.Flat R B := by
  let P := Algebra.EssFiniteType.subalgebra R B
  let M : Submonoid P := Algebra.EssFiniteType.submonoid R B
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R P)
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] B := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R P B).comp f₀) fun x ↦
    IsLocalization.map_units (M := M) B ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    exact (IsLocalization.lift_mk'_spec (M := M') (S := P')
      (g := ((IsScalarTower.toAlgHom R P B).comp f₀).toRingHom)
      (fun x ↦ IsLocalization.map_units (M := M) B ⟨f₀ x.1, x.2⟩) x _ ⟨s, hs⟩).mpr
      (IsLocalization.mk'_spec' B (f₀ x) (⟨f₀ s, hs⟩ : M)).symm
  have : Module.Flat R P' := .trans R (MvPolynomial (Fin n) R) P'
  exact Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing fP hf₁
end GlobalTheory.SmoothDescent
