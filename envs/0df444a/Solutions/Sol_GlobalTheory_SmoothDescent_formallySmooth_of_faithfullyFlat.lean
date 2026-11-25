-- Prove2me | solution 1 for GlobalTheory.SmoothDescent.formallySmooth_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:53.808977+00:00
-- url     : https://prove2.me/submissions/8689be53-6176-499f-8039-f7308b6be4f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionDescendsEtaleCover
import Theorems.Thm_GlobalTheory_SmoothDescent_flat_of_formallySmooth_of_essFiniteType
import Theorems.Thm_GlobalTheory_SmoothDescent_formallySmooth_of_flat_of_formallyUnramified
import Theorems.Thm_GlobalTheory_SmoothDescent_formallyEtale_of_bijective_mapBaseChange
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_ringHom_flat_of_comp_faithfullyFlat
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
theorem _root_.solution (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsNoetherianRing R] [IsLocalRing A]
    [Algebra.EssFiniteType R A] [Algebra.EssFiniteType A B] [Module.FaithfullyFlat A B]
    [Algebra.FormallyEtale A B] [Algebra.FormallySmooth R B] : Algebra.FormallySmooth R A := by
  classical
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing R A
  have : Algebra.EssFiniteType R B := .comp R A B
  have : Module.FinitePresentation A Ω[A⁄R] := Module.finitePresentation_of_finite _ _
  have : Module.Flat B (B ⊗[A] Ω[A⁄R]) := .of_linearEquiv (tensorKaehlerEquivOfFormallyEtale R A B)
  have : Module.Flat A Ω[A⁄R] := Module.Flat.of_flat_tensorProduct _ _ B
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _ (span_range_derivation R A)
  have : Finite κ := Module.Finite.finite_basis b
  let P := MvPolynomial κ R
  let φ : P →ₐ[R] A := MvPolynomial.aeval a
  algebraize [φ.toRingHom, (algebraMap A B).comp φ.toRingHom]
  have : IsScalarTower R P B := .to₁₂₄ R P A B
  have hX (i : κ) : algebraMap P A (MvPolynomial.X i) = a i := MvPolynomial.aeval_X _ _
  let bB : Module.Basis κ B Ω[B⁄R] := (b.baseChange B).map (tensorKaehlerEquivOfFormallyEtale R A B)
  let bP : Module.Basis κ B (B ⊗[P] Ω[P⁄R]) := (mvPolynomialBasis R κ).baseChange B
  have hbij : Function.Bijective (mapBaseChange R P B) := by
    have : mapBaseChange R P B = (bP.equiv bB (Equiv.refl κ)).toLinearMap := by
      refine bP.ext fun i => ?_
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      simp [bP, bB, hb, ← hX, ← IsScalarTower.algebraMap_apply, P]
    rw [this]
    exact (bP.equiv bB (Equiv.refl κ)).bijective
  have : Algebra.FormallyEtale P B := formallyEtale_of_bijective_mapBaseChange R P B hbij
  let p : Ideal P := (IsLocalRing.maximalIdeal A).comap (algebraMap P A)
  let Q := Localization.AtPrime p
  let ψ : Q →ₐ[P] A := IsLocalization.liftAlgHom (M := p.primeCompl) (f := Algebra.ofId P A) fun x => by
    by_contra h
    exact x.2 h
  algebraize [ψ.toRingHom, (algebraMap A B).comp ψ.toRingHom]
  have : IsScalarTower P Q B := .to₁₂₄ P Q A B
  have : IsScalarTower R Q A := .to₁₃₄ R P Q A
  have : IsScalarTower R Q B := .to₁₂₄ R Q A B
  have : IsLocalHom (algebraMap Q A) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff Q p]
    intro hxp
    have e : algebraMap P A x = algebraMap P A s * algebraMap Q A (IsLocalization.mk' Q x s) := by
      rw [IsScalarTower.algebraMap_apply P Q A s, ← map_mul, IsLocalization.mk'_spec',
        ← IsScalarTower.algebraMap_apply]
    have hs : IsUnit (algebraMap P A s) := by
      by_contra h
      exact s.2 h
    exact hxp (e ▸ hs.mul hx)
  have : Algebra.FormallyEtale Q B := Algebra.FormallyEtale.localization_base p.primeCompl
  have : Algebra.EssFiniteType Q A := .of_comp R Q A
  have : Algebra.EssFiniteType Q B := .of_comp R Q B
  have : Module.Flat Q B := flat_of_formallySmooth_of_essFiniteType Q B
  have : Module.Flat Q A := by
    rw [← RingHom.flat_algebraMap_iff]
    refine ringHom_flat_of_comp_faithfullyFlat (β := algebraMap A B)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) ?_
    rw [← IsScalarTower.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Algebra.FormallyUnramified Q A := by
    have h1 : Subsingleton (B ⊗[A] Ω[A⁄Q]) := (tensorKaehlerEquivOfFormallyEtale Q A B).subsingleton
    exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B).mp h1⟩
  have : Algebra.FormallySmooth Q A := formallySmooth_of_flat_of_formallyUnramified Q A
  have : Algebra.FormallySmooth P A := .comp P Q A
  exact .comp R P A
end GlobalTheory.SmoothDescent
