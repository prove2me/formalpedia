-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_internal_norm_morphisms_and_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T10:54:59.458646+00:00
-- url     : https://prove2.me/submissions/00f26b9c-9dff-46fd-887c-0a3db983c638

import Theorems.Thm_MazurTransfer_internal_monoid_morphism_of_all_points
import Theorems.Thm_MazurTransfer_ProperUnramifiedInertiaFibres_inertia_fixed_of_image_fixed
import Theorems.Thm_MazurTransfer_ProperGenericInertiaFibres_generic_inertia_fixed_of_image_fixed
import Theorems.Thm_MazurTransfer_Order13LocalRingInValuationSubring_local_coefficients_mem
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same original integral norm maps are internal group morphisms, and genuine dyadic valuation inertia fixes every actual norm lift with fixed image.
Named downstream consumer: dyadic unramified continuous Kummer classes and the two fixed norm quotient injections.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalNormInertiaScopedGroupProvidersV220261019
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_scalar_nineteen_and_finite_etale_norm_fibres
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedPicardGeometry
open Order13DyadicMixedGenericNorms Order13DyadicMixedIntegralNormExtensions
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedGenericNormGroupLaws
open Order13DyadicMixedIntegralNormGroupLaws Order13DyadicMixedIntegralNormComposition
open scoped CategoryTheory.MonObj
open Order13DyadicMixedIntegralScalarNineteen Order13DyadicMixedScalarInputs
open Order13DyadicMixedIntegralNormFinite Order13DyadicMixedIntegralNormEtale
open Order13DyadicMixedIntegralNormInternalMorphism Order13DyadicMixedIntegralNormInertia
open Order13DyadicMixedActualNormInertia
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInternalMorphism
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormInertia.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInertia
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormInternalMorphism
attribute [local instance] MazurTransfer.Order13DyadicMixedActualNormInertia.instFactPrimeOfNatNat_order13DyadicMixedActualNormInertia

namespace MazurTransfer.ActualDyadicOriginalInternalNormInertiaProofBoundaryTheoremBundleV320261019
end MazurTransfer.ActualDyadicOriginalInternalNormInertiaProofBoundaryTheoremBundleV320261019

namespace MazurTransfer.DyadicInertiaPublicFiniteEtaleBridgeV220261019
theorem integral_norms_etale : Etale integralPi.val ∧ Etale integralPiConjugate.val :=
  MazurTransfer.order13_actual_dyadic_scalar_nineteen_and_finite_etale_norm_fibres.2.2.2.2.1
end MazurTransfer.DyadicInertiaPublicFiniteEtaleBridgeV220261019
open MazurTransfer.DyadicInertiaPublicFiniteEtaleBridgeV220261019

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: The same original actual norm maps are internal morphisms of the selected integral group law, and genuine valuation inertia at two fixes every actual norm lift whose image is fixed.
Named downstream consumer: Actual dyadic unramified continuous Kummer classes and the two fixed norm quotient injections.
Original headers and attribution are retained below.
-/

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transfer proper unramified inertia lift uniqueness to
the generic fibre, retaining the actual scalar and Galois maps.
Named downstream consumer: good-prime inertia fixed rational norm lifts.
-/

noncomputable section
namespace MazurTransfer.OriginalDyadicNormInertiaBaseMapCompatibility20261019
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u
variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]

theorem spec_aut_comp_base (σ : Ω ≃ₐ[K] Ω) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply congrArg CommRingCat.ofHom
  exact RingHom.ext (fun k => σ.commutes k)

end MazurTransfer.OriginalDyadicNormInertiaBaseMapCompatibility20261019
end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: translate preservation of the represented relative group
law on all scheme points into the accepted public internal morphism contract.
Named downstream consumer: the SAME order-13 integral norm extensions.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj
universe u
namespace MazurTransfer.OriginalDyadicNormInternalMorphismBridge20261019

theorem isMonHom_of_all_points {R : Type u} [CommRing R]
    {A B : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {g : B ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (H : RelativeGroupLaw R g)
    (φ : SchemeHomOver f g)
    (h1 : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      NeronModelInfra.schemeHomOverComp (G.one t) φ = H.one t)
    (hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (G.mul t x y) φ =
        H.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) :
    letI := G.grpObjOverMk
    letI := H.grpObjOverMk
    IsMonHom (schemeHomOverToOverHom φ) := by
  letI := G.grpObjOverMk
  letI := H.grpObjOverMk
  apply MazurTransfer.internal_monoid_morphism_of_all_points
  · intro T
    apply (overHomEquivSchemeHomOver T g).injective
    have hc : ∀ x : T ⟶ Over.mk f,
        overHomEquivSchemeHomOver T g (x ≫ schemeHomOverToOverHom φ) =
          NeronModelInfra.schemeHomOverComp (overHomEquivSchemeHomOver T f x) φ :=
      fun x => Subtype.ext rfl
    rw [hc, G.overHomEquivSchemeHomOver_one, H.overHomEquivSchemeHomOver_one]
    exact h1 T.hom
  · intro T x y
    apply (overHomEquivSchemeHomOver T g).injective
    have hc : ∀ x : T ⟶ Over.mk f,
        overHomEquivSchemeHomOver T g (x ≫ schemeHomOverToOverHom φ) =
          NeronModelInfra.schemeHomOverComp (overHomEquivSchemeHomOver T f x) φ :=
      fun x => Subtype.ext rfl
    rw [hc, G.overHomEquivSchemeHomOver_mul, H.overHomEquivSchemeHomOver_mul,
      hc, hc]
    exact hm T.hom _ _

end MazurTransfer.OriginalDyadicNormInternalMorphismBridge20261019
#print axioms MazurTransfer.OriginalDyadicNormInternalMorphismBridge20261019.isMonHom_of_all_points

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the following checked good-prime proof is adapted to the
SAME selected actual dyadic Picard, its represented group law and actual
rational norm maps. No unit assumption on two or 104 is added.
Named downstream consumer: finite etale dyadic norm fibres and their
arithmetic inertia/Kummer condition. Original method and attribution follow.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: apply the accepted public all-points morphism contract
to the SAME integral extensions with the already selected local group law.
Named downstream consumer: finite etale norm maps away from nineteen.
-/

noncomputable section
namespace MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedIntegralNormInternalMorphism
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13ActualDyadicMixedPicardNeronModel Order13DyadicMixedIntegralNormExtensions
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13DyadicMixedRationalPicardComparison
open Order13DyadicMixedIntegralNormGroupLaws Order13DyadicMixedIntegralNormPointwiseUnit
open scoped CategoryTheory.MonObj
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInternalMorphism
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormInternalMorphism.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormInternalMorphism

theorem integralNorm_isMonHom
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    letI := (dyadicLaw).grpObjOverMk
    IsMonHom (schemeHomOverToOverHom (integralNorm φ)) := by
  exact OriginalDyadicNormInternalMorphismBridge20261019.isMonHom_of_all_points
    (dyadicLaw) (dyadicLaw) (integralNorm φ)
    (integralNorm_preserves_all_units φ)
    (integralNorm_preserves_mul φ)

end MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedIntegralNormInternalMorphism
#print axioms MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedIntegralNormInternalMorphism.integralNorm_isMonHom

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inertia fixed lifts for the SAME two integral norm maps,
using valuation subrings that contain the local coefficient ring.
Named downstream consumer: actual dyadic unramified Kummer classes.
The original good-prime proof below is specialized to the SAME selected
mixed Z_(2) Picard and its actual finite etale norm extensions.
-/

noncomputable section
namespace MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedIntegralNormInertia
open CategoryTheory AlgebraicGeometry NeronModelInfra
open Order13ActualDyadicMixedPicardNeronModel Order13DyadicMixedPicardGeometry
open Order13DyadicMixedQuadraticCharts
open Order13DyadicMixedIntegralNormExtensions Order13DyadicMixedIntegralNormEtale
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormInertia.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormInertia
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra BaseRing Ω]
  [IsScalarTower BaseRing ℚ Ω]

theorem integral_norm_inertia_fixed_of_image_fixed
    (φ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase)
    (hφ : φ = integralPi ∨ φ = integralPiConjugate)
    (A : ValuationSubring Ω)
    (hA : ∀ r : BaseRing, algebraMap BaseRing Ω r ∈ A)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap BaseRing Ω)))
      dyadicPicard.toBase)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ.val =
      x.val ≫ φ.val) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by
  letI : IsProper dyadicPicard.toBase := dyadicPicard_geometry.2.1
  have he : Etale φ.val := by
    rcases hφ with rfl | rfl
    · exact (integral_norms_etale).1
    · exact (integral_norms_etale).2
  letI : Etale φ.val := he
  exact ProperUnramifiedInertiaFibres.inertia_fixed_of_image_fixed ℚ
    dyadicPicard.toBase φ.val φ.property A hA σ hσ x hx

end MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedIntegralNormInertia
#print axioms MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedIntegralNormInertia.integral_norm_inertia_fixed_of_image_fixed

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inertia fixes every geometric norm lift of a rational
point for the SAME actual rational Picard norm maps at TWO.
The original good-prime proof is specialized using the proved mixed
dyadic model, canonical rational comparison and finite etale extensions.
Named downstream consumer: unramified local Kummer restrictions.
-/

noncomputable section
namespace MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedActualNormInertia
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open Order13ActualDyadicMixedPicardNeronModel Order13DyadicMixedQuadraticCharts
open Order13DyadicMixedPicardGeometry
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedIntegralNormExtensions
open Order13DyadicMixedGenericNorms
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13DyadicMixedIntegralNormEtale
attribute [local instance] MazurTransfer.Order13DyadicMixedActualNormInertia.instFactPrimeOfNatNat_order13DyadicMixedActualNormInertia
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra BaseRing Ω]
  [IsScalarTower BaseRing ℚ Ω]

theorem actual_norm_inertia_fixed_of_image_fixed
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime 2)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ.left =
      x.val ≫ φ.left) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by
  let e := actualDyadicRationalOverIso
  let xg : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)))
      (pullback.snd dyadicPicard.toBase (specGenericFibreInclusion BaseRing ℚ)) :=
    ⟨x.val ≫ e.hom.left, by erw [Category.assoc, e.hom.w, x.property]⟩
  let ψ := integralNorm φ
  have he : Etale ψ.val := by
    rcases hφ with rfl | rfl
    · exact (integral_norms_etale).1
    · exact (integral_norms_etale).2
  letI : Etale ψ.val := he
  letI : IsProper dyadicPicard.toBase := dyadicPicard_geometry.2.1
  have hxg : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ xg.val ≫
      (genericFibreRestrict BaseRing ℚ dyadicPicard.toBase
        dyadicPicard.toBase ψ).val =
      xg.val ≫ (genericFibreRestrict BaseRing ℚ dyadicPicard.toBase
        dyadicPicard.toBase ψ).val := by
    rw [integralNorm_restrict]
    change Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      (x.val ≫ e.hom.left) ≫ (genericNorm φ).val =
      (x.val ≫ e.hom.left) ≫ (genericNorm φ).val
    erw [Category.assoc, genericNorm_intertwine φ]
    have h := congrArg (fun z => z ≫ e.hom.left) hx
    erw [Category.assoc] at h
    exact h
  have hg := ProperGenericInertiaFibres.generic_inertia_fixed_of_image_fixed ℚ
    dyadicPicard.toBase ψ A
    (fun r => Order13LocalRingInValuationSubring.local_coefficients_mem 2 A hA r)
    σ hσ xg hxg
  have hei : e.hom.left ≫ e.inv.left = 𝟙 _ :=
    congrArg (fun z => z.left) e.hom_inv_id
  have h := congrArg (fun z => z ≫ e.inv.left) hg
  change (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
    (x.val ≫ e.hom.left)) ≫ e.inv.left = (x.val ≫ e.hom.left) ≫ e.inv.left at h
  erw [Category.assoc, Category.assoc, hei, Category.comp_id] at h
  exact h

theorem actual_norm_lift_of_rational_point_inertia_fixed
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime 2)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (p : Spec (CommRingCat.of ℚ) ⟶ actualPicard.P)
    (hx : x.val ≫ φ.left = Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)) ≫ p) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by
  apply actual_norm_inertia_fixed_of_image_fixed φ hφ A hA σ hσ x
  rw [hx, ← Category.assoc, MazurTransfer.OriginalDyadicNormInertiaBaseMapCompatibility20261019.spec_aut_comp_base ℚ σ]

end MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedActualNormInertia
#print axioms MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedActualNormInertia.actual_norm_inertia_fixed_of_image_fixed
#print axioms MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedActualNormInertia.actual_norm_lift_of_rational_point_inertia_fixed

end

theorem solution : (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], letI := (dyadicLaw).grpObjOverMk
    IsMonHom (schemeHomOverToOverHom (integralNorm φ))) ∧ (∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra BaseRing Ω] [IsScalarTower BaseRing ℚ Ω], ∀ (φ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase)
    (hφ : φ = integralPi ∨ φ = integralPiConjugate)
    (A : ValuationSubring Ω)
    (hA : ∀ r : BaseRing, algebraMap BaseRing Ω r ∈ A)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap BaseRing Ω)))
      dyadicPicard.toBase)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ.val =
      x.val ≫ φ.val), Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val) ∧ (∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra BaseRing Ω] [IsScalarTower BaseRing ℚ Ω], ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime 2)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ.left =
      x.val ≫ φ.left), Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val) ∧ (∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra BaseRing Ω] [IsScalarTower BaseRing ℚ Ω], ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime 2)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (p : Spec (CommRingCat.of ℚ) ⟶ actualPicard.P)
    (hx : x.val ≫ φ.left = Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)) ≫ p), Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val) := by
  exact ⟨MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedIntegralNormInternalMorphism.integralNorm_isMonHom, MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedIntegralNormInertia.integral_norm_inertia_fixed_of_image_fixed, MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedActualNormInertia.actual_norm_inertia_fixed_of_image_fixed, MazurTransfer.NormInertiaTheoremBodyV220261019.Order13DyadicMixedActualNormInertia.actual_norm_lift_of_rational_point_inertia_fixed⟩
#print axioms solution
