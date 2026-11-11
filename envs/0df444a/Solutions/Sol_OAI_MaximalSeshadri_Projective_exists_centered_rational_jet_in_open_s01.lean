-- Prove2me | solution 1 for OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:16:38.716568+00:00
-- url     : https://prove2.me/submissions/8b845d4a-300a-42ca-bcb4-b98f5b7d95c1

import Mathlib
import Definitions.Def_Q223SES009

section
-- module Solutions.Q223_SES.Seshadri_Projective_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] [Fintype σ]

lemma linearEquation_chart (t : σ → R) (i : σ) :
    Away.isLocalizationElem (poly_X_mem (R := R) i) (linearEquation_homogeneous t) =
      ∑ j, chartConstants i (t j) * chartCoordinate i j := by
  apply HomogeneousLocalization.val_injective _
  change (Away.mk _ _ 1 _ _).val = _
  rw [chart_val_mk]
  rw [← HomogeneousLocalization.algebraMap_apply]
  simp only [linearEquation, map_sum, map_mul, pow_one,
    HomogeneousLocalization.algebraMap_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [chart_val_constants, chart_val_coordinate]
  exact mul_assoc _ _ _

lemma hyperplane_chart_preimage (t : σ → R) (i : σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (linearEquation t) =
      PrimeSpectrum.basicOpen (∑ j, chartConstants i (t j) * chartCoordinate i j) := by
  rw [Proj.awayι_preimage_basicOpen _ _ (by decide) (linearEquation_homogeneous t)
    (by decide), linearEquation_chart]

lemma hyperplane_affine_preimage {Y : Scheme} (h : Y ⟶ Proj (PolyGrade R σ))
    (U : Y.affineOpens) (i : σ) (φ : PolyChart (R := R) i →+* Γ(Y, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) = U.2.fromSpec ≫ h)
    (t : σ → R) :
    U.2.fromSpec ⁻¹ᵁ (h ⁻¹ᵁ Proj.basicOpen (PolyGrade R σ) (linearEquation t)) =
      PrimeSpectrum.basicOpen (∑ j, φ (chartConstants i (t j)) * φ (chartCoordinate i j)) := by
  rw [← Scheme.Hom.comp_preimage, ← hφ, Scheme.Hom.comp_preimage,
    hyperplane_chart_preimage]
  ext x
  change φ (∑ j, chartConstants i (t j) * chartCoordinate i j) ∉ x.asIdeal ↔
    (∑ j, φ (chartConstants i (t j)) * φ (chartCoordinate i j)) ∉ x.asIdeal
  simp only [map_sum, map_mul]

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R σ : Type u} [CommRing R] [Fintype σ]

omit [Fintype σ] in
                                                                            
lemma projective_affine_constants {Y : Scheme} (h : Y ⟶ Proj (PolyGrade R σ))
    (g : Y ⟶ Spec (CommRingCat.of R)) (hbase : h ≫ projectiveToSpec = g)
    (U : Y.affineOpens) [Algebra R Γ(Y, U.1)]
    (hOver : Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, U.1))) = U.2.fromSpec ≫ g)
    (i : σ) (φ : PolyChart (R := R) i →+* Γ(Y, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) = U.2.fromSpec ≫ h) :
    ∀ c, φ (chartConstants i c) = algebraMap R Γ(Y, U.1) c := by
  have he : CommRingCat.ofHom (φ.comp (chartConstants i)) =
      CommRingCat.ofHom (algebraMap R Γ(Y, U.1)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← chart_toSpec,
      ← Category.assoc, hφ, Category.assoc, hbase, hOver]
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom he)

end
end MaximalSeshadri.Projective


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_RationalPoint
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

lemma exists_point_finite_type {K R : Type} [Field K] [IsAlgClosed K]
    [CommRing R] [Nontrivial R] [Algebra K R] [Algebra.FiniteType K R] :
    Nonempty (R →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let : m.IsMaximal := hm
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K _
  exact ⟨(IsAlgClosed.lift : (R ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m)⟩

end
end MaximalSeshadri.ProjectiveBertini
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_SectionMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coordinatesMap_preimage (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) (j : σ) :
    coordinatesMap X k a i hi ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = X.basicOpen (a j) := by
  rw [coordinatesMap, Scheme.Hom.comp_preimage,
    fromUnitCoordinate_preimage _ (coordinates_X_mem (K := K) i) _
      (by simpa only [eval₂Hom_X'] using hi) (by decide) (coordinates_X_mem (K := K) j),
    eval₂Hom_X', Scheme.toSpecΓ_preimage_basicOpen]

end

end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionsMorphism_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (j : σ) :
    sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j) =
      SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) U.ι (sectionFrame (s i))]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end
end MaximalSeshadri.Projective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ClosedEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma evalAway_constants {R : Type u} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      ((fromZeroRingHom (homogeneousSubmodule σ K) (.powers (X i))).comp
        projectiveConstants) = k := by
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
      (.powers (X i)) (projectiveConstants c)).val = k c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (algebraMap (MvPolynomial σ K) (Localization.Away (X i)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

@[reassoc]
theorem coordinatesMap_over {X : Scheme.{u}} (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    coordinatesMap X k a i hi ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  simp only [coordinatesMap, fromUnitCoordinate, projectiveBase, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (evalAway_constants k a i hi)

@[reassoc]
theorem sectionsMorphism_over {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (MaximalSeshadri.Frames.O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k s hcover ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover).hom_ext
  intro i
  change σ at i
  change (SectionOpens.isoOpen (s i)).ι ≫ _ = _
  rw [← Category.assoc, sectionsMorphism_local, coordinatesMap_over]
  change _ = (SectionOpens.isoOpen (s i)).ι ≫ X.toSpecΓ ≫ _
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

instance sectionsMorphism_proper {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (sectionsMorphism k s hcover) := by
  have : IsProper (sectionsMorphism k s hcover ≫ projectiveBase) := by
    rw [sectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionChart
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_C _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X : Scheme}

lemma sectionsMorphism_on {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (i : σ) (U : X.Opens) (hU : U ≤ SectionOpens.isoOpen (s i)) :
    U.ι ≫ sectionsMorphism k s hcover =
      coordinatesMap U.toScheme (U.ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrameOn (s i) U hU) (restrictSection U.ι (s j)))
        i (sectionFrameOn_normalized (s i) U hU) := by
  conv_lhs => rw [← X.homOfLE_ι hU, Category.assoc, sectionsMorphism_local,
    coordinatesMap_natural]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, X.homOfLE_ι]
  · funext j
    exact (sectionFrameOn_coefficient (s i) (s j) U hU).symm

lemma affine_coordinates_factor (U : X.affineOpens) (k : K →+* Γ(U.1.toScheme, ⊤))
    (a : σ → Γ(U.1.toScheme, ⊤)) (i : σ) (hi : a i = 1) :
    U.2.isoSpec.inv ≫ coordinatesMap U.1.toScheme k a i hi =
      fromUnitCoordinate (MvPolynomial.eval₂Hom (U.1.topIso.hom.hom.comp k)
        (fun j => U.1.topIso.hom (a j))) (by decide) (coordinates_X_mem i)
        (by simpa only [MvPolynomial.eval₂Hom_X', hi, map_one] using
          (isUnit_one : IsUnit (1 : Γ(X, U.1)))) := by
  rw [coordinatesMap, ← Category.assoc]
  have he : U.2.isoSpec.inv ≫ U.1.toScheme.toSpecΓ = Spec.map U.1.topIso.hom := by
    let : IsAffine U.1.toScheme := U.2
    change (Spec.map U.1.topIso.hom ≫ U.1.toScheme.isoSpec.inv) ≫ _ = _
    simp only [Category.assoc, Scheme.isoSpec_inv_toSpecΓ, Category.comp_id]
  rw [he]
  change Spec.map (CommRingCat.ofHom U.1.topIso.hom.hom) ≫ _ = _
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural _ _ _

lemma evalAway_coordinate {R : Type} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) (j : σ) :
    evalAway (MvPolynomial.eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [MvPolynomial.eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) (chartCoordinate i j) = a j := by
  have hh := evalAway_mk_clear (MvPolynomial.eval₂Hom k a) (poly_X_mem i)
    (by simpa only [MvPolynomial.eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (MvPolynomial.X j)
      (by simpa using (poly_X_mem (R := K) j))
  simpa only [chartCoordinate, MvPolynomial.eval₂Hom_X', hi, one_pow, mul_one] using hh

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothAffineRefinement
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

lemma spec_openScalars (g : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (openScalars g U.1)) = U.2.fromSpec ≫ g := by
  rw [openScalars, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom]
  rw [← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) U.2 _

theorem exists_standard_smooth_affine_inside
    (g : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n g]
    (W : X.Opens) (x : X) (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g U.1) := by
  obtain ⟨B, hB, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := g) x
  have hBtop : B = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = g x := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst B
  let e₀ : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g V) := by
    convert hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨⟨X.basicOpen f, hV.basicOpen f⟩, hxf, hfW, ?_⟩
  let : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  have hs := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (Γ(X, X.basicOpen f)) f (openScalars g V) hstd
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  exact (openScalars_restrict g (X.basicOpen_le f)).symm

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeneratedEtaleCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open KaehlerDifferential

section CoordinateBasis
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

theorem formallyUnramified_polynomial_of_basis
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyUnramified (MvPolynomial ι R) S := by
  have hz : KaehlerDifferential.map R (MvPolynomial ι R) S S = 0 := by
    apply b.ext
    intro i
    rw [hb, KaehlerDifferential.map_D]
    change D (MvPolynomial ι R) S
      (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) = 0
    exact Derivation.map_algebraMap _ _
  constructor
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S x
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S y
  rw [hz]
  rfl

theorem formallySmooth_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallySmooth (MvPolynomial ι R) S := by
  classical
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  let : Algebra R B := Algebra.compHom B (algebraMap R (MvPolynomial ι R))
  let : IsScalarTower R (MvPolynomial ι R) B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R S I hI (f.restrictScalars R)
  let : Algebra S B := g.toRingHom.toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let correction (i : ι) : I := ⟨algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) -
      g (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)), by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, sub_eq_zero]
    change _ = (Ideal.Quotient.mkₐ R I) (g _)
    rw [← AlgHom.comp_apply, hg]
    exact (f.commutes _).symm⟩
  let d : Derivation R S I := (b.constr S correction).compDer (D R S)
  let g' : S →ₐ[R] B := liftOfDerivationToSquareZero I hI d
  have hcoords (i : ι) : g' (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) =
      algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) := by
    change ((b.constr S correction) (D R S (algebraMap _ _ (MvPolynomial.X i))) : B) +
      g (algebraMap _ _ (MvPolynomial.X i)) = _
    rw [← hb, b.constr_basis]
    exact sub_add_cancel _ _
  have hcomm : g'.comp (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) =
      IsScalarTower.toAlgHom R (MvPolynomial ι R) B := by
    apply MvPolynomial.algHom_ext
    exact hcoords
  let lift : S →ₐ[MvPolynomial ι R] B :=
    { g'.toRingHom with commutes' := fun p => AlgHom.congr_fun hcomm p }
  refine ⟨lift, ?_⟩
  ext s
  change Ideal.Quotient.mk I (g' s) = f s
  rw [liftOfDerivationToSquareZero_mk_apply]
  exact AlgHom.congr_fun hg s

theorem formallyEtale_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyEtale (MvPolynomial ι R) S := by
  let := formallySmooth_polynomial_of_basis b hb
  let := formallyUnramified_polynomial_of_basis b hb
  constructor <;> infer_instance

end CoordinateBasis

end

noncomputable section
open KaehlerDifferential
universe u v w
variable {R : Type u} {S : Type v} {ι : Type w}
  [CommRing R] [CommRing S] [Algebra R S]

lemma differentials_span_of_generators (v : ι → S)
    (hv : Function.Surjective (MvPolynomial.aeval (R := R) v)) :
    Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤ := by
  apply top_unique
  rw [← span_range_derivation R S, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  obtain ⟨q, rfl⟩ := hv s
  induction q using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.aeval_C, Derivation.map_algebraMap]
      exact Submodule.zero_mem _
  | add f g hf hg =>
      simp only [map_add]
      exact Submodule.add_mem _ hf hg
  | mul_X f i hf =>
      simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
        (Submodule.smul_mem _ _ hf)

theorem exists_local_differential_basis [Algebra.Smooth R S]
    (v : ι → S)
    (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤)
    (p : Ideal S) [p.IsPrime] :
    ∃ g : S, g ∉ p ∧ ∃ (κ : Type w) (_ : Finite κ) (a : κ → ι)
      (b : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R]),
      ∀ i, b i = D R (Localization.Away g) (algebraMap S (Localization.Away g) (v (a i))) := by
  let w : ι → Ω[Localization.AtPrime p⁄R] :=
    fun i => map R R S (Localization.AtPrime p) (D R S (v i))
  have hw : Submodule.span (Localization.AtPrime p) (Set.range w) = ⊤ := by
    have hh := span_eq_top_of_isLocalizedModule (Localization.AtPrime p) p.primeCompl
      (map R R S (Localization.AtPrime p)) hv
    simpa only [← Set.range_comp, Function.comp_def, w] using hh
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat w hw
  let e : (κ →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i : κ => D R S (v (a i))
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] := map R R S (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p]
      Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have he : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e (l₁ (Finsupp.single i 1))
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb, w]
  have heₚ : Function.Bijective eₚ := he ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] := map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ : (κ →₀ Localization.Away g) →ₗ[Localization.Away g]
      Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  refine ⟨g, hg, κ, inferInstance, a, .ofRepr (LinearEquiv.ofBijective eₜ h).symm, ?_⟩
  intro i
  change eₜ (Finsupp.single i 1) = _
  trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e (l₁ₜ (Finsupp.single i 1))
  · simp [eₜ, -IsLocalizedModule.map_apply, l₁ₜ]
  · simp [l₂ₜ, e]

theorem coordinate_map_etale [Algebra.Smooth R S] [Finite ι]
    (v : ι → S) (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (v i)) :
    (MvPolynomial.aeval (R := R) v).toRingHom.Etale := by
  let φ := MvPolynomial.aeval (R := R) v
  let : Algebra (MvPolynomial ι R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ι R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FinitePresentation (MvPolynomial ι R) S :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ S
  let : Algebra.FormallyEtale (MvPolynomial ι R) S :=
    formallyEtale_polynomial_of_basis b (by
      intro i
      change b i = D R S (φ (MvPolynomial.X i))
      simpa only [φ, MvPolynomial.aeval_X] using hb i)
  change Algebra.Etale (MvPolynomial ι R) S
  constructor <;> infer_instance

theorem exists_local_etale_from_spanning (n : ℕ)
    [IsDomain S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (v : ι → S)
    (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤)
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S), g ∉ p ∧ ∃ (κ : Type w) (_ : Finite κ) (a : κ → ι),
      Nat.card κ = n ∧
      (MvPolynomial.aeval (R := R)
        (fun i => algebraMap S (Localization.Away g) (v (a i)))).toRingHom.Etale := by
  let : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  obtain ⟨g, hg, κ, hκ, a, b, hb⟩ := exists_local_differential_basis v hv p
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  have hg0 : g ≠ 0 := fun h => hg (h ▸ Ideal.zero_mem p)
  let : IsDomain (Localization.Away g) := Localization.Away.isDomain hg0
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 S (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away g
  let : Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away g) := by
    simpa using (Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := S)
      (T := Localization.Away g) (n := n) (m := 0))
  let : Algebra.IsStandardSmooth R (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  refine ⟨g, hg, κ, hκ, a, ?_, coordinate_map_etale _ b hb⟩
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := Localization.Away g) n
  rw [rank_eq_card_basis b] at hr
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hr

end

noncomputable section
open KaehlerDifferential TensorProduct
variable {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

lemma differentials_span_of_formallyEtale [Algebra.FormallyEtale S T]
    (v : ι → S) (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤) :
    Submodule.span T (Set.range (fun i => D R T (algebraMap S T (v i)))) = ⊤ := by
  let M := Submodule.span T (Set.range (fun i => D R T (algebraMap S T (v i))))
  have hmem (s : Ω[S⁄R]) : map R R S T s ∈ M := by
    have hh : Submodule.span S (Set.range (fun i => D R S (v i))) ≤
        (M.restrictScalars S).comap (map R R S T) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change map R R S T (D R S (v i)) ∈ M
      rw [map_D]
      exact Submodule.subset_span (Set.mem_range_self i)
    rw [hv] at hh
    exact hh (Submodule.mem_top)
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨z, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale R S T).surjective x
  induction z using OAI.tensorInductionOn with
  | tmul t s =>
      rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
      exact M.smul_mem t (hmem s)
  | add x y hx hy =>
      rw [map_add]
      exact M.add_mem hx hy

end
end MaximalSeshadri.AlgebraicJets


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ProjectiveCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma affine_restriction_etale (U V : X.affineOpens) (e : U.1 ≤ V.1) :
    (X.presheaf.map (homOfLE e).op).hom.Etale := by
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2
  have he := hV.map_fromSpec hU (homOfLE e).op
  have : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE e).op) ≫ hV.fromSpec) := by
    rw [he]
    infer_instance
  let : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE e).op)) :=
    IsOpenImmersion.of_comp _ hV.fromSpec
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance

lemma awayToSection_awayι (i : σ) :
    Spec.map (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i)) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
      (Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i) (by decide)).fromSpec := by
  let hV := Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i) (by decide)
  rw [← cancel_epi hV.isoSpec.hom, ← Category.assoc, hV.isoSpec_hom]
  change Proj.basicOpenToSpec _ _ ≫ _ = _
  rw [← Proj.basicOpenIsoSpec_hom _ _ (poly_X_mem i) (by decide),
    Proj.awayι, Iso.hom_inv_id_assoc]
  exact hV.toSpecΓ_fromSpec.symm

theorem closed_projective_affine_surjective (h : X ⟶ Proj (PolyGrade K σ))
    [IsClosedImmersion h] (i : σ) :
    ∃ (U : X.affineOpens) (φ : PolyChart (R := K) i →+* Γ(X, U.1)),
      U.1 = h ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ∧
      Function.Surjective φ ∧
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
          U.2.fromSpec ≫ h := by
  let V := Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)
  have hV : IsAffineOpen V := Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide)
  let U : X.affineOpens := ⟨h ⁻¹ᵁ V, hV.preimage h⟩
  let e := Proj.basicOpenIsoAway (PolyGrade K σ) _ (poly_X_mem i) (by decide)
  let φ : PolyChart (R := K) i →+* Γ(X, U.1) := (h.app V).hom.comp e.hom.hom
  refine ⟨U, φ, rfl, ?_, ?_⟩
  · exact (h.app_surjective V hV).comp (ConcreteCategory.bijective_of_isIso e.hom).surjective
  · change Spec.map (e.hom ≫ h.app V) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    have he : e.hom = Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) := rfl
    rw [he, awayToSection_awayι]
    rw [Scheme.Hom.app_eq_appLE]
    exact hV.SpecMap_appLE_fromSpec h U.2 le_rfl

open KaehlerDifferential MaximalSeshadri.AlgebraicJets

lemma differentials_span_projective_chart {A : Type} [CommRing A] [Algebra K A]
    (i : σ) (φ : PolyChart (R := K) i →+* A) (hφ : Function.Surjective φ)
    (hconst : ∀ c, φ (chartConstants i c) = algebraMap K A c) :
    Submodule.span A (Set.range (fun j : ChartVariables i =>
      D K A (-φ (chartCoordinate i j.1)))) = ⊤ := by
  have he : (MvPolynomial.aeval (R := K)
      (fun j : ChartVariables i => φ (chartCoordinate i j.1))).toRingHom =
      φ.comp (polyToChart i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.aeval _ (MvPolynomial.C c) = φ (polyToChart i (MvPolynomial.C c))
      rw [MvPolynomial.aeval_C]
      simpa only [polyToChart, MvPolynomial.eval₂Hom_C] using (hconst c).symm
    · intro j
      change MvPolynomial.aeval _ (MvPolynomial.X j) = φ (polyToChart i (MvPolynomial.X j))
      rw [MvPolynomial.aeval_X, polyToChart, MvPolynomial.eval₂Hom_X']
  have hp : Function.Surjective (MvPolynomial.aeval (R := K)
      (fun j : ChartVariables i => φ (chartCoordinate i j.1))) := by
    change Function.Surjective (MvPolynomial.aeval _).toRingHom
    rw [he]
    exact hφ.comp (polynomialChartEquiv (R := K) i).symm.surjective
  have hs := differentials_span_of_generators _ hp
  have hr : Set.range (fun j : ChartVariables i => D K A (-φ (chartCoordinate i j.1))) =
      -(Set.range (fun j : ChartVariables i => D K A (φ (chartCoordinate i j.1)))) := by
    ext x
    simp only [Set.mem_range, Set.mem_neg, map_neg, neg_eq_iff_eq_neg]
  rw [hr, Submodule.span_neg]
  exact hs

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ProjectiveRefinement
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                             

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open MaximalSeshadri.Projective MaximalSeshadri.AlgebraicJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma restrict_projective_factor (h : X ⟶ Proj (PolyGrade K σ))
    (U V : X.affineOpens) (e : U.1 ≤ V.1) (i : σ)
    (φ : PolyChart (R := K) i →+* Γ(X, V.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        V.2.fromSpec ≫ h) :
    Spec.map (CommRingCat.ofHom ((X.presheaf.map (homOfLE e).op).hom.comp φ)) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ, ← Category.assoc,
    CommRingCat.ofHom_hom, V.2.map_fromSpec U.2]

lemma etale_aeval_equiv {A B ι : Type} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) (v : ι → A)
    (hv : (MvPolynomial.aeval (R := K) v).toRingHom.Etale) :
    (MvPolynomial.aeval (R := K) (fun i => e (v i))).toRingHom.Etale := by
  have hh := RingHom.Etale.respectsIso.1 _ e.toRingEquiv hv
  change (e.toAlgHom.comp (MvPolynomial.aeval (R := K) v)).toRingHom.Etale at hh
  rw [MvPolynomial.comp_aeval] at hh
  exact hh

theorem exists_etale_projective_chart [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (i : σ) (W : X.Opens) (x : X) (hxW : x ∈ W)
    (hxi : h x ∈ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W ∧ C.coord = i := by
  classical
  obtain ⟨V, φ, hV, hsurj, hφ⟩ := closed_projective_affine_surjective h i
  have hxV : x ∈ V.1 := by rwa [hV]
  obtain ⟨U, hxU, hUW, hstd⟩ := exists_standard_smooth_affine_inside g 2
    (W ⊓ V.1) x ⟨hxW, hxV⟩
  have e : U.1 ≤ V.1 := hUW.trans inf_le_right
  let : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  let : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  let : Algebra K Γ(X, V.1) := (openScalars g V.1).toAlgebra
  let : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
  let r : Γ(X, V.1) →+* Γ(X, U.1) := (X.presheaf.map (homOfLE e).op).hom
  let : Algebra Γ(X, V.1) Γ(X, U.1) := r.toAlgebra
  let : IsScalarTower K Γ(X, V.1) Γ(X, U.1) :=
    IsScalarTower.of_algebraMap_eq' (openScalars_restrict g e).symm
  let : Algebra.Etale Γ(X, V.1) Γ(X, U.1) := affine_restriction_etale U V e
  have hconst := projective_affine_constants h g hbase V (spec_openScalars g V) i φ hφ
  have hspan := differentials_span_projective_chart i φ hsurj hconst
  have hs := differentials_span_of_formallyEtale (T := Γ(X, U.1))
    (fun j : ChartVariables i => -φ (chartCoordinate i j.1)) hspan
  let φU := r.comp φ
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 K Γ(X, U.1) := hstd
  let p : PrimeSpectrum Γ(X, U.1) := U.2.isoSpec.hom ⟨x, hxU⟩
  obtain ⟨f, hfp, κ, hκ, a, hcard, het⟩ := exists_local_etale_from_spanning 2
    (fun j : ChartVariables i => -φU (chartCoordinate i j.1))
    (by simpa only [φU, RingHom.comp_apply, map_neg, RingHom.algebraMap_toAlgebra] using hs) p.asIdeal
  let T : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
  have hxf : x ∈ T.1 := by
    have hp : U.2.fromSpec p = x := by
      change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨x, hxU⟩ = x
      rw [U.2.isoSpec_hom_fromSpec]
      rfl
    have hm : p ∈ PrimeSpectrum.basicOpen f := hfp
    rw [← U.2.fromSpec_preimage_basicOpen f] at hm
    change U.2.fromSpec p ∈ X.basicOpen f at hm
    rwa [hp] at hm
  let r' : Γ(X, U.1) →+* Γ(X, T.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : Algebra K Γ(X, T.1) := (openScalars g T.1).toAlgebra
  let : IsScalarTower K Γ(X, U.1) Γ(X, T.1) :=
    IsScalarTower.of_algebraMap_eq' (openScalars_restrict g (X.basicOpen_le f)).symm
  let : IsLocalization.Away f Γ(X, T.1) := U.2.isLocalization_basicOpen f
  let ρ := (IsLocalization.algEquiv (Submonoid.powers f)
    (Localization.Away f) Γ(X, T.1)).restrictScalars K
  have het' := etale_aeval_equiv ρ _ het
  let φT := r'.comp φU
  have hφU := restrict_projective_factor h U V e i φ hφ
  refine ⟨{ U := T
            coord := i
            nonempty := ⟨⟨x, hxf⟩⟩
            φ := φT
            factor := restrict_projective_factor h T U (X.basicOpen_le f) i φU hφU
            κ := κ
            finite := hκ
            a := a
            card := hcard
            etale := ?_ }, hxf,
      (X.basicOpen_le f).trans (hUW.trans inf_le_left), rfl⟩
  convert het' using 1
  all_goals try with_reducible_and_instances rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c) =
      MvPolynomial.aeval _ (MvPolynomial.C c)
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.aeval_C]
    rfl
  · intro k
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X k) =
      MvPolynomial.aeval _ (MvPolynomial.X k)
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X]
    change -r' (φU (chartCoordinate i (a k).1)) =
      ρ (algebraMap Γ(X, U.1) (Localization.Away f) (-φU (chartCoordinate i (a k).1)))
    rw [← map_neg]
    exact ((IsLocalization.algEquiv (Submonoid.powers f)
      (Localization.Away f) Γ(X, T.1)).commutes
      (-φU (chartCoordinate i (a k).1))).symm

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FramedMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

@[reassoc]
theorem framedSectionsMorphism_over :
    framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover U hc).hom_ext
  intro i
  change ι at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [← Category.assoc, framedSectionsMorphism_local, coordinatesMap_over,
    ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

instance framedSectionsMorphism_proper
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (framedSectionsMorphism k s U hc e a hnorm) := by
  have : IsProper (framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase) := by
    rw [framedSectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_EtaleRegularPair
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

lemma sectionsMorphism_coordinate_preimage {K σ : Type} [Field K] [Fintype σ]
    {X : Scheme} {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : X.affineOpens) (i j : Option σ)
    (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X i)
        (poly_X_mem i) (by decide) = U.2.fromSpec ≫ sectionsMorphism k s hs) :
    U.2.fromSpec ⁻¹ᵁ SectionOpens.isoOpen (s j) =
      PrimeSpectrum.basicOpen (φ (chartCoordinate i j)) := by
  classical
  have h := hyperplane_affine_preimage (sectionsMorphism k s hs) U i φ hφ (Pi.single j 1)
  rw [linearEquation_single, MvPolynomial.C_1, one_mul, sectionsMorphism_preimage] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp [Pi.single_apply]

lemma chart_coordinate_basicOpen_le {K σ : Type} [Field K] [Fintype σ]
    {X : Scheme} {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : X.affineOpens) (i j : Option σ)
    (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X i)
        (poly_X_mem i) (by decide) = U.2.fromSpec ≫ sectionsMorphism k s hs) :
    X.basicOpen (φ (chartCoordinate i j)) ≤ SectionOpens.isoOpen (s j) := by
  intro x hx
  have hxU := (X.basicOpen_le (φ (chartCoordinate i j))) hx
  obtain ⟨p, rfl⟩ := (U.2.range_fromSpec ▸ hxU : x ∈ Set.range U.2.fromSpec)
  have hp : p ∈ PrimeSpectrum.basicOpen (φ (chartCoordinate i j)) := by
    rwa [← U.2.fromSpec_preimage_basicOpen]
  rwa [← sectionsMorphism_coordinate_preimage k s hs U i j φ hφ] at hp

end
end MaximalSeshadri.ProjectiveBertini
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_GlobalIntegralQuartic
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.Hartogs
open MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

lemma center_mem_distinguished {σ : Type} {X : Scheme} {M : X.Modules}
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (p : X) (hp : p ∉ centeredOpen s) : p ∈ SectionOpens.isoOpen (s none) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hs.ge (Set.mem_univ p))
  cases i with
  | none => exact hi
  | some i => exact (hp ((le_iSup (fun j => SectionOpens.isoOpen (s (some j))) i) hi)).elim

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_CenteredJetChart
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] {X : Scheme} {M : X.Modules}

lemma affineSectionRatios_none (s : Option σ → (O X ⟶ M))
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none)) :
    affineSectionRatios s U hU none = 1 := by
  simp only [affineSectionRatios, sectionFrameOn_normalized, map_one]

lemma sectionsMorphism_affine_ratios (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none))
    (φ : PolyChart (R := K) (none : Option σ) →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X none) (poly_X_mem none) (by decide) =
        U.2.fromSpec ≫ sectionsMorphism k s hs) :
    (∀ j, φ (chartCoordinate none j) = affineSectionRatios s U hU j) ∧
      ∀ c, φ (chartConstants none c) =
        U.1.topIso.hom (U.1.ι.appTop (k c)) := by
  let a := affineSectionRatios s U hU
  let kU : K →+* Γ(X, U.1) := U.1.topIso.hom.hom.comp (U.1.ι.appTop.hom.comp k)
  have hai : a none = 1 := affineSectionRatios_none s U hU
  have hφ' : φ = evalAway (MvPolynomial.eval₂Hom kU a) (MvPolynomial.X none)
      (by simpa only [MvPolynomial.eval₂Hom_X', hai] using
        (isUnit_one : IsUnit (1 : Γ(X, U.1)))) := by
    apply_fun CommRingCat.ofHom
    · apply Spec.map_injective
      rw [← cancel_mono (Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X none)
        (poly_X_mem none) (by decide))]
      rw [hφ, ← U.2.isoSpec_inv_ι, Category.assoc, sectionsMorphism_on k s hs none U.1 hU,
        affine_coordinates_factor]
      rfl
    · exact fun _ _ hh => congrArg CommRingCat.Hom.hom hh
  constructor
  · intro j
    rw [hφ']
    exact evalAway_coordinate kU a none hai j
  · intro c
    rw [hφ']
    exact RingHom.congr_fun (evalAway_constants kU a none hai) c

lemma etale_reindex {A ι ι' : Type} [CommRing A] (k : K →+* A)
    (v : ι → A) (e : ι' ≃ ι) (hv : (MvPolynomial.eval₂Hom k v).Etale) :
    (MvPolynomial.eval₂Hom k (v ∘ e)).Etale := by
  have h := RingHom.Etale.respectsIso.2 (MvPolynomial.eval₂Hom k v)
    (MvPolynomial.renameEquiv K e).toRingEquiv hv
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro i; simp

lemma cast_chart_factor (h : X ⟶ Proj (PolyGrade K (Option σ))) (U : X.affineOpens)
    {i j : Option σ} (hij : i = j) (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h) :
    Spec.map (CommRingCat.ofHom (hij ▸ φ)) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X j) (poly_X_mem j) (by decide) =
        U.2.fromSpec ≫ h := by
  cases hij
  exact hφ

lemma cast_chart_coordinate (U : X.affineOpens)
    {i j : Option σ} (hij : i = j) (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (l : Option σ) : φ (chartCoordinate i l) = (hij ▸ φ) (chartCoordinate j l) := by
  cases hij
  rfl

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_PolynomialJets
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.AlgebraicJets

noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

lemma jetAugment_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (jetAugment (σ := σ) (R := R) n hn) :=
  fun c => ⟨algebraMap R _ c, by simp⟩

lemma jetAugment_ker (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := R) n hn) =
      (idealOfVars σ R).map (Ideal.Quotient.mk ((idealOfVars σ R) ^ n)) := by
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingHom.mem_ker, jetAugment_mk,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · intro h
    exact ⟨p, by rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker], rfl⟩
  · rintro ⟨f, hf, hfp⟩
    have hd : f - p ∈ (idealOfVars σ R) ^ n := Ideal.Quotient.eq.mp hfp
    have hd' := (mem_pow_idealOfVars_iff' n (f - p)).mp hd 0 (by simpa using hn)
    have hf' : constantCoeff f = 0 := by
      rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker] at hf
    change constantCoeff (f - p) = 0 at hd'
    simpa [map_sub, hf'] using hd'

lemma jetAugment_ker_nilpotent (n : ℕ) (hn : 0 < n) :
    IsNilpotent (RingHom.ker (jetAugment (σ := σ) (R := R) n hn)) := by
  refine ⟨n, ?_⟩
  rw [jetAugment_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

end

noncomputable section
open MvPolynomial

variable {σ F S B : Type*} [CommRing F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma exists_lift_with_coordinates [CommRing B] [Algebra F B]
    [Algebra.FormallySmooth (MvPolynomial σ F) S]
    (β : MvPolynomial σ F →ₐ[F] B) (α : B →ₐ[F] S)
    (hαβ : α.comp β = IsScalarTower.toAlgHom F (MvPolynomial σ F) S)
    (hα : Function.Surjective α) (hnil : IsNilpotent (RingHom.ker α)) :
    ∃ τ : S →ₐ[F] B, α.comp τ = AlgHom.id F S ∧
      τ.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) = β := by
  let : Algebra (MvPolynomial σ F) B := β.toRingHom.toAlgebra
  let : IsScalarTower F (MvPolynomial σ F) B :=
    IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
  let ap : B →ₐ[MvPolynomial σ F] S :=
    { α.toRingHom with
      commutes' := fun p => AlgHom.congr_fun hαβ p }
  let τ := Algebra.FormallySmooth.liftOfSurjective
    (AlgHom.id (MvPolynomial σ F) S) ap hα hnil
  have hτ := Algebra.FormallySmooth.comp_liftOfSurjective
    (AlgHom.id (MvPolynomial σ F) S) ap hα hnil
  refine ⟨τ.restrictScalars F, ?_, ?_⟩
  · ext s
    exact AlgHom.congr_fun hτ s
  · ext i
    exact τ.commutes (X i)

theorem exists_regular_taylor [Algebra.FormallySmooth (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) :
    ∃ τ : S →ₐ[F] JetAlgebra σ S n,
      (∀ s, jetAugment n hn (τ s) = s) ∧
      (∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
        algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
          Ideal.Quotient.mk _ (X i)) := by
  let T := JetAlgebra σ S n
  let x : σ → S := fun i => algebraMap (MvPolynomial σ F) S (X i)
  let β : MvPolynomial σ F →ₐ[F] T :=
    aeval (fun i => algebraMap S T (x i) + Ideal.Quotient.mk _ (X i))
  let α := (jetAugment (σ := σ) (R := S) n hn).restrictScalars F
  have hαβ : α.comp β = IsScalarTower.toAlgHom F (MvPolynomial σ F) S := by
    ext i
    change jetAugment n hn (β (X i)) = x i
    simp only [β, aeval_X, map_add, jetAugment_mk, constantCoeff_X, add_zero]
    exact (jetAugment (σ := σ) (R := S) n hn).commutes (x i)
  obtain ⟨τ, hτ, hcoord⟩ := exists_lift_with_coordinates β α hαβ
    (jetAugment_surjective n hn) (jetAugment_ker_nilpotent n hn)
  refine ⟨τ, fun s => AlgHom.congr_fun hτ s, ?_⟩
  intro i
  have hi := AlgHom.congr_fun hcoord (X i)
  exact hi.trans (aeval_X _ _)

end

noncomputable section
open MvPolynomial

variable {σ F R S : Type*} [CommRing F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S]

lemma jetAugment_map (φ : R →ₐ[F] S) (n : ℕ) (hn : 0 < n)
    (z : JetAlgebra σ R n) :
    jetAugment n hn (mapJetAlgebra φ n z) = φ (jetAugment n hn z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp [MvPolynomial.constantCoeff_map]

lemma jetAugment_ker_pow (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := S) n hn) ^ n = 0 := by
  rw [jetAugment_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_FormalEtale
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma quotient_factor_pow_ker_nilpotent (I : Ideal R) (n : ℕ) (hn : 0 < n) :
    IsNilpotent (RingHom.ker
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne') : R ⧸ I ^ n →ₐ[R] R ⧸ I)) := by
  refine ⟨n, ?_⟩
  change RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn.ne')) ^ n = 0
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

theorem quotientBaseMap_pow_bijective [Algebra.FormallyEtale R S]
    (I : Ideal R) (hI : Function.Bijective (quotientBaseMap (S := S) I))
    (n : ℕ) : Function.Bijective (quotientBaseMap (S := S) (I ^ n)) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hR : I ^ 0 = (⊤ : Ideal R) := by simp
    have hS : (I ^ 0).map (algebraMap R S) = (⊤ : Ideal S) := by
      rw [hR, Ideal.map_top]
    let : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr hR
    let : Subsingleton (S ⧸ (I ^ 0).map (algebraMap R S)) :=
      Ideal.Quotient.subsingleton_iff.mpr hS
    exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  let J := I.map (algebraMap R S)
  let mapn := quotientBaseMap (S := S) (I ^ n)
  let e : (R ⧸ I) ≃ₐ[R] (S ⧸ J) := AlgEquiv.ofBijective (quotientBaseMap I) hI
  let qR : R ⧸ I ^ n →ₐ[R] R ⧸ I := Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne')
  let qS : S ⧸ (I ^ n).map (algebraMap R S) →ₐ[R] S ⧸ J :=
    Ideal.Quotient.factorₐ R (Ideal.map_mono (Ideal.pow_le_self hn.ne'))
  have hqR : Function.Surjective qR := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk (I ^ n) x, rfl⟩
  have hnR : IsNilpotent (RingHom.ker qR) := quotient_factor_pow_ker_nilpotent I n hn
  have hnS : IsNilpotent (RingHom.ker qS) := by
    refine ⟨n, ?_⟩
    change RingHom.ker (Ideal.Quotient.factor
      (Ideal.map_mono (f := algebraMap R S) (Ideal.pow_le_self (I := I) hn.ne'))) ^ n = 0
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  let f : S →ₐ[R] R ⧸ I := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
  let g : S →ₐ[R] R ⧸ I ^ n := Algebra.FormallySmooth.liftOfSurjective f qR hqR hnR
  have hg : qR.comp g = f := Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have hker : (I ^ n).map (algebraMap R S) ≤ RingHom.ker g := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change g (algebraMap R S x) = 0
    rw [g.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let inv : S ⧸ (I ^ n).map (algebraMap R S) →ₐ[R] R ⧸ I ^ n :=
    Ideal.Quotient.liftₐ _ g hker
  have hleft : inv.comp mapn = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext
    ext
  have hmod : qS.comp (mapn.comp g) = qS.comp (Ideal.Quotient.mkₐ R _) := by
    ext x
    have hx := AlgHom.congr_fun hg x
    apply e.symm.injective
    change e.symm (qS (mapn (g x))) = e.symm (Ideal.Quotient.mk J x)
    have hcompat (y : R ⧸ I ^ n) : e.symm (qS (mapn y)) = qR y := by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change e.symm (e (Ideal.Quotient.mk I y)) = Ideal.Quotient.mk I y
      exact e.symm_apply_apply _
    rw [hcompat]
    exact hx
  have hright' : mapn.comp g = Ideal.Quotient.mkₐ R _ :=
    Algebra.FormallyUnramified.lift_unique' qS hnS _ _ hmod
  have hright : mapn.comp inv = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext
    exact hright'
  exact ⟨fun x y h => by
    change mapn x = mapn y at h
    calc
      x = inv (mapn x) := (AlgHom.congr_fun hleft x).symm
      _ = inv (mapn y) := congrArg inv h
      _ = y := AlgHom.congr_fun hleft y,
    fun y => ⟨inv y, AlgHom.congr_fun hright y⟩⟩

end

noncomputable section
open IsLocalRing

variable {F R S : Type*} [Field F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S] [Algebra R S] [IsScalarTower F R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

lemma quotientBaseMap_maximal_bijective
    (hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (ρ : S →ₐ[F] F) :
    Function.Bijective (quotientBaseMap (S := S) (maximalIdeal R)) := by
  have hρ : Function.Surjective ρ := fun c => ⟨algebraMap F S c, by simp⟩
  have hker : RingHom.ker ρ = maximalIdeal S :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ρ hρ)
  constructor
  · intro x y h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.mpr
    have hmem : algebraMap R S (x - y) ∈ maximalIdeal S := by
      rw [← hmax]
      have hh := Ideal.Quotient.eq.mp h
      change algebraMap R S x - algebraMap R S y ∈ _ at hh
      simpa only [map_sub] using hh
    have hc : x - y ∈ (maximalIdeal S).comap (algebraMap R S) := hmem
    rwa [maximalIdeal_comap] at hc
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk _ (algebraMap F R (ρ y)), ?_⟩
    apply Ideal.Quotient.eq.mpr
    rw [hmax, ← hker]
    change ρ (algebraMap R S (algebraMap F R (ρ y)) - y) = 0
    rw [← IsScalarTower.algebraMap_apply F R S]
    simp

theorem local_etale_jet_equiv [Algebra.EssFiniteType R S]
    [Algebra.FormallyEtale R S] (ρ : S →ₐ[F] F) (n : ℕ) :
    Nonempty ((R ⧸ (maximalIdeal R) ^ n) ≃ₐ[R]
      (S ⧸ (maximalIdeal S) ^ n)) := by
  have hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hbij := quotientBaseMap_pow_bijective (maximalIdeal R)
    (quotientBaseMap_maximal_bijective hmax ρ) n
  have heq : ((maximalIdeal R) ^ n).map (algebraMap R S) = (maximalIdeal S) ^ n := by
    rw [Ideal.map_pow, hmax]
  exact ⟨(AlgEquiv.ofBijective _ hbij).trans (Ideal.quotientEquivAlgOfEq R heq)⟩

end

noncomputable section
open IsLocalRing

variable {F R S : Type*} [Field F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S] [Algebra R S] [IsScalarTower F R S]

theorem etale_rational_jet_equiv [Algebra.EssFiniteType R S]
    [Algebra.FormallyEtale R S] (ρ : S →ₐ[F] F) (n : ℕ) :
    Nonempty ((R ⧸ ((RingHom.ker ρ).under R) ^ n) ≃ₐ[F]
      (S ⧸ (RingHom.ker ρ) ^ n)) := by
  let q := RingHom.ker ρ
  let p := q.under R
  have hρ : Function.Surjective ρ := fun c => ⟨algebraMap F S c, by simp⟩
  let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hρ
  have hp : p = RingHom.ker (ρ.comp (IsScalarTower.toAlgHom F R S)) := rfl
  let : p.IsMaximal := by
    rw [hp]
    exact RingHom.ker_isMaximal_of_surjective _
      (fun c => ⟨algebraMap F R c, by simp⟩)
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyEtale R Sq := Algebra.FormallyEtale.comp R S Sq
  let : Algebra.FormallyEtale Rp Sq := Algebra.FormallyEtale.of_restrictScalars (R := R)
  obtain ⟨e⟩ := local_etale_jet_equiv (R := Rp) (S := Sq) (rationalLocalMap ρ) n
  exact ⟨((IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rp n).restrictScalars F).trans
    ((e.restrictScalars F).trans
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow q Sq n).restrictScalars F).symm)⟩

end

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Field F] [CommRing S] [Algebra F S]

lemma specializeTaylor_augment (n : ℕ) (hn : 0 < n)
    (τ : S →ₐ[F] JetAlgebra σ S n) (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (ρ : S →ₐ[F] F) (s : S) :
    jetAugment n hn (specializeTaylor n τ ρ s) = ρ s := by
  rw [specializeTaylor, AlgHom.comp_apply, jetAugment_map, hτ]

lemma specializeTaylor_ker_le (n : ℕ) (hn : 0 < n)
    (τ : S →ₐ[F] JetAlgebra σ S n) (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (ρ : S →ₐ[F] F) :
    (RingHom.ker ρ)^n ≤ RingHom.ker (specializeTaylor n τ ρ) := by
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
  apply le_antisymm _ bot_le
  calc
    ((RingHom.ker ρ).map (specializeTaylor n τ ρ))^n ≤
        (RingHom.ker (jetAugment (σ := σ) (R := F) n hn))^n := by
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      change jetAugment n hn (specializeTaylor n τ ρ s) = 0
      rw [specializeTaylor_augment n hn τ hτ]
      exact hs
    _ = ⊥ := jetAugment_ker_pow n hn

variable [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma specializeTaylor_coordinate (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) :
    (specializeTaylor n τ ρ).comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) =
      (Ideal.Quotient.mkₐ F _).comp (polynomialTranslate
        (fun i => ρ (algebraMap (MvPolynomial σ F) S (X i)))).toAlgHom := by
  ext i
  change mapJetAlgebra ρ n (τ (algebraMap (MvPolynomial σ F) S (X i))) = _
  rw [hcoord, map_add]
  change Ideal.Quotient.mk _ (MvPolynomial.map ρ.toRingHom
    (C (algebraMap (MvPolynomial σ F) S (X i)))) +
    Ideal.Quotient.mk _ (MvPolynomial.map ρ.toRingHom (X i)) = _
  simp [polynomialTranslate, add_comm]

lemma specializeTaylor_surjective (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) :
    Function.Surjective (specializeTaylor n τ ρ) := by
  have h := specializeTaylor_coordinate n τ hcoord ρ
  have hs : Function.Surjective ((specializeTaylor n τ ρ).comp
      (IsScalarTower.toAlgHom F (MvPolynomial σ F) S)) := by
    rw [h]
    exact Ideal.Quotient.mk_surjective.comp (polynomialTranslate _).surjective
  exact Function.Surjective.of_comp hs

theorem regularTaylor_detects_ideal_power [Finite σ] [Algebra.FormallyEtale (MvPolynomial σ F) S]
    [Algebra.EssFiniteType (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) :
    RingHom.ker (specializeTaylor n τ ρ) = (RingHom.ker ρ)^n := by
  classical
  let I := (RingHom.ker ρ)^n
  let ψ : (S ⧸ I) →ₐ[F] JetAlgebra σ F n :=
    Ideal.Quotient.liftₐ I (specializeTaylor n τ ρ)
      (specializeTaylor_ker_le n hn τ hτ ρ)
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨s, hs⟩ := specializeTaylor_surjective n τ hcoord ρ y
    exact ⟨Ideal.Quotient.mk I s, hs⟩
  let x : σ → F := fun i => ρ (algebraMap (MvPolynomial σ F) S (X i))
  have hres : (RingHom.ker ρ).under (MvPolynomial σ F) = RingHom.ker (eval x) := by
    have heq : ρ.toRingHom.comp (algebraMap (MvPolynomial σ F) S) = eval x := by
      apply ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, eval_C]
        change ρ (algebraMap (MvPolynomial σ F) S (algebraMap F (MvPolynomial σ F) c)) = c
        rw [← IsScalarTower.algebraMap_apply F (MvPolynomial σ F) S]
        exact ρ.commutes c
      · intro i
        exact (eval_X (f := x) i).symm
    change RingHom.ker (ρ.toRingHom.comp (algebraMap (MvPolynomial σ F) S)) = _
    rw [heq]
  obtain ⟨e⟩ := etale_rational_jet_equiv (R := MvPolynomial σ F) ρ n
  let e' : (S ⧸ I) ≃ₗ[F] (JetIndex σ n → F) :=
    e.symm.toLinearEquiv.trans
      (((Ideal.quotientEquivAlgOfEq F (congrArg (fun J => J ^ n) hres)).toLinearEquiv).trans
        (polynomialJetEquivAt x n))
  let e'' : JetAlgebra σ F n ≃ₗ[F] (JetIndex σ n → F) := polynomialJetEquiv n
  let : FiniteDimensional F (JetIndex σ n → F) := Module.Finite.pi
  let : FiniteDimensional F (S ⧸ I) := Module.Finite.equiv e'.symm
  let : FiniteDimensional F (JetAlgebra σ F n) := Module.Finite.equiv e''.symm
  have hinj : Function.Injective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (e'.finrank_eq.trans e''.finrank_eq.symm) (f := ψ.toLinearMap)).mpr hsurj
  apply le_antisymm _ (specializeTaylor_ker_le n hn τ hτ ρ)
  intro s hs
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hinj
  change specializeTaylor n τ ρ s = ψ 0
  rw [map_zero]
  exact hs

end

end MaximalSeshadri.AlgebraicJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_QuadraticJets
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets MaximalSeshadri.Projective

variable {K A σ : Type} [Field K] [CommRing A] [Algebra K A] [Fintype σ]

omit [Fintype σ] in
theorem exists_quadratic_jet_of_etale (a : Option σ → A) (ρ : A →ₐ[K] K)
    (ha : ∀ i : σ, ρ (a (some i)) = 0) (i : Fin 2 → σ)
    (het : (eval₂Hom (algebraMap K A) (fun j => -a (some (i j)))).Etale) :
    ∃ τ : A →ₐ[K] JetAlgebra (Fin 2) K 3,
      RingHom.ker τ = (RingHom.ker ρ)^3 ∧
      (∀ f : A, jetAugment 3 (by decide) (τ f) = ρ f) ∧
      ∀ j : Fin 2, τ (a (some (i j))) = -Ideal.Quotient.mk _ (X j) := by
  let : Algebra (MvPolynomial (Fin 2) K) A :=
    (eval₂Hom (algebraMap K A) (fun j => -a (some (i j)))).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) A :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (eval₂Hom_C (algebraMap K A) _ c).symm)
  let : Algebra.Etale (MvPolynomial (Fin 2) K) A := het
  obtain ⟨τ, hτ, hc⟩ := exists_regular_taylor (σ := Fin 2) (F := K) (S := A) 3 (by decide)
  refine ⟨specializeTaylor 3 τ ρ,
    regularTaylor_detects_ideal_power 3 (by decide) τ hτ hc ρ,
    specializeTaylor_augment 3 (by decide) τ hτ ρ, ?_⟩
  intro j
  have hh := DFunLike.congr_fun (specializeTaylor_coordinate 3 τ hc ρ) (X j)
  change specializeTaylor 3 τ ρ ((algebraMap (MvPolynomial (Fin 2) K) A) (X j)) =
    Ideal.Quotient.mk _ (aeval (fun b => X b + C
      (ρ ((algebraMap (MvPolynomial (Fin 2) K) A) (X b)))) (X j)) at hh
  simp only [aeval_X, RingHom.algebraMap_toAlgebra, eval₂Hom_X', map_neg, ha,
    neg_zero, C_0, add_zero] at hh
  simpa only [map_neg, neg_neg] using congrArg Neg.neg hh

end
end MaximalSeshadri.QuadraticJets

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_FramedNodalChart
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [IsAlgClosed K] [Fintype σ] {X : Scheme} {M : X.Modules}

omit [IsAlgClosed K] in
theorem exists_centered_etale_ratios_in_open [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : p ∉ centeredOpen s) (W : X.Opens) (hpW : p ∈ W) :
    ∃ U : X.affineOpens, p ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        ∃ i : Fin 2 → σ,
          (MvPolynomial.eval₂Hom (openScalars g U.1)
            (fun j => -affineSectionRatios s U hU (some (i j)))).Etale ∧
          (∀ j : σ, X.basicOpen (affineSectionRatios s U hU (some j)) ≤ centeredOpen s) ∧
          ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c := by
  classical
  have hp₀ := center_mem_distinguished s hs p hp
  obtain ⟨C, hpC, hCUW, hcoord⟩ := exists_etale_projective_chart g
    (sectionsMorphism k s hs) hbase none (W ⊓ SectionOpens.isoOpen (s none)) p ⟨hpW,hp₀⟩
      (by rwa [← sectionsMorphism_preimage k s hs none] at hp₀)
  have hCU := hCUW.trans inf_le_right
  let : Finite C.κ := C.finite
  let : Fintype C.κ := Fintype.ofFinite _
  have hcard : Fintype.card C.κ = 2 := by rw [← Nat.card_eq_fintype_card]; exact C.card
  let e : Fin 2 ≃ C.κ := (Fintype.equivFinOfCardEq hcard).symm
  have hi (j : Fin 2) : ∃ i : σ, (C.a (e j)).1 = some i :=
    Option.ne_none_iff_exists'.mp (by simpa only [hcoord] using (C.a (e j)).2)
  let i : Fin 2 → σ := fun j => (hi j).choose
  have his (j : Fin 2) : (C.a (e j)).1 = some (i j) := (hi j).choose_spec
  let φ : PolyChart (R := K) (none : Option σ) →+* Γ(X, C.U.1) := hcoord ▸ C.φ
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X none) (poly_X_mem none) (by decide) =
        C.U.2.fromSpec ≫ sectionsMorphism k s hs := by
    exact cast_chart_factor (sectionsMorphism k s hs) C.U hcoord C.φ C.factor
  have heq := sectionsMorphism_affine_ratios k s hs C.U hCU φ hφ
  refine ⟨C.U, hpC, hCUW.trans inf_le_left, hCU, i, ?_, ?_, ?_⟩
  · have h := etale_reindex (openScalars g C.U.1)
      (fun j => -C.φ (chartCoordinate C.coord (C.a j).1)) e C.etale
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext j
    have hc : C.φ (chartCoordinate C.coord (C.a (e j)).1) =
        φ (chartCoordinate none (some (i j))) := by
      rw [his]
      exact cast_chart_coordinate C.U hcoord C.φ _
    rw [Function.comp_apply, hc, heq.1]
  · intro j
    rw [← heq.1]
    exact (chart_coordinate_basicOpen_le k s hs C.U none (some j) φ hφ).trans
      (le_iSup (fun j => SectionOpens.isoOpen (s (some j))) j)
  · intro c
    rw [← heq.2]
    let : Algebra K Γ(X, C.U.1) := (openScalars g C.U.1).toAlgebra
    exact projective_affine_constants (sectionsMorphism k s hs) g hbase
      C.U (_root_.OAI.MaximalSeshadri.ProjectiveBertini.spec_openScalars g C.U) none φ hφ c

theorem exists_centered_rational_jet_in_open_s01_oai [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : p ∉ centeredOpen s) (W : X.Opens) (hpW : p ∈ W) :
    ∃ U : X.affineOpens, p ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
        ∃ i : Fin 2 → σ, ∃ ρ : Γ(X, U.1) →ₐ[K] K,
          ∃ τ : Γ(X, U.1) →ₐ[K] JetAlgebra (Fin 2) K 3,
            (∀ j : σ, ρ (affineSectionRatios s U hU (some j)) = 0) ∧
            RingHom.ker τ = (RingHom.ker ρ)^3 ∧
            (∀ f, jetAugment 3 (by decide) (τ f) = ρ f) ∧
            (∀ j : Fin 2, τ (affineSectionRatios s U hU (some (i j))) =
              -Ideal.Quotient.mk _ (MvPolynomial.X j)) ∧
            (MvPolynomial.eval₂Hom (openScalars g U.1)
              (fun j => -affineSectionRatios s U hU (some (i j)))).Etale ∧
            ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c := by
  obtain ⟨U, hpU, hUW, hU, i, hi, hb, hk⟩ := exists_centered_etale_ratios_in_open g k s hs hbase p hp W hpW
  let : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
  let a := affineSectionRatios s U hU
  let : Algebra (MvPolynomial (Fin 2) K) Γ(X, U.1) :=
    (eval₂Hom (openScalars g U.1) (fun j => -a (some (i j)))).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) Γ(X, U.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (eval₂Hom_C (openScalars g U.1) _ c).symm)
  let : Algebra.Etale (MvPolynomial (Fin 2) K) Γ(X, U.1) := hi
  let : Algebra.FiniteType K Γ(X, U.1) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (MvPolynomial (Fin 2) K))
    (inferInstance : Algebra.FiniteType (MvPolynomial (Fin 2) K) Γ(X, U.1))
  let x : PrimeSpectrum Γ(X, U.1) := U.2.isoSpec.hom ⟨p, hpU⟩
  let : x.asIdeal.IsPrime := x.isPrime
  have hpx : U.2.fromSpec x = p := by
    change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨p, hpU⟩ = p
    rw [U.2.isoSpec_hom_fromSpec]
    rfl
  have ham (j : σ) : a (some j) ∈ x.asIdeal := by
    by_contra h
    have hx : x ∈ PrimeSpectrum.basicOpen (a (some j)) := h
    rw [← U.2.fromSpec_preimage_basicOpen] at hx
    change U.2.fromSpec x ∈ X.basicOpen (a (some j)) at hx
    rw [hpx] at hx
    exact hp (hb j hx)
  obtain ⟨ρ₀⟩ := exists_point_finite_type (K := K) (R := Γ(X, U.1) ⧸ x.asIdeal)
  let ρ : Γ(X, U.1) →ₐ[K] K := ρ₀.comp (Ideal.Quotient.mkₐ K x.asIdeal)
  have ha (j : σ) : ρ (a (some j)) = 0 := by
    change ρ₀ (Ideal.Quotient.mk _ (a (some j))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (ham j), map_zero]
  obtain ⟨τ, hτ, haug, hc⟩ := exists_quadratic_jet_of_etale a ρ ha i hi
  exact ⟨U, hpU, hUW, hU, i, ρ, τ, ha, hτ, haug, hc, hi, hk⟩

end
end MaximalSeshadri.Projective

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open_s01_oai := @OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open_s01_oai
