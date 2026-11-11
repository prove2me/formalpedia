-- Prove2me | solution 1 for OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:22:06.939205+00:00
-- url     : https://prove2.me/submissions/c71f36f6-7661-4ee9-a599-24c17686eb50

import Mathlib
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_BertiniIntegral_smooth_integral_hyperplane_of_etale_atlas_with_equations_s01

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

omit [Fintype σ] in
lemma chartCoordinate_self (i : σ) : chartCoordinate (R := R) i i = 1 := by
  apply HomogeneousLocalization.val_injective _
  rw [chart_val_coordinate, HomogeneousLocalization.val_one]
  exact IsLocalization.Away.mul_invSelf (X i)

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

lemma linearEquation_ne_zero {K σ : Type} [Field K] [Fintype σ]
    (v : σ → K) (i : σ) (hi : v i ≠ 0) : linearEquation v ≠ 0 := by
  classical
  intro h
  have := congrArg (MvPolynomial.aeval (Pi.single i (1 : K))) h
  simp [linearEquation, Pi.single_apply, Finset.sum_ite_eq', hi] at this

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

lemma projective_factor_open (h : X ⟶ Proj (PolyGrade K σ)) (U : X.affineOpens)
    (i : σ) (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h) :
    U.1 ≤ h ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) := by
  intro x hx
  have hx' : x ∈ (U.1 : Set X) := hx
  rw [← U.2.range_fromSpec] at hx'
  obtain ⟨y, rfl⟩ := hx'
  change h (U.2.fromSpec y) ∈ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)
  rw [← Scheme.Hom.comp_apply, ← hφ]
  have hh : (Spec.map (CommRingCat.ofHom φ) ≫
    Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)) y ∈
    (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)).opensRange :=
      ⟨_, rfl⟩
  rwa [Proj.opensRange_awayι] at hh

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

theorem sectionsMorphism_affine_equation [Fintype σ] {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : X.affineOpens) (i : σ) (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ sectionsMorphism k s hcover) :
    ∃ e : M.restrict U.1.ι ≅ O U.1.toScheme, ∀ t : σ → K,
      U.1.topIso.hom (coefficient e (restrictSection U.1.ι (sectionCombination k s t))) =
        ∑ j, φ (chartConstants i (t j)) * φ (chartCoordinate i j) := by
  have hU := projective_factor_open (sectionsMorphism k s hcover) U i φ hφ
  rw [sectionsMorphism_preimage] at hU
  let e := sectionFrameOn (s i) U.1 hU
  let a (j : σ) : Γ(X, U.1) :=
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι (s j)))
  let kU : K →+* Γ(X, U.1) := U.1.topIso.hom.hom.comp (U.1.ι.appTop.hom.comp k)
  have hai : a i = 1 := by simp only [a, e, sectionFrameOn_normalized, map_one]
  have hφ' : φ = evalAway (MvPolynomial.eval₂Hom kU a) (MvPolynomial.X i)
      (by simpa only [MvPolynomial.eval₂Hom_X', hai] using
        (isUnit_one : IsUnit (1 : Γ(X, U.1)))) := by
    apply_fun CommRingCat.ofHom
    · apply Spec.map_injective
      rw [← cancel_mono (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i)
        (poly_X_mem i) (by decide))]
      rw [hφ, ← U.2.isoSpec_inv_ι, Category.assoc, sectionsMorphism_on k s hcover i U.1 hU,
        affine_coordinates_factor]
      rfl
    · exact fun _ _ hh => congrArg CommRingCat.Hom.hom hh
  have hcoord (j : σ) : φ (chartCoordinate i j) = a j := by
    rw [hφ']
    exact evalAway_coordinate kU a i hai j
  have hconst (c : K) : φ (chartConstants i c) = kU c := by
    rw [hφ']
    exact RingHom.congr_fun (evalAway_constants kU a i hai) c
  refine ⟨e, fun t => ?_⟩
  simp only [sectionCombination, restrictSection_sum, coefficient_sum, map_sum, hconst, hcoord]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficient_restrict_scalar_comp, map_mul]
  rfl

end
end MaximalSeshadri.Projective
end


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
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_LocalCoordinateAtlas
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
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
open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open MaximalSeshadri.Projective MaximalSeshadri.AlgebraicJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

theorem etale_chart_of_affine_coordinates [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ))
    (hbase : h ≫ projectiveToSpec = g)
    (i : σ) (V : X.affineOpens)
    (φ : PolyChart (R := K) i →+* Γ(X, V.1)) (hsurj : Function.Surjective φ)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        V.2.fromSpec ≫ h)
    (W : X.Opens) (x : X) (hxW : x ∈ W) (hxV : x ∈ V.1) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W ∧ C.coord = i := by
  classical
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

theorem finite_atlas_of_local_coordinates [IsIntegral X] [CompactSpace X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ))
    (hbase : h ≫ projectiveToSpec = g)
    (hlocal : ∀ x : X, ∃ i : σ, ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ φ : PolyChart (R := K) i →+* Γ(X, V.1), Function.Surjective φ ∧
        Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
            V.2.fromSpec ≫ h) :
    Nonempty (OverlappingEtaleProjectiveAtlas g h) := by
  classical
  have hchart (W : X.Opens) (x : X) (hxW : x ∈ W) :
      ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W := by
    obtain ⟨i, V, hxV, φ, hsurj, hφ⟩ := hlocal x
    obtain ⟨C, hxC, hCW, _⟩ :=
      etale_chart_of_affine_coordinates g h hbase i V φ hsurj hφ W x hxW hxV
    exact ⟨C, hxC, hCW⟩
  choose C hC using (fun x : X => hchart ⊤ x
    (show x ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((C x).U.1 : Set X))
    (fun x => (C x).U.1.isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, (hC x).1⟩)
  have hcover : ∀ x : X, ∃ j : s, x ∈ (C j.1).U.1 := by
    intro x
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨j, hj⟩, hx⟩
  let x₀ : X := Classical.arbitrary X
  obtain ⟨j₀, _⟩ := hcover x₀
  have hov (j : s) : ∃ D : EtaleProjectiveChart g h,
      D.U.1 ≤ (C j₀.1).U.1 ∧ D.U.1 ≤ (C j.1).U.1 := by
    have hne (k : s) : ((C k.1).U.1 : Set X).Nonempty :=
      Set.nonempty_coe_sort.mp (C k.1).nonempty
    obtain ⟨x, hx₀, hx⟩ := nonempty_preirreducible_inter
      (C j₀.1).U.1.isOpen (C j.1).U.1.isOpen (hne j₀) (hne j)
    obtain ⟨D, _, hD⟩ := hchart
      ((C j₀.1).U.1 ⊓ (C j.1).U.1) x ⟨hx₀, hx⟩
    exact ⟨D, hD.trans inf_le_left, hD.trans inf_le_right⟩
  choose D hD₀ hD using hov
  refine ⟨{ ι := s ⊕ s
            finite := inferInstance
            chart := Sum.elim (fun j => C j.1) D
            cover := ?_
            base := Sum.inl j₀
            overlap := fun j => Sum.inr (Sum.elim id id j)
            left := ?_
            right := ?_ }⟩
  · intro x
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨Sum.inl j, hj⟩
  · intro j
    cases j with
    | inl j => exact hD₀ j
    | inr j => exact hD₀ j
  · intro j
    cases j with
    | inl j => exact hD j
    | inr j => exact le_rfl

end
end MaximalSeshadri.ProjectiveBertini

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_LocalBertiniSection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_C _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_X _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
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

theorem exists_smooth_integral_cartier_section_of_local_coordinates_s01_oai
    {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    {n : ℕ} (X : Scheme) [IsIntegral X] [CompactSpace X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (M : X.Modules) (k : K →+* Γ(X, ⊤))
    (s : Option (Fin n) → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n))))
    (hh : h = sectionsMorphism k s hs)
    (hbase : h ≫ projectiveToSpec = g)
    (hlocal : ∀ x : X, ∃ i : Option (Fin n), ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ φ : PolyChart (R := K) i →+* Γ(X, V.1), Function.Surjective φ ∧
        Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (PolyGrade K (Option (Fin n))) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
            V.2.fromSpec ≫ h)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (projectiveHyperplane h t).subscheme ∧
      Smooth ((projectiveHyperplane h t).subschemeι ≫ g) ∧
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X, U.1),
        IsRegular r ∧ (projectiveHyperplane h t).ideal U = Ideal.span {r} ∧
        ∃ e : M.restrict U.1.ι ≅ O U.1.toScheme,
          U.1.topIso.hom (coefficient e (restrictSection U.1.ι
            (sectionCombination k s t))) = r := by
  classical
  let A := Classical.choice (finite_atlas_of_local_coordinates g h hbase hlocal)
  let C := A.chart
  let : Finite A.ι := A.finite
  let : ∀ j, Nonempty (C j).U.1 := fun j => (C j).nonempty
  let : ∀ j, IsDomain Γ(X, (C j).U.1) := fun j => inferInstance
  let : ∀ j, Algebra K Γ(X, (C j).U.1) :=
    fun j => (openScalars g (C j).U.1).toAlgebra
  let : ∀ j, Finite (C j).κ := fun j => (C j).finite
  let : ∀ j, Algebra (MvPolynomial (C j).κ K) Γ(X, (C j).U.1) :=
    fun j => (MvPolynomial.eval₂Hom (openScalars g (C j).U.1)
      (fun k => -(C j).φ (chartCoordinate (C j).coord ((C j).a k).1))).toAlgebra
  let : ∀ j, IsScalarTower K (MvPolynomial (C j).κ K) Γ(X, (C j).U.1) := by
    intro j
    apply IsScalarTower.of_algebraMap_eq'
    ext k
    exact (MvPolynomial.eval₂Hom_C _ _ k).symm
  let : ∀ j, Algebra.Etale (MvPolynomial (C j).κ K) Γ(X, (C j).U.1) :=
    fun j => (C j).etale
  let : ∀ j, Algebra.FiniteType K Γ(X, (C j).U.1) := fun j =>
    Algebra.FiniteType.trans (R := K) (S := MvPolynomial (C j).κ K)
      (A := Γ(X, (C j).U.1)) inferInstance inferInstance
  let : Fintype A.ι := Fintype.ofFinite _
  let ψ (j : A.ι) : Γ(X, (C j).U.1) →ₐ[K] K :=
    Classical.choice (exists_point_finite_type (K := K) (R := Γ(X, (C j).U.1)))
  let v (j : A.ι) (k : Option (Fin n)) : K :=
    ψ j ((C j).φ (chartCoordinate (C j).coord k))
  let P (j : A.ι) : MvPolynomial (Option (Fin n)) K := linearEquation (v j)
  have hP (j : A.ι) : P j ≠ 0 :=
    linearEquation_ne_zero (v j) (C j).coord (by
      simp [v, chartCoordinate_self])
  let Q := q * ∏ j, P j
  have hQ : Q ≠ 0 := mul_ne_zero hq (Finset.prod_ne_zero_iff.mpr (fun j _ => hP j))
  let δ (j : A.ι) : Fin n ≃ ChartVariables (C j).coord :=
    Equiv.optionSubtype (C j).coord ⟨Equiv.swap none (C j).coord, by simp⟩
  let e (j : A.ι) : Option (Fin n) ≃ Option (Fin n) :=
    ((Equiv.optionSubtype (C j).coord).symm (δ j)).1
  have hp (j : A.ι) : ∃ a b : (C j).κ, a ≠ b := by
    let : Fintype (C j).κ := Fintype.ofFinite _
    have hcard : Fintype.card (C j).κ = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact (C j).card
    let : Nontrivial (C j).κ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_pair_ne _
  choose a b hab using hp
  have hc : ∀ j, ∀ c, (C j).φ (chartConstants (C j).coord c) =
      openScalars g (C j).U.1 c := fun j =>
    projective_affine_constants h g hbase (C j).U (spec_openScalars g (C j).U)
      _ (C j).φ (C j).factor
  obtain ⟨t, ht, hI, hS, heq⟩ :=
    smooth_integral_hyperplane_of_etale_atlas_with_equations_s01 X g h hbase
    (fun j => (C j).U) A.cover (fun j => spec_openScalars g (C j).U)
    e (fun j => (C j).φ) (fun j => (C j).factor) (fun j => (C j).κ)
    (fun j => (δ j).symm ((C j).a (a j)))
    (fun j => (δ j).symm ((C j).a (b j))) a b hab
    (by
      intro j
      change -(C j).φ (chartCoordinate (C j).coord (δ j ((δ j).symm ((C j).a (a j)))).1) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.X (a j))
      rw [Equiv.apply_symm_apply, MvPolynomial.eval₂Hom_X'])
    (by
      intro j
      change -(C j).φ (chartCoordinate (C j).coord (δ j ((δ j).symm ((C j).a (b j)))).1) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.X (b j))
      rw [Equiv.apply_symm_apply, MvPolynomial.eval₂Hom_X'])
    A.base A.overlap A.left A.right Q hQ

  have htq : MvPolynomial.aeval t q ≠ 0 :=
    (mul_ne_zero_iff.mp (by simpa only [Q, map_mul] using ht)).1
  have htP (j : A.ι) : MvPolynomial.aeval t (P j) ≠ 0 := by
    have hh := (mul_ne_zero_iff.mp (by simpa only [Q, map_mul] using ht)).2
    rw [map_prod] at hh
    exact Finset.prod_ne_zero_iff.mp hh j (Finset.mem_univ j)
  refine ⟨t, htq, hI, hS, fun x => ?_⟩
  obtain ⟨j, hj⟩ := A.cover x
  let r : Γ(X, (C j).U.1) := ∑ k, (C j).φ (chartConstants (C j).coord (t k)) *
    (C j).φ (chartCoordinate (C j).coord k)
  have hψr : ψ j r = MvPolynomial.aeval t (P j) := by
    simp only [r, map_sum, map_mul, hc, P, linearEquation, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X]
    apply Finset.sum_congr rfl
    intro k hk
    have hh : ψ j (openScalars g (C j).U.1 (t k)) = t k := (ψ j).commutes _
    rw [hh, mul_comm]
    rfl
  have hr : r ≠ 0 := by
    intro hz
    apply htP j
    rw [← hψr, hz, map_zero]
  obtain ⟨e, he⟩ := sectionsMorphism_affine_equation k s hs (C j).U
    (C j).coord (C j).φ (by simpa only [← hh] using (C j).factor)
  exact ⟨(C j).U, hj, r, isRegular_iff_ne_zero.mpr hr, heq j, e, he t⟩

end
end MaximalSeshadri.ProjectiveBertini

end


end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates_s01_oai := @OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates_s01_oai
