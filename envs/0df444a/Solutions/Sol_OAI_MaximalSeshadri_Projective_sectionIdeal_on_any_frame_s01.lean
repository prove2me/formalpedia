-- Prove2me | solution 1 for OAI.MaximalSeshadri.Projective.sectionIdeal_on_any_frame_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:22:05.166426+00:00
-- url     : https://prove2.me/submissions/77998d6f-ad40-4ac9-8301-9ec4b7d5ef0d

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

end

end MaximalSeshadri.Projective


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionNaturality
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
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

variable {K σ : Type} [CommRing K] {X Y : Scheme}

lemma sectionsMorphism_frame {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (φ : Y ⟶ X) [IsOpenImmersion φ] (e : M.restrict φ ≅ O Y)
    (i : σ) (hi : coefficient e (restrictSection φ (s i)) = 1) :
    φ ≫ sectionsMorphism k s hs =
      coordinatesMap Y (φ.appTop.hom.comp k)
        (fun j => coefficient e (restrictSection φ (s j))) i hi := by
  let U := SectionOpens.isoOpen (s i)
  have hp : φ ⁻¹ᵁ U = ⊤ := by
    rw [show U = SectionOpens.isoOpen (s i) from rfl, preimage_isoOpen (s i) φ e, hi]
    exact (isUnit_iff_basicOpen_top _).mp isUnit_one
  have hr : Set.range φ ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h : y ∈ φ ⁻¹ᵁ U := by rw [hp]; trivial
    exact h
  let l := IsOpenImmersion.lift U.ι φ hr
  have hl : l ≫ U.ι = φ := IsOpenImmersion.lift_fac U.ι φ hr
  let : IsOpenImmersion l := IsOpenImmersion.of_comp l U.ι
  obtain ⟨c, hc⟩ := overlap_coefficients φ U.ι (𝟙 Y) l (by simpa using hl.symm)
    e (sectionFrame (s i))
  have hci : (c : Γ(Y, ⊤)) = 1 := by
    have h := hc (s i)
    simpa only [U, sectionFrame_normalized, map_one, hi, Scheme.Hom.id_appTop,
      CommRingCat.id_apply, mul_one] using h.symm
  have hc' (j : σ) : l.appTop (coefficient (sectionFrame (s i))
      (restrictSection U.ι (s j))) = coefficient e (restrictSection φ (s j)) := by
    simpa only [hci, Scheme.Hom.id_appTop, CommRingCat.id_apply, one_mul] using hc (s j)
  conv_lhs => rw [← hl, Category.assoc, sectionsMorphism_local, coordinatesMap_natural]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hl]
  · exact funext hc'

lemma coefficient_composite_frame {Z : Scheme} {M : X.Modules}
    (φ : Y ⟶ X) (ψ : Z ⟶ Y) [IsOpenImmersion φ] [IsOpenImmersion ψ]
    (e : (M.restrict φ).restrict ψ ≅ O Z) (s : O X ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctorComp ψ φ).app M ≪≫ e)
      (restrictSection (ψ ≫ φ) s) = coefficient e (restrictSection ψ (restrictSection φ s)) := by
  rw [coefficient_transport]
  change coefficient e (restrictSection (ψ ≫ φ) s ≫
    (Scheme.Modules.restrictFunctorComp ψ φ).hom.app M) = _
  rw [restrictSection_comp]

lemma sectionsMorphism_restrict {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (φ : Y ⟶ X) [IsOpenImmersion φ] :
    φ ≫ sectionsMorphism k s hs =
      sectionsMorphism (φ.appTop.hom.comp k) (fun i => restrictSection φ (s i))
        (restricted_sections_cover s hs φ) := by
  let t (i : σ) := restrictSection φ (s i)
  let ht := restricted_sections_cover s hs φ
  apply (Y.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (t i)) ht).hom_ext
  intro i
  change σ at i
  let U := SectionOpens.isoOpen (t i)
  let e := (Scheme.Modules.restrictFunctorComp U.ι φ).app M ≪≫ sectionFrame (t i)
  have he (j : σ) : coefficient e (restrictSection (U.ι ≫ φ) (s j)) =
      coefficient (sectionFrame (t i)) (restrictSection U.ι (t j)) :=
    coefficient_composite_frame φ U.ι (sectionFrame (t i)) (s j)
  have hi : coefficient e (restrictSection (U.ι ≫ φ) (s i)) = 1 := by
    rw [he, sectionFrame_normalized]
  change U.ι ≫ (φ ≫ sectionsMorphism k s hs) =
    U.ι ≫ sectionsMorphism (φ.appTop.hom.comp k) t ht
  rw [← Category.assoc, sectionsMorphism_frame k s hs (U.ι ≫ φ) e i hi,
    sectionsMorphism_local]
  congr 1
  exact funext he

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
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_LinearRadical
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open MvPolynomial
variable {K σ : Type*} [Field K]

theorem span_isRadical_of_totalDegree_le_one (p : MvPolynomial σ K)
    (hp : p.totalDegree ≤ 1) : (Ideal.span ({p} : Set (MvPolynomial σ K))).IsRadical := by
  by_cases h0 : p.totalDegree = 0
  · rw [(totalDegree_eq_zero_iff_eq_C (p := p)).mp h0]
    by_cases hc : p.coeff 0 = 0
    · simpa only [hc, C_0, Ideal.span_singleton_zero] using
        (Ideal.isRadical_bot : (⊥ : Ideal (MvPolynomial σ K)).IsRadical)
    · have hu : IsUnit (C (p.coeff 0) : MvPolynomial σ K) :=
        (isUnit_iff_ne_zero.mpr hc).map C
      rw [Ideal.span_singleton_eq_top.mpr hu]
      exact le_top
  · have h1 : p.totalDegree = 1 := by omega
    have hirr : Irreducible p := irreducible_of_totalDegree_eq_one h1 (by
      intro x hx
      apply isUnit_iff_ne_zero.mpr
      intro hx0
      have hp0 : p = 0 := by
        ext d
        simpa [hx0, zero_dvd_iff] using hx d
      simp [hp0] at h1)
    exact (Ideal.span_singleton_prime hirr.ne_zero).mpr
      (irreducible_iff_prime.mp hirr) |>.isRadical

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_HyperplaneIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_C _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme} {R : Type} [CommRing R]

lemma vanishingIdeal_comap_open (Z : Closeds Y) (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal (Z.preimage f.continuous) := by
  let I := (Scheme.IdealSheafData.vanishingIdeal Z).comap f
  have hs : I.support = Z.preimage f.continuous := by
    ext x
    simp only [I, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rw [← hs, Scheme.IdealSheafData.vanishingIdeal_support]
  symm
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal]
  change (I.ideal U).radical = I.ideal U
  rw [show I = (Scheme.IdealSheafData.vanishingIdeal Z).comap f from rfl,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact ((PrimeSpectrum.isRadical_vanishingIdeal _).comap _).radical

lemma specIdeal_support (I : Ideal R) :
    ((specIdeal I).support : Set (Spec (.of R))) = PrimeSpectrum.zeroLocus I := by
  rw [specIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
  congr 1
  change ((I.map (Scheme.ΓSpecIso (.of R)).inv.hom).comap
    (Scheme.ΓSpecIso (.of R)).inv.hom : Set R) = _
  rw [Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]

lemma specIdeal_radical_eq (I : Ideal R) (hI : I.IsRadical) :
    (specIdeal I).radical = specIdeal I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.radical_ideal, specIdeal_top]
  let e : R ≃+* Γ(Spec (.of R), ⊤) :=
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  change (I.map e.toRingHom).radical = I.map e.toRingHom
  have he : I.map e.toRingHom = I.comap e.symm.toRingHom := Ideal.map_comap_of_equiv e
  rw [he]
  exact (hI.comap e.symm.toRingHom).radical

lemma vanishingIdeal_open_chart (D : X.Opens) (f : Spec (.of R) ⟶ X)
    [IsOpenImmersion f] (a : R)
    (hD : f ⁻¹ᵁ D = PrimeSpectrum.basicOpen a)
    (ha : (Ideal.span ({a} : Set R)).IsRadical) :
    (Scheme.IdealSheafData.vanishingIdeal D.compl).comap f =
      specIdeal (Ideal.span {a}) := by
  rw [vanishingIdeal_comap_open]
  have hs : D.compl.preimage f.continuous = (specIdeal (Ideal.span {a})).support := by
    apply SetLike.coe_injective
    rw [specIdeal_support, PrimeSpectrum.zeroLocus_span]
    change f ⁻¹' ((D : Set X)ᶜ) = PrimeSpectrum.zeroLocus {a}
    have h := congrArg (fun U : (Spec (.of R)).Opens => (U : Set (Spec (.of R)))) hD
    change f ⁻¹' (D : Set X) = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) at h
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] at h
    rw [Set.preimage_compl, h]
    exact compl_compl _
  rw [hs, Scheme.IdealSheafData.vanishingIdeal_support, specIdeal_radical_eq _ ha]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ]

lemma chart_linear_equation_radical (t : σ → K) (i : σ) :
    (Ideal.span ({∑ j, chartConstants i (t j) * chartCoordinate i j} :
      Set (PolyChart (R := K) i))).IsRadical := by
  classical
  let a : PolyChart (R := K) i := ∑ j, chartConstants i (t j) * chartCoordinate i j
  let e := polynomialChartEquiv (R := K) i
  have hdeg : (e a).totalDegree ≤ 1 := by
    change (chartToPoly i a).totalDegree ≤ 1
    simp only [a, map_sum, map_mul, chartToPoly_constants, chartToPoly_coordinate]
    apply totalDegree_finsetSum_le
    intro j hj
    split_ifs
    · simp
    · apply (totalDegree_mul _ _).trans
      simp
  have hrad := span_isRadical_of_totalDegree_le_one (e a) hdeg
  have he : (Ideal.span ({e a} : Set (MvPolynomial (ChartVariables i) K))).comap
      e.toRingHom = Ideal.span {a} := by
    rw [← Set.image_singleton, ← Ideal.map_span]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  rw [← he]
  exact hrad.comap e.toRingHom

lemma ambientHyperplane_chart (t : σ → K) (i : σ) :
    (ambientHyperplane t).comap
      (Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide)) =
        IdealPullback.specIdeal (Ideal.span {∑ j, chartConstants i (t j) * chartCoordinate i j}) :=
  IdealPullback.vanishingIdeal_open_chart _ _ _ (hyperplane_chart_preimage t i)
    (chart_linear_equation_radical t i)

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_HyperplanePullback
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} {R : Type} [CommRing R]

lemma specIdeal_injective : Function.Injective (specIdeal (R := R)) := by
  intro I J h
  have hh := congrArg (fun A => A.ideal ⟨⊤, isAffineOpen_top (Spec (.of R))⟩) h
  simp only [specIdeal_top] at hh
  have hh' := congrArg (Ideal.map (Scheme.ΓSpecIso (.of R)).hom.hom) hh
  have he : (Scheme.ΓSpecIso (.of R)).hom.hom.comp
      (Scheme.ΓSpecIso (.of R)).inv.hom = RingHom.id R := by
    exact congrArg CommRingCat.Hom.hom (Iso.inv_hom_id (Scheme.ΓSpecIso (.of R)))
  simpa only [Ideal.map_map, he, Ideal.map_id] using hh'

lemma comap_fromSpec (I : X.IdealSheafData) (U : X.affineOpens) :
    I.comap U.2.fromSpec = specIdeal (I.ideal U) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [← U.2.isoSpec_inv_ι, Scheme.IdealSheafData.comap_comp, comap_top,
    comap_ι_top, U.2.isoSpec_inv_appTop, specIdeal_top]
  rw [Ideal.map_map]
  congr 1
  simp only [← CommRingCat.hom_comp, Iso.inv_hom_id_assoc]
  rfl

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma ambientHyperplane_comap_equation
    (h : X ⟶ Proj (PolyGrade K σ)) (v : σ → K) (U : X.affineOpens) (i : σ)
    (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h) :
    ((ambientHyperplane v).comap h).ideal U =
      Ideal.span {∑ j, φ (chartConstants i (v j)) * φ (chartCoordinate i j)} := by
  apply specIdeal_injective
  rw [← comap_fromSpec, ← Scheme.IdealSheafData.comap_comp, ← hφ,
    Scheme.IdealSheafData.comap_comp, ambientHyperplane_chart, specIdeal_comap,
    Ideal.map_span, Set.image_singleton]
  simp only [map_sum, map_mul]

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionIdeal
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
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma sectionIdeal_restrict {Y : Scheme} {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    (sectionIdeal k s hs v).comap φ = sectionIdeal (φ.appTop.hom.comp k)
      (fun i => restrictSection φ (s i)) (restricted_sections_cover s hs φ) v := by
  rw [sectionIdeal, ← Scheme.IdealSheafData.comap_comp, sectionsMorphism_restrict]
  rfl

lemma sectionIdeal_on {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (U : X.affineOpens) (i : σ)
    (hU : U.1 ≤ SectionOpens.isoOpen (s i)) :
    (sectionIdeal k s hs v).ideal U = Ideal.span
      {U.1.topIso.hom (coefficient (sectionFrameOn (s i) U.1 hU)
        (restrictSection U.1.ι (sectionCombination k s v)))} := by
  let e := sectionFrameOn (s i) U.1 hU
  let kU := U.1.topIso.hom.hom.comp (U.1.ι.appTop.hom.comp k)
  let a (j : σ) := U.1.topIso.hom (coefficient e (restrictSection U.1.ι (s j)))
  have hai : a i = 1 := by simp only [a, e, sectionFrameOn_normalized, map_one]
  let φ : PolyChart (R := K) i →+* Γ(X, U.1) :=
    evalAway (eval₂Hom kU a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X', hai] using (isUnit_one : IsUnit (1 : Γ(X, U.1))))
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ sectionsMorphism k s hs := by
    rw [← U.2.isoSpec_inv_ι, Category.assoc, sectionsMorphism_on k s hs i U.1 hU,
      affine_coordinates_factor]
    rfl
  have hcoord (j : σ) : φ (chartCoordinate i j) = a j := evalAway_coordinate kU a i hai j
  have hconst (c : K) : φ (chartConstants i c) = kU c :=
    RingHom.congr_fun (evalAway_constants kU a i hai) c
  rw [sectionIdeal, ambientHyperplane_comap_equation _ v U i φ hφ]
  congr 2
  simp only [sectionCombination, restrictSection_sum, coefficient_sum, map_sum,
    hconst, hcoord]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficient_restrict_scalar_comp, map_mul]
  rfl

lemma coefficient_span_frame {M : X.Modules} (e f : M ≅ O X) (s : O X ⟶ M)
    {R : Type} [CommRing R] (ρ : Γ(X, ⊤) →+* R) :
    Ideal.span ({ρ (coefficient e s)} : Set R) =
      Ideal.span {ρ (coefficient f s)} := by
  rw [coefficient_change e f, map_mul, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.mpr ((frameChange e f).isUnit.map ρ), Ideal.top_mul]

lemma sectionIdeal_on_frame {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (U : X.affineOpens) (i : σ)
    (hU : U.1 ≤ SectionOpens.isoOpen (s i))
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    (sectionIdeal k s hs v).ideal U = Ideal.span
      {U.1.topIso.hom (coefficient e (restrictSection U.1.ι (sectionCombination k s v)))} := by
  rw [sectionIdeal_on k s hs v U i hU]
  exact coefficient_span_frame _ e _ U.1.topIso.hom.hom

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SectionIdealExt
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type} [Field K] [Fintype σ] [Fintype τ] {X : Scheme}

lemma idealSheaf_ext_local {I J : X.IdealSheafData}
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ I.ideal U = J.ideal U) : I = J := by
  choose U hx hU using h
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U _ hU
  exact top_unique (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_PrincipalSectionIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme}

lemma restrictSection_scalar (φ : Y ⟶ X) [IsOpenImmersion φ]
    {M : X.Modules} (a : Γ(X, ⊤)) (s : O X ⟶ M) :
    restrictSection φ (scalarEnd a ≫ s) = scalarEnd (φ.appTop a) ≫ restrictSection φ s := by
  have h : restrictSection φ (scalarEnd a) ≫ (Scheme.Modules.restrictUnitIso φ).hom =
      scalarEnd (φ.appTop a) := by
    apply endValue_injective
    exact (endValue_restrict φ (scalarEnd a)).trans
      ((congrArg φ.appTop (endValue_scalarEnd a)).trans (endValue_scalarEnd _).symm)
  rw [← h]
  let restriction : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor φ
  let unitIso : restriction.obj (O X) ≅ O Y := Scheme.Modules.restrictUnitIso φ
  change unitIso.inv ≫ restriction.map (scalarEnd a ≫ s) =
    (unitIso.inv ≫ restriction.map (scalarEnd a) ≫ unitIso.hom) ≫
      unitIso.inv ≫ restriction.map s
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma sectionCombination_restrict {Y : Scheme} {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (v : σ → K) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    restrictSection φ (sectionCombination k s v) =
      sectionCombination (φ.appTop.hom.comp k) (fun i => restrictSection φ (s i)) v := by
  simp only [sectionCombination, restrictSection_sum, restrictSection_scalar, RingHom.comp_apply]

lemma sectionIdeal_framed {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (e : M ≅ O X) :
    sectionIdeal k s hs v = principalGlobalIdeal (coefficient e (sectionCombination k s v)) := by
  apply idealSheaf_ext_local
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hs.ge (Set.mem_univ x))
  obtain ⟨_, ⟨U, hUa, rfl⟩, hx, hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (SectionOpens.isoOpen (s i)).isOpen
  let A : X.affineOpens := ⟨U, hUa⟩
  refine ⟨A, hx, ?_⟩
  rw [sectionIdeal_on_frame k s hs v A i hU (restrictFrame A.1.ι e), coefficient_restrict]
  congr 2
  change (A.1.ι.appTop ≫ A.1.topIso.hom) _ = _
  apply congrArg (fun morphism : Γ(X, ⊤) ⟶ Γ(X, A.1) =>
    morphism (coefficient e (sectionCombination k s v)))
  rw [A.1.ι_appTop, A.1.topIso_hom]
  exact (X.presheaf.map_comp _ _).symm

lemma sectionIdeal_on_any_frame_s01_oai {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (U : X.affineOpens) (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    (sectionIdeal k s hs v).ideal U = Ideal.span
      {U.1.topIso.hom (coefficient e (restrictSection U.1.ι (sectionCombination k s v)))} := by
  have h := congrArg (fun J : U.1.toScheme.IdealSheafData =>
    J.ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩)
    (sectionIdeal_framed (U.1.ι.appTop.hom.comp k)
      (fun i => restrictSection U.1.ι (s i)) (restricted_sections_cover s hs U.1.ι) v e)
  rw [← sectionIdeal_restrict k s hs v U.1.ι, comap_ι_top,
    principalGlobalIdeal_top, ← sectionCombination_restrict] at h
  have h' := congrArg (Ideal.map U.1.topIso.hom.hom) h
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton] at h'
  have hid : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ :=
    congrArg CommRingCat.Hom.hom U.1.topIso.inv_hom_id
  simpa only [hid, Ideal.map_id] using h'

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Projective.sectionIdeal_on_any_frame_s01_oai := @OAI.MaximalSeshadri.Projective.sectionIdeal_on_any_frame_s01_oai
