-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:47.916222+00:00
-- url     : https://prove2.me/submissions/405f3f62-9216-45cc-969e-e01005105f3c

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
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
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

lemma endValue_endPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    endValue (endPower f n) = endValue f ^ n := by
  induction n with
  | zero =>
    change (1 : Γ(X, ⊤)) = endValue f ^ 0
    exact (pow_zero _).symm
  | succ n hn =>
    calc
      endValue (endPower f (n + 1)) = endValue f * endValue (endPower f n) :=
        endValue_comp f (endPower f n)
      _ = endValue f * endValue f ^ n := congrArg (endValue f * ·) hn
      _ = _ := (pow_succ' _ _).symm

lemma moduleTensorUnit_natural {M N : X.Modules} (g : M ⟶ N) :
    moduleTensorMap (𝟙 (structureSheaf X)) g ≫ (moduleTensorUnit N).hom =
      (moduleTensorUnit M).hom ≫ g := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let ε := (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit
  change F.map ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫
    (F.map (λ_ N.val).hom ≫ ε.app N) =
    (F.map (λ_ M.val).hom ≫ ε.app M) ≫ g
  have h : ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫ (λ_ N.val).hom =
      (λ_ M.val).hom ≫ g.val := by
    rw [id_tensorHom]
    exact leftUnitor_naturality g.val
  refine Eq.trans (F.map_comp_assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun morphism => F.map morphism ≫ ε.app N) h) ?_
  refine Eq.trans (F.map_comp_assoc _ _ _) ?_
  refine Eq.trans
    (congrArg (fun morphism => F.map (λ_ M.val).hom ≫ morphism) (ε.naturality g)) ?_
  exact (Category.assoc _ _ _).symm

lemma modulePowMap_unitPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    modulePowMap f n ≫ (unitPowerIso n).hom =
      (unitPowerIso n).hom ≫ endPower f n := by
  induction n with
  | zero =>
    change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X)
    rfl
  | succ n hn =>
    change moduleTensorMap f (modulePowMap f n) ≫
      ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) =
        ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) ≫ (f ≫ endPower f n)
    calc
      _ = moduleTensorMap f (modulePowMap f n) ≫
          moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [moduleTensorUnit_natural]
      _ = moduleTensorMap f ((unitPowerIso n).hom ≫ endPower f n) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.comp_id, hn]
      _ = moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
          moduleTensorMap f (endPower f n) ≫ (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.id_comp]
      _ = (moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫
          (unitPowerIso n).hom ≫ (f ≫ endPower f n) := by
        rw [moduleTensorUnit_scalar, ← Category.assoc, moduleTensorUnit_natural,
          Category.assoc]
      _ = _ := by simp only [Category.assoc]

lemma powerSection_coefficient {M : X.Modules} (e : M ≅ structureSheaf X)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (globalPowerFrame e n) (powerSection s n) = coefficient e s ^ n := by
  have section_power : powerSection s n ≫ (globalPowerFrame e n).hom =
      endPower (s ≫ e.hom) n := by
    change ((unitPowerIso n).inv ≫ modulePowMap s n) ≫
      (modulePowMap e.hom n ≫ (unitPowerIso n).hom) = _
    rw [Category.assoc, ← Category.assoc (modulePowMap s n), ← modulePowMap_comp,
      modulePowMap_unitPower, Iso.inv_hom_id_assoc]
  exact (congrArg (fun morphism : structureSheaf X ⟶ structureSheaf X =>
    endValue morphism) section_power).trans (endValue_endPower (s ≫ e.hom) n)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

lemma restrictPowerSection_factor (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom =
      (powerRestrictionUnit U n).hom ≫
        powerSection (restrictSection U.ι s) n := by
  let restriction : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let unitIso : restriction.obj (structureSheaf X) ≅ structureSheaf U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  change (unitIso.inv ≫ restriction.map ((unitPowerIso n).inv ≫ modulePowMap s n)) ≫
      (modulePowRestrict U M n).hom =
    (unitIso.inv ≫ restriction.map (unitPowerIso n).inv ≫
      (modulePowRestrict U (structureSheaf X) n).hom ≫
      modulePowMap unitIso.hom n ≫
      (unitPowerIso n).hom) ≫
        ((unitPowerIso n).inv ≫ modulePowMap (unitIso.inv ≫ restriction.map s) n)
  rw [restriction.map_comp]
  simp only [Category.assoc]
  rw [modulePowRestrict_natural]
  rw [Iso.hom_inv_id_assoc, ← modulePowMap_comp]
  rw [unitIso.hom_inv_id_assoc]

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma coefficient_precompose {M : X.Modules} (e : M ≅ O X)
    (a : O X ⟶ O X) (s : O X ⟶ M) :
    coefficient e (a ≫ s) = endValue a * coefficient e s := by
  change endValue ((a ≫ s) ≫ e.hom) = _
  rw [Category.assoc]
  exact endValue_comp a (s ≫ e.hom)

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

lemma local_powerSection_coefficient (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (localPowerFrame U e n) (restrictSection U.ι (powerSection s n)) =
      endValue (powerRestrictionUnit U n).hom *
        coefficient e (restrictSection U.ι s) ^ n := by
  change coefficient (globalPowerFrame e n)
    (restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom) = _
  calc
    _ = coefficient (globalPowerFrame e n)
        ((powerRestrictionUnit U n).hom ≫ powerSection (restrictSection U.ι s) n) :=
      congrArg (coefficient (globalPowerFrame e n)) (restrictPowerSection_factor U s n)
    _ = endValue (powerRestrictionUnit U n).hom *
        coefficient (globalPowerFrame e n) (powerSection (restrictSection U.ι s) n) :=
      coefficient_precompose _ _ _
    _ = _ := congrArg (endValue (powerRestrictionUnit U n).hom * ·)
      (powerSection_coefficient e _ n)

lemma local_powerSection_coefficient_unit (U : X.Opens) (n : ℕ) :
    IsUnit (endValue (powerRestrictionUnit U n).hom) := by
  have h : IsIso (powerRestrictionUnit U n).hom := inferInstance
  exact (end_isIso_iff (powerRestrictionUnit U n).hom).mp h

end
end MaximalSeshadri.Geometry


end
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
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionTransport
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
variable {X Y : Scheme} {M N : X.Modules}

lemma restrictSection_postcomp (φ : Y ⟶ X) [IsOpenImmersion φ]
    (s : O X ⟶ M) (f : M ⟶ N) :
    restrictSection φ (s ≫ f) = restrictSection φ s ≫
      (Scheme.Modules.restrictFunctor φ).map f := by
  exact (congrArg (fun morphism => (Scheme.Modules.restrictUnitIso φ).inv ≫ morphism)
    ((Scheme.Modules.restrictFunctor φ).map_comp s f)).trans (Category.assoc _ _ _).symm

lemma restrictSection_precomp (φ : Y ⟶ X) [IsOpenImmersion φ]
    (a : O X ≅ O X) (s : O X ⟶ M) :
    restrictSection φ (a.hom ≫ s) = (restrictEndIso φ a).hom ≫ restrictSection φ s := by
  let restriction := Scheme.Modules.restrictFunctor φ
  let unitIso := Scheme.Modules.restrictUnitIso φ
  change unitIso.inv ≫ restriction.map (a.hom ≫ s) =
    (unitIso.inv ≫ restriction.map a.hom ≫ unitIso.hom) ≫
      unitIso.inv ≫ restriction.map s
  exact (restrictSection_postcomp φ a.hom s).trans
    ((congrArg (fun morphism => (unitIso.inv ≫ restriction.map a.hom) ≫ morphism)
      (unitIso.hom_inv_id_assoc (restriction.map s)).symm).trans
        ((Category.assoc (unitIso.inv ≫ restriction.map a.hom) unitIso.hom
          (unitIso.inv ≫ restriction.map s)).symm.trans
            (congrArg (fun morphism => morphism ≫ unitIso.inv ≫ restriction.map s)
              (Category.assoc unitIso.inv (restriction.map a.hom) unitIso.hom))))

lemma coefficient_precomp {M : X.Modules} (e : M ≅ O X)
    (a : O X ⟶ O X) (s : O X ⟶ M) :
    coefficient e (a ≫ s) = endValue a * coefficient e s := by
  exact (congrArg endValue (Category.assoc a s e.hom)).trans (endValue_comp _ _)

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] {X : Scheme}

lemma sectionsMorphism_twist {M N : X.Modules} (k : K →+* Γ(X, ⊤))
    (a : O X ≅ O X) (e : M ≅ N) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k (fun i => a.hom ≫ s i ≫ e.hom) (twistedSections_cover a e s hs) =
      sectionsMorphism k s hs := by
  let t (i : σ) := a.hom ≫ s i ≫ e.hom
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hs).hom_ext
  intro i
  let U := SectionOpens.isoOpen (s i)
  have hU : U ≤ SectionOpens.isoOpen (t i) := by
    simp only [t, ← Category.assoc, SectionOpens.isoOpen_postcomp,
      SectionOpens.isoOpen_precomp]
    exact le_rfl
  let f := (Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ sectionFrame (s i)
  let b := sectionFrameOn (t i) U hU
  let c := frameChange f b * endUnit (restrictEndIso U.ι a)
  have hc (j : σ) : coefficient b (restrictSection U.ι (t j)) =
      (c : Γ(U.toScheme, ⊤)) * coefficient (sectionFrame (s i)) (restrictSection U.ι (s j)) := by
    rw [coefficient_change f b]
    have hh : coefficient f (restrictSection U.ι (t j)) =
        endValue (restrictEndIso U.ι a).hom *
          coefficient (sectionFrame (s i)) (restrictSection U.ι (s j)) := by
      dsimp only [f]
      rw [coefficient_transport]
      change coefficient (sectionFrame (s i))
        (restrictSection U.ι (a.hom ≫ s j ≫ e.hom) ≫
          (Scheme.Modules.restrictFunctor U.ι).map e.inv) = _
      rw [← Category.assoc a.hom, restrictSection_postcomp, Category.assoc,
        ← (Scheme.Modules.restrictFunctor U.ι).map_comp, Iso.hom_inv_id,
        (Scheme.Modules.restrictFunctor U.ι).map_id, Category.comp_id,
        restrictSection_precomp, coefficient_precomp]
    rw [hh]
    simp only [c, Units.val_mul, endUnit_val, mul_assoc]
  change U.ι ≫ sectionsMorphism k t _ = U.ι ≫ sectionsMorphism k s hs
  exact (sectionsMorphism_on k t _ i U hU).trans
    ((coordinatesMap_scale _ _ _ _ i i (sectionFrame_normalized (s i))
      (sectionFrameOn_normalized (t i) U hU) c hc).symm.trans
        (sectionsMorphism_local k s hs i).symm)

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SectionIdealExt
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
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type} [Field K] [Fintype σ] [Fintype τ] {X : Scheme}

lemma idealSheaf_ext_local {I J : X.IdealSheafData}
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ I.ideal U = J.ideal U) : I = J := by
  choose U hx hU using h
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U _ hU
  exact top_unique (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)

lemma sectionIdeal_twist {M N : X.Modules} (k : K →+* Γ(X, ⊤))
    (a : O X ≅ O X) (e : M ≅ N) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K) :
    sectionIdeal k (fun i => a.hom ≫ s i ≫ e.hom) (twistedSections_cover a e s hs) v =
      sectionIdeal k s hs v := by
  unfold sectionIdeal
  rw [sectionsMorphism_twist]

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

lemma sectionIdeal_on_any_frame {M : X.Modules} (k : K →+* Γ(X, ⊤))
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

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CartierSection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames
variable {X Y : Scheme}

lemma LineBundle.section_coefficient_regular [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    IsRegular (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))) := by
  apply isRegular_iff_ne_zero.mpr
  intro h
  apply hs
  apply L.restricted_coefficient_injective U.1.ι e
  have he := (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective
  apply he
  change U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) =
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι (0 : O X ⟶ L.sheaf)))
  exact h.trans (by rw [restrictSection_zero, coefficient_zero, map_zero])
end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_FramedPullback
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.sectionsMorphism_proper _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

                                        

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma exists_frame_natIso (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) (s : O X ⟶ M) :
    ∃ eF : F.obj M ≅ O Y,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

theorem exists_restricted_pullback_frame (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e) s
  refine ⟨eF, ?_⟩
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    have leftSection : uF.inv ≫ F.map s =
        restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) := by
      dsimp only [uF, F, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).inv ≫
          sectionMap) ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map_comp
            (pullbackUnitIso f).inv ((Scheme.Modules.pullback f).map s)).symm)
    have rightSection : uG.inv ≫ G.map s =
        pullbackSection (f ∣_ U) (restrictSection U.ι s) := by
      dsimp only [uG, G, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (pullbackUnitIso (f ∣_ U)).inv ≫ sectionMap)
          ((Scheme.Modules.pullback (f ∣_ U)).map_comp
            (Scheme.Modules.restrictUnitIso U.ι).inv
            ((Scheme.Modules.restrictFunctor U.ι).map s)).symm)
    exact (congrArg (coefficient eF) leftSection).symm.trans
      (he.trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e)) rightSection))
  rw [he', coefficient_pullback]

end MaximalSeshadri.Geometry

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
-- module Solutions.Q223_SES.Seshadri_Intersection_OpenChartDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Y : Scheme.{0}}

lemma chart_topIso_naturality (j : Y ⟶ X) (U : X.Opens) :
    U.topIso.hom ≫ j.app U ≫ (j ⁻¹ᵁ U).topIso.inv = (j ∣_ U).appTop := by
  have H := (arrowResLEAppIso j U (j ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ j.appLE U (j ⁻¹ᵁ U) le_rfl =
    (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop ≫ (j ⁻¹ᵁ U).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  apply (cancel_mono (j ⁻¹ᵁ U).topIso.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H

lemma structuralOpenChartMap_apply (p : X ⟶ Spec (CommRingCat.of ℂ))
    (j : Y ⟶ X) (U : X.Opens) (f : Γ(X,U)) :
    letI : Algebra ℂ Γ(X,U) := (openScalars p U).toAlgebra
    letI : Algebra ℂ Γ((j ⁻¹ᵁ U).toScheme,⊤) :=
      (baseScalars ((j ⁻¹ᵁ U).ι ≫ (j ≫ p))).toAlgebra
    structuralOpenChartMap p j U f = (j ⁻¹ᵁ U).topIso.inv (j.app U f) := by
  change (j ∣_ U).appTop (U.topIso.inv f) = _
  rw [← chart_topIso_naturality]
  simp only [CommRingCat.comp_apply]
  rw [U.topIso.inv_hom_id_apply]

lemma structuralOpenChartMap_ker (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (U : X.affineOpens) :
    letI : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
    letI : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
      (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
    RingHom.ker (structuralOpenChartMap p I.subschemeι U.1).toRingHom = I.ideal U := by
  ext t
  change structuralOpenChartMap p I.subschemeι U.1 t = 0 ↔ t ∈ I.ideal U
  rw [structuralOpenChartMap_apply, ← I.ker_subschemeι_app U]
  change (I.subschemeι ⁻¹ᵁ U.1).topIso.inv (I.subschemeι.app U.1 t) = 0 ↔
    I.subschemeι.app U.1 t = 0
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (I.subschemeι ⁻¹ᵁ U.1).topIso.inv).injective

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeometricDivision
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma section_value_naturality {M : X.Modules} (s : O X ⟶ M)
    {U V : X.Opens} (h : V ≤ U) :
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) =
      s.app V (1 : Γ(X,V)) := by
  have ht := CategoryTheory.congr_fun (s.mapPresheaf.naturality (homOfLE h).op)
    (1 : Γ(X,U))
  change s.app V (X.presheaf.map (homOfLE h).op (1 : Γ(X,U))) =
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) at ht
  simpa only [map_one] using ht.symm

lemma section_eq_zero_of_top_value {M : X.Modules} (s : O X ⟶ M)
    (hs : s.app ⊤ (1 : Γ(X,⊤)) = 0) : s = 0 := by
  ext U a
  change Γ(X,U) at a
  change s.app U a = 0
  have h := s.app_smul (r := a) (x := (1 : Γ(X,U)))
  change s.app U (a*1 : Γ(X,U)) = a • s.app U (1 : Γ(X,U)) at h
  rw [mul_one] at h
  rw [h, ← section_value_naturality s (show U ≤ ⊤ from le_top), hs,map_zero,smul_zero]

lemma section_eq_zero_of_local_restrictions {M : X.Modules} (s : O X ⟶ M)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ restrictSection U.ι s = 0) : s = 0 := by
  apply section_eq_zero_of_top_value
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  apply TopCat.Presheaf.section_ext F ⊤ (s.app ⊤ (1 : Γ(X,⊤))) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := hs x
  have hv : s.app U (1 : Γ(X,U)) = 0 := by
    have ht := congrArg (fun q : O U.toScheme ⟶ M.restrict U.ι =>
      q.app ⊤ (1 : Γ(U.toScheme,⊤))) hU
    change s.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))) = 0 at ht
    rw [map_one] at ht
    have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
      rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Opens.opensRange_ι]
    suffices h : ∀ V : X.Opens, V = U → s.app V (1 : Γ(X,V)) = 0 →
        s.app U (1 : Γ(X,U)) = 0 from h _ htop ht
    intro V he ht
    subst V
    exact ht
  change M.presheaf.germ ⊤ x hx (s.app ⊤ (1 : Γ(X,⊤))) =
    M.presheaf.germ ⊤ x hx 0
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (show U ≤ ⊤ from le_top)) x hxU]
  rw [section_value_naturality s, hv, map_zero, map_zero]

theorem global_division_of_local_lifts {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (s : O X ⟶ N)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ t : O U.toScheme ⟶ M.restrict U.ι,
        t ≫ (Scheme.Modules.restrictFunctor U.ι).map f = restrictSection U.ι s) :
    ∃! t : O X ⟶ M, t ≫ f = s := by
  have hz : s ≫ cokernel.π f = 0 := by
    apply section_eq_zero_of_local_restrictions
    intro x
    obtain ⟨U,hx,t,ht⟩ := hs x
    refine ⟨U,hx,?_⟩
    have hc : restrictSection U.ι (s ≫ cokernel.π f) =
        restrictSection U.ι s ≫ (Scheme.Modules.restrictFunctor U.ι).map (cokernel.π f) := by
      exact (congrArg (fun morphism :
          (Scheme.Modules.restrictFunctor U.ι).obj (O X) ⟶
            (Scheme.Modules.restrictFunctor U.ι).obj (cokernel f) =>
          (Scheme.Modules.restrictUnitIso U.ι).inv ≫ morphism)
        ((Scheme.Modules.restrictFunctor U.ι).map_comp s (cokernel.π f))).trans
          (Category.assoc _ _ _).symm
    rw [hc, ← ht, Category.assoc, ← Functor.map_comp,cokernel.condition,Functor.map_zero,comp_zero]
  refine ⟨Abelian.monoLift _ s hz,Abelian.monoLift_comp _ s hz,?_⟩
  intro t ht
  apply (cancel_mono f).mp
  rw [ht,Abelian.monoLift_comp]

lemma pullback_zero_coefficient_mem (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (hs : pullbackSection I.subschemeι s = 0) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∈ I.ideal U := by
  let : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
  let : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
    (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
  rw [← structuralOpenChartMap_ker p I U]
  change structuralOpenChartMap p I.subschemeι U.1
    (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))) = 0
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame I.subschemeι U.1 e s
  have hzero : coefficient eF
      (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι (pullbackSection I.subschemeι s)) = 0 := by
    rw [hs,restrictSection_zero,coefficient_zero]
  rw [he] at hzero
  change (I.subschemeι ∣_ U.1).appTop
    (U.1.topIso.inv (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))) = 0
  rw [U.1.topIso.hom_inv_id_apply]
  exact hzero

lemma framed_local_division {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X)
    (f : M ⟶ N) (s : O X ⟶ N)
    (hs : coefficient d s ∈ Ideal.span {endValue (e.inv ≫ f ≫ d.hom)}) :
    ∃ t : O X ⟶ M, t ≫ f = s := by
  obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hs
  refine ⟨scalarEnd r ≫ e.inv,?_⟩
  apply (cancel_mono d.hom).mp
  apply endValue_injective
  rw [Category.assoc,Category.assoc,endValue_comp,endValue_scalarEnd]
  change r * endValue (e.inv ≫ f ≫ d.hom) = coefficient d s
  rw [mul_comm,← hr]

theorem geometric_global_division (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (f : M.sheaf ⟶ N.sheaf) [Mono f]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map f ≫ d.hom))})
    (s : O X ⟶ N.sheaf) (hs : pullbackSection I.subschemeι s = 0) :
    ∃! t : O X ⟶ M.sheaf, t ≫ f = s := by
  apply global_division_of_local_lifts
  intro x
  obtain ⟨U,hx,e,d,hI⟩ := heq x
  refine ⟨U.1,hx,?_⟩
  apply framed_local_division e d
  have hb := pullback_zero_coefficient_mem p I N s hs U d
  rw [hI,Ideal.mem_span_singleton] at hb
  obtain ⟨r,hr⟩ := hb
  rw [Ideal.mem_span_singleton]
  refine ⟨U.1.topIso.inv r,?_⟩
  have h := congrArg U.1.topIso.inv hr
  simpa only [map_mul,U.1.topIso.hom_inv_id_apply] using h

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_CartierTensor
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.Tensor
noncomputable section
open TensorProduct
variable {R S A B P : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
  [NoZeroSMulDivisors S P]

theorem tmul_injective_of_local_coefficient (f : A →ₗ[R] S) (g : B →ₗ[R] P)
    {a : A} (ha : f a ≠ 0) (hg : Function.Injective g) :
    Function.Injective (fun b : B => a ⊗ₜ[R] b) := by
  let bil : A →ₗ[R] (B →ₗ[R] P) := {
    toFun a := f a • g
    map_add' a b := by simp only [map_add, add_smul]
    map_smul' r a := by
      ext b
      simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
      exact smul_assoc r (f a) (g b) }
  intro b c h
  have hh := congrArg (TensorProduct.lift bil) h
  change f a • g b = f a • g c at hh
  apply hg
  apply sub_eq_zero.mp
  apply (eq_zero_or_eq_zero_of_smul_eq_zero (c := f a) ?_).resolve_left ha
  rw [smul_sub, hh, sub_self]

end
end MaximalSeshadri.Tensor

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry TensorProduct
variable {X : Scheme} (L : LineBundle X)

lemma frameCoefficient_injective (T : X.Opens)
    (e : L.sheaf.restrict T.ι ≅ structureSheaf T.toScheme) (V : T.toScheme.Opens) :
    Function.Injective (frameCoefficient L T e V) := by
  apply Function.Injective.comp
    (ConcreteCategory.bijective_of_isIso (T.ι.appIso V).inv).injective
  apply Function.Injective.comp
    (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf T.toScheme).mapIso e).app (Opposite.op V)).hom).injective
  exact (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso T.ι V).inv).injective

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry TensorProduct
variable {X : Scheme} [IsIntegral X]

theorem LineBundle.tmul_injective (L M : LineBundle X) (U : X.Opens) [Nonempty U]
    {a : Γ(L.sheaf, U)} (ha : a ≠ 0) :
    Function.Injective (fun b : Γ(M.sheaf, U) => a ⊗ₜ[Γ(X, U)] b) := by
  obtain ⟨x, hx⟩ := ‹Nonempty U›
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
  let V : T.toScheme.Opens := T.ι ⁻¹ᵁ U
  let W : X.Opens := T.ι ''ᵁ V
  have : Nonempty W := ⟨⟨x, ⟨x, hxT⟩, hx, rfl⟩⟩
  let i : W ⟶ U := homOfLE (T.ι.image_preimage_le U)
  let h : Γ(X, U) →+* Γ(X, W) := (X.presheaf.map i.op).hom
  let : Algebra Γ(X, U) Γ(X, W) := h.toAlgebra
  let : Module Γ(X, U) Γ(M.sheaf, W) := Module.compHom _ h
  let : IsScalarTower Γ(X, U) Γ(X, W) Γ(M.sheaf, W) :=
    IsScalarTower.of_compHom _ _ _
  let := M.noZeroSMulDivisors W
  let f : Γ(L.sheaf, U) →ₗ[Γ(X, U)] Γ(X, W) := {
    toFun a := frameCoefficient L T e V (L.sheaf.presheaf.map i.op a)
    map_add' a b := by simp only [map_add]
    map_smul' r a := by
      rw [L.sheaf.map_smul, LinearMap.map_smul]
      rfl }
  let g : Γ(M.sheaf, U) →ₗ[Γ(X, U)] Γ(M.sheaf, W) := {
    toFun a := M.sheaf.presheaf.map i.op a
    map_add' a b := map_add _ _ _
    map_smul' r a := M.sheaf.map_smul i r a }
  have hf : f a ≠ 0 := by
    intro hf
    apply ha
    apply L.restriction_injective i
    apply frameCoefficient_injective L T e V
    change frameCoefficient L T e V (L.sheaf.presheaf.map i.op a) = 0 at hf
    simpa only [map_zero] using hf
  exact Tensor.tmul_injective_of_local_coefficient f g hf (M.restriction_injective i)

lemma sectionMultiplyPresheaf_mono (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    Mono (sectionMultiplyPresheaf L M s) := by
  apply PresheafOfModules.mono_of_injective
  intro U a b hab
  by_cases hU : Nonempty U.unop
  · let := hU
    have hn : s.app U.unop (1 : Γ(X, U.unop)) ≠ 0 := by
      intro hn
      apply hs
      apply L.section_restriction_injective U.unop
      exact hn
    apply L.tmul_injective M U.unop hn
    exact hab
  · have he : U.unop = ⊥ := by
      apply Opens.ext
      ext x
      exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    have : Subsingleton Γ(X, U.unop) := by rw [he]; infer_instance
    let := Module.subsingleton Γ(X, U.unop) Γ(M.sheaf, U.unop)
    change Γ(M.sheaf, U.unop) at a b
    exact Subsingleton.elim a b

theorem sectionMultiply_mono (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    Mono (sectionMultiply L M s) := by
  have : Mono (sectionMultiplyPresheaf L M s) := sectionMultiplyPresheaf_mono L M s hs
  have hm : Mono ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (sectionMultiplyPresheaf L M s)) := by
    exact CategoryTheory.preserves_mono_of_preservesLimit _ _
  let e := (asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit).app M.sheaf
  have he : Mono e.inv := ⟨fun a b h => by
    have q := congrArg (fun k => k ≫ e.hom) h
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using q⟩
  exact mono_comp' he hm

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorDivision
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

lemma tensor_multiply_ideal (L M : LineBundle X) (s : O X ⟶ L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue (f.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiply L M s) ≫
        (tensorFrame L M U.1 e f).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  rw [tensor_multiply_framed,endValue_comp,map_mul,← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).hom) :=
    (end_isIso_iff _).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.top_mul]
  rfl

theorem divide_by_generated_section [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (s : σ → (O X ⟶ L.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    (t : O X ⟶ (L.tensor M).sheaf)
    (ht : pullbackSection (sectionIdeal k s hs v).subschemeι t = 0) :
    ∃! q : O X ⟶ M.sheaf, q ≫ sectionMultiply L M (sectionCombination k s v) = t := by
  apply @geometric_global_division X p M (L.tensor M)
    (sectionMultiply L M (sectionCombination k s v))
    (sectionMultiply_mono L M _ hne) (sectionIdeal k s hs v) ?_ t ht
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U,hx,f,tensorFrame L M U.1 e f,?_⟩
  exact (sectionIdeal_on_any_frame k s hs v U e).trans
    (tensor_multiply_ideal L M (sectionCombination k s v) U e f).symm

theorem divide_by_power_section [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (d n : ℕ)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (a : σ → (O X ⟶ (L.pow d).sheaf))
    (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k a v ≠ 0)
    (t : O X ⟶ (L.pow (d+n)).sheaf)
    (ht : pullbackSection (sectionIdeal k a ha v).subschemeι t = 0) :
    ∃! q : O X ⟶ (L.pow n).sheaf,
      q ≫ sectionMultiply (L.pow d) (L.pow n) (sectionCombination k a v) ≫
        (linePowerAdd L d n).inv = t := by
  let e : (L.pow (d+n)).sheaf ≅ ((L.pow d).tensor (L.pow n)).sheaf :=
    linePowerAdd L d n
  have hv : pullbackSection (sectionIdeal k a ha v).subschemeι (t ≫ e.hom) = 0 := by
    unfold pullbackSection at ht ⊢
    rw [Functor.map_comp,← Category.assoc,ht,zero_comp]
  obtain ⟨q,hq,huniq⟩ := divide_by_generated_section (X := X) p (L.pow d) (L.pow n)
    k a ha v hne (t ≫ e.hom) hv
  let multiplication : (L.pow n).sheaf ⟶ ((L.pow d).tensor (L.pow n)).sheaf :=
    sectionMultiply (L.pow d) (L.pow n) (sectionCombination k a v)
  change q ≫ multiplication = t ≫ e.hom at hq
  refine ⟨q,?_,?_⟩
  · change q ≫ multiplication ≫ e.inv = t
    rw [← Category.assoc,hq,Category.assoc,e.hom_inv_id,Category.comp_id]
  · intro r hr
    apply huniq
    apply (cancel_mono e.inv).mp
    change r ≫ multiplication ≫ e.inv = t at hr
    change (r ≫ multiplication) ≫ e.inv = (t ≫ e.hom) ≫ e.inv
    simpa only [Category.assoc,e.hom_inv_id,Category.comp_id] using hr

lemma global_quotient_ne_zero {M N : X.Modules} (f : M ⟶ N)
    (s : O X ⟶ N) (hs : s ≠ 0) (t : O X ⟶ M) (ht : t ≫ f = s) : t ≠ 0 := by
  intro h
  rw [h,zero_comp] at ht
  exact hs ht.symm

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCoefficientOrder
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

lemma affineCoefficient_change {M : X.Modules} (U : X.affineOpens)
    (e f : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) :
    Associated (affineCoefficient U e s) (affineCoefficient U f s) := by
  unfold affineCoefficient
  rw [coefficient_change e f, map_mul]
  exact associated_unit_mul_right _ _ ((frameChange e f).isUnit.map U.1.topIso.hom.hom)

lemma affineCoefficient_iso {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (g : M ≅ N) (s : O X ⟶ M) :
    Associated (affineCoefficient U e s) (affineCoefficient U f (s ≫ g.hom)) := by
  have h := affineCoefficient_change U e
    ((Scheme.Modules.restrictFunctor U.1.ι).mapIso g ≪≫ f) s
  let restriction := Scheme.Modules.restrictFunctor U.1.ι
  let unitIso := Scheme.Modules.restrictUnitIso U.1.ι
  have composition :
      (unitIso.inv ≫ restriction.map s) ≫ restriction.map g.hom ≫ f.hom =
        (unitIso.inv ≫ restriction.map (s ≫ g.hom)) ≫ f.hom := by
    calc
      _ = unitIso.inv ≫ (restriction.map s ≫ restriction.map g.hom) ≫ f.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun morphism => unitIso.inv ≫ morphism)
            (Category.assoc _ _ _).symm)
      _ = unitIso.inv ≫ restriction.map (s ≫ g.hom) ≫ f.hom :=
        congrArg (fun morphism => unitIso.inv ≫ morphism ≫ f.hom)
          (restriction.map_comp s g.hom).symm
      _ = _ := (Category.assoc _ _ _).symm
  have equality : affineCoefficient U (restriction.mapIso g ≪≫ f) s =
      affineCoefficient U f (s ≫ g.hom) :=
    congrArg (fun value => U.1.topIso.hom value) (congrArg endValue composition)
  exact equality ▸ h

lemma affineCoefficient_ne_zero [IsIntegral X] (L : LineBundle X)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : affineCoefficient U e s ≠ 0 := by
  exact (isRegular_iff_ne_zero.mp (L.section_coefficient_regular s hs U e))

lemma coefficient_postcompose {Y : Scheme.{0}} {M N : Y.Modules}
    (e : M ≅ O Y) (f : N ≅ O Y) (s : O Y ⟶ M) (a : M ⟶ N) :
    coefficient f (s ≫ a) = coefficient e s * endValue (e.inv ≫ a ≫ f.hom) := by
  unfold coefficient
  rw [← endValue_comp]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]

lemma associated_unit_middle {R : Type*} [CommMonoid R] (a b u : R) (hu : IsUnit u) :
    Associated (a*b) (b*(u*a)) := by
  rw [show b*(u*a) = u*(a*b) by ac_rfl]
  exact associated_unit_mul_right _ _ hu

lemma affineCoefficient_sectionMultiply (L M : LineBundle X) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (g : (L.tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    Associated (affineCoefficient U e s * affineCoefficient U f t)
      (affineCoefficient U g (t ≫ sectionMultiply L M s)) := by
  apply Associated.trans _ (affineCoefficient_change U (tensorFrame L M U.1 e f) g _)
  let multiplication : M.sheaf ⟶ (L.tensor M).sheaf := sectionMultiply L M s
  let restriction := Scheme.Modules.restrictFunctor U.1.ι
  let unitIso := Scheme.Modules.restrictUnitIso U.1.ι
  let tensorTrivialization : (L.tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
    tensorFrame L M U.1 e f
  have restrictedComposition : restrictSection U.1.ι (t ≫ multiplication) =
      restrictSection U.1.ι t ≫ restriction.map multiplication :=
    (congrArg (fun morphism => unitIso.inv ≫ morphism)
      (restriction.map_comp t multiplication)).trans (Category.assoc _ _ _).symm
  have he : coefficient (tensorFrame L M U.1 e f)
      (restrictSection U.1.ι (t ≫ sectionMultiply L M s)) =
      coefficient f (restrictSection U.1.ι t) *
        (endValue (tensorUnitTwist M U.1 f).hom * coefficient e (restrictSection U.1.ι s)) := by
    calc
      _ = coefficient tensorTrivialization
          (restrictSection U.1.ι t ≫ restriction.map multiplication) :=
        congrArg (coefficient tensorTrivialization) restrictedComposition
      _ = coefficient f (restrictSection U.1.ι t) *
          endValue (f.inv ≫ restriction.map multiplication ≫ tensorTrivialization.hom) :=
        coefficient_postcompose f tensorTrivialization _ _
      _ = coefficient f (restrictSection U.1.ι t) *
          endValue ((tensorUnitTwist M U.1 f).hom ≫ (restrictSection U.1.ι s ≫ e.hom)) :=
        congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme =>
          coefficient f (restrictSection U.1.ι t) * endValue morphism)
          (tensor_multiply_framed L M s U.1 e f)
      _ = _ := congrArg (coefficient f (restrictSection U.1.ι t) * ·)
        (endValue_comp _ _)
  have equality : affineCoefficient U tensorTrivialization (t ≫ multiplication) =
      affineCoefficient U f t *
        (U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).hom) * affineCoefficient U e s) :=
    (congrArg (fun value => U.1.topIso.hom value) he).trans
      (by simp only [map_mul, affineCoefficient])
  exact equality.symm ▸ associated_unit_middle
    (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))
    (U.1.topIso.hom (coefficient f (restrictSection U.1.ι t)))
    (U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).hom))
    (((end_isIso_iff _).mp (tensorUnitTwist M U.1 f).isIso_hom).map
      U.1.topIso.hom.hom)

lemma affineCoefficient_power (L : LineBundle X) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (s : O X ⟶ L.sheaf) (n : ℕ)
    (f : (L.pow n).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Associated ((affineCoefficient U e s)^n)
      (affineCoefficient U f (powerSection s n)) := by
  apply Associated.trans _ (affineCoefficient_change U (localPowerFrame U.1 e n) f _)
  have equality : affineCoefficient U (localPowerFrame U.1 e n) (powerSection s n) =
      U.1.topIso.hom (endValue (powerRestrictionUnit U.1 n).hom) *
        (affineCoefficient U e s) ^ n :=
    (congrArg (fun value => U.1.topIso.hom value)
      (local_powerSection_coefficient U.1 e s n)).trans
        (by simp only [map_mul, map_pow, affineCoefficient])
  exact equality.symm ▸ associated_unit_mul_right _ _
    ((local_powerSection_coefficient_unit U.1 n).map U.1.topIso.hom.hom)

lemma affineCoefficient_division (L : LineBundle X) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (d n : ℕ)
    (s : O X ⟶ (L.pow d).sheaf) (t : O X ⟶ (L.pow n).sheaf) :
    Associated
      (affineCoefficient U (localPowerFrame U.1 e d) s *
       affineCoefficient U (localPowerFrame U.1 e n) t)
      (affineCoefficient U (localPowerFrame U.1 e (d+n))
        (t ≫ sectionMultiply (L.pow d) (L.pow n) s ≫ (linePowerAdd L d n).inv)) := by
  exact (affineCoefficient_sectionMultiply (L.pow d) (L.pow n) U _ _
    (tensorFrame (L.pow d) (L.pow n) U.1 (localPowerFrame U.1 e d)
      (localPowerFrame U.1 e n)) s t).trans
    (affineCoefficient_iso U _ _ (linePowerAdd L d n).symm _)

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_ProperGlobalField
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.constantsInDegreeZero_isIso _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.projectiveSpaceToSpec_proper _root_.OAI.MaximalSeshadri.Geometry.projectiveSpaceToSpec_separated _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

instance Surface.isProper_structureMap (surface : Surface) : IsProper surface.structureMap := by
  have constants_bijective : Function.Bijective
      (constantsInDegreeZero surface.embeddingDimension) := by
    constructor
    · intro left right equality
      have polynomial_equality : MvPolynomial.C left =
          (MvPolynomial.C right : MvPolynomial (Fin (surface.embeddingDimension + 1)) ℂ) :=
        congrArg Subtype.val equality
      exact MvPolynomial.C_injective _ _ polynomial_equality
    · intro polynomial
      have degree_zero : polynomial.val.totalDegree = 0 :=
        (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr polynomial.property
      refine ⟨polynomial.val.coeff 0, ?_⟩
      apply Subtype.ext
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp degree_zero).symm
  let constantsIso := (RingEquiv.ofBijective
    (constantsInDegreeZero surface.embeddingDimension) constants_bijective).toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (constantsInDegreeZero surface.embeddingDimension)) :=
    constantsIso.isIso_hom
  let polynomialRing := MvPolynomial (Fin (surface.embeddingDimension + 1)) ℂ
  let grading := MvPolynomial.homogeneousSubmodule (Fin (surface.embeddingDimension + 1)) ℂ
  let : Algebra ℂ (grading 0) := SetLike.GradeZero.instAlgebra grading
  let : IsScalarTower ℂ (grading 0) polynomialRing := ⟨fun scalar homogeneous polynomial => by
    change (scalar • (homogeneous : polynomialRing)) * polynomial =
      scalar • ((homogeneous : polynomialRing) * polynomial)
    exact smul_mul_assoc scalar (homogeneous : polynomialRing) polynomial⟩
  let : Algebra.FiniteType (grading 0) polynomialRing :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (grading 0) polynomialRing
  have projective_proper : IsProper (Proj.toSpecZero grading) :=
    Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat grading
  let : IsIso (Spec.map
      (CommRingCat.ofHom (constantsInDegreeZero surface.embeddingDimension))) := by
    infer_instance
  have : IsProper (projectiveSpaceToSpec surface.embeddingDimension) := by
    unfold projectiveSpaceToSpec
    exact IsProper.stableUnderComposition.comp_mem _ _ projective_proper inferInstance
  rw [← surface.overComplex]
  infer_instance

variable {X : Scheme.{0}} [IsIntegral X]

theorem proper_baseScalars_surjective (p : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper p] : Function.Surjective (baseScalars p) := by
  have hi : (baseScalars p).IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral (baseScalars p) hi).2

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_ResidualZero
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.MaximalSeshadri.Projective.sectionsMorphism_proper _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}} [IsIntegral X]

theorem proper_nonzero_structure_section_constant
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (s : O X ⟶ O X) (hs : s ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ s = scalarEnd (baseScalars p c) := by
  obtain ⟨c,hc⟩ := proper_baseScalars_surjective p (endValue s)
  have he : s = scalarEnd (baseScalars p c) := by
    apply endValue_injective
    rw [endValue_scalarEnd,hc]
  refine ⟨c,?_,he⟩
  intro hz
  apply hs
  apply endValue_injective
  rw [← hc,hz,map_zero]
  rfl

theorem proper_nonzero_structure_section_isIso
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (s : O X ⟶ O X) (hs : s ≠ 0) : IsIso s := by
  obtain ⟨c,hc,rfl⟩ := proper_nonzero_structure_section_constant p s hs
  apply (end_isIso_iff _).mpr
  rw [endValue_scalarEnd]
  exact (isUnit_iff_ne_zero.mpr hc).map (baseScalars p)

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_LocalContainment
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

theorem pullback_section_zero_iff_local_coefficient
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (U : X.affineOpens) [Nonempty (I.subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    pullbackSection I.subschemeι s = 0 ↔
      U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∈ I.ideal U := by
  let : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
  let : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
    (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame I.subschemeι U.1 e s
  let π := structuralOpenChartMap p I.subschemeι U.1
  let f := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
  have hcoeff : π f = coefficient eF
      (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι (pullbackSection I.subschemeι s)) := by
    rw [he]
    change (I.subschemeι ∣_ U.1).appTop
      (U.1.topIso.inv (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))) = _
    rw [U.1.topIso.hom_inv_id_apply]
  have hker : f ∈ I.ideal U ↔ π f = 0 := by
    rw [← structuralOpenChartMap_ker p I U]
    rfl
  rw [show U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) = f from rfl,
    hker, hcoeff]
  constructor
  · intro h
    rw [h,restrictSection_zero,coefficient_zero]
  · intro h
    apply (L.pullback I.subschemeι).restricted_coefficient_injective
      (I.subschemeι ⁻¹ᵁ U.1).ι eF
    change coefficient eF
      (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι (pullbackSection I.subschemeι s)) =
      coefficient eF (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι
        (0 : O I.subscheme ⟶ (Scheme.Modules.pullback I.subschemeι).obj L.sheaf))
    rw [restrictSection_zero,coefficient_zero]
    exact h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CartierExtraction
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.scheme_isReduced _root_.OAI.MaximalSeshadri.BlowupGluing.scheme_isReduced _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X]

theorem extract_power_with_order (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (d n j : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (t : O X ⟶ (L.pow (d+n)).sheaf) (ht : t ≠ 0)
    (ho : (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v))^(j+1) ∣
      affineCoefficient U (localPowerFrame U.1 e (d+n)) t) :
    ∃ q : O X ⟶ (L.pow n).sheaf, q ≠ 0 ∧
      q ≫ sectionMultiply (L.pow d) (L.pow n) (sectionCombination k s v) ≫
        (linePowerAdd L d n).inv = t ∧
      (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v))^j ∣
        affineCoefficient U (localPowerFrame U.1 e n) q := by
  let f := affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)
  have hf : f ≠ 0 := affineCoefficient_ne_zero (L.pow d) U _ _ hne
  have hv : pullbackSection (sectionIdeal k s hs v).subschemeι t = 0 := by
    apply (pullback_section_zero_iff_local_coefficient p _ (L.pow (d+n)) t U
      (localPowerFrame U.1 e (d+n))).mpr
    rw [sectionIdeal_on_any_frame k s hs v U (localPowerFrame U.1 e d),
      Ideal.mem_span_singleton]
    obtain ⟨b,hb⟩ := ho
    refine ⟨f^j*b,?_⟩
    change affineCoefficient U (localPowerFrame U.1 e (d+n)) t = f*(f^j*b)
    rw [hb]
    change f^(j+1)*b = _
    ring
  obtain ⟨q,hq,-⟩ := divide_by_power_section p L d n k s hs v hne t hv
  refine ⟨q,global_quotient_ne_zero _ t ht q hq,hq,?_⟩
  have he := affineCoefficient_division L U e d n (sectionCombination k s v) q
  rw [hq] at he
  have hd := he.dvd_iff_dvd_right.mpr ho
  change f^(j+1) ∣ f*affineCoefficient U (localPowerFrame U.1 e n) q at hd
  rw [pow_succ'] at hd
  exact (mul_dvd_mul_iff_left hf).mp hd

theorem power_multiple_order_bound (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)))
    (m : ℕ) : ∀ t : O X ⟶ (L.pow (d*m)).sheaf, t ≠ 0 →
      ¬ ((affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v))^(m+1) ∣
        affineCoefficient U (localPowerFrame U.1 e (d*m)) t) := by
  induction m with
  | zero =>
    intro t ht hd
    have sectionIsIso : IsIso t := proper_nonzero_structure_section_isIso p t ht
    have hu : IsUnit (affineCoefficient U (localPowerFrame U.1 e (d*0)) t) := by
      apply IsUnit.map U.1.topIso.hom.hom
      apply (end_isIso_iff _).mp
      dsimp only [coefficient,restrictSection]
      exact IsIso.comp_isIso'
        (IsIso.comp_isIso' (Scheme.Modules.restrictUnitIso U.1.ι).isIso_inv
          ((Scheme.Modules.restrictFunctor U.1.ι).map_isIso t))
        (localPowerFrame U.1 e (d*0)).isIso_hom
    simp only [Nat.mul_zero,Nat.zero_add,pow_one] at hd
    exact hnu (isUnit_of_dvd_unit hd hu)
  | succ m ih =>
    rw [Nat.mul_succ,Nat.add_comm (d*m) d]
    intro t ht hd
    obtain ⟨q,hq,he,ho⟩ := extract_power_with_order p L d (d*m) (m+1) k s hs v hne U e t ht hd
    exact ih q hq ho

theorem cartier_order_times_degree_le_power (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)))
    (a i : ℕ) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0)
    (ho : (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v))^i ∣
      affineCoefficient U (localPowerFrame U.1 e a) t) : i*d ≤ a := by
  let f := affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)
  let b := affineCoefficient U (localPowerFrame U.1 e a) t
  let E : ((L.pow a).pow d).sheaf ≅ (L.pow (d*a)).sheaf :=
    linePowerMul L a d ≪≫ eqToIso (congrArg (fun n => modulePow X L.sheaf n) (Nat.mul_comm a d))
  let q : O X ⟶ (L.pow (d*a)).sheaf := powerSection t d ≫ E.hom
  have ha := affineCoefficient_power (L.pow a) U (localPowerFrame U.1 e a) t d
    (localPowerFrame U.1 (localPowerFrame U.1 e a) d)
  have hb := affineCoefficient_iso U (localPowerFrame U.1 (localPowerFrame U.1 e a) d)
    (localPowerFrame U.1 e (d*a)) E (powerSection t d)
  have H : Associated (b^d) (affineCoefficient U (localPowerFrame U.1 e (d*a)) q) := ha.trans hb
  have hq : q ≠ 0 := by
    intro hq
    have hz : affineCoefficient U (localPowerFrame U.1 e (d*a)) q = 0 := by
      rw [hq]
      let frame : (L.pow (d*a)).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
        localPowerFrame U.1 e (d*a)
      exact (congrArg (fun value => U.1.topIso.hom value)
        ((congrArg (coefficient frame) (restrictSection_zero U.1.ι)).trans
          (coefficient_zero frame))).trans (map_zero U.1.topIso.hom.hom)
    have hn : b ≠ 0 := affineCoefficient_ne_zero (L.pow a) U _ t ht
    exact (pow_ne_zero d hn) (H.eq_zero_iff.mpr hz)
  by_contra hle
  have hlt : a+1 ≤ i*d := by omega
  have hd : f^(i*d) ∣ b^d := by
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd ho d
  have hdiv : f^(a+1) ∣ affineCoefficient U (localPowerFrame U.1 e (d*a)) q :=
    dvd_trans (pow_dvd_pow f hlt) (dvd_trans hd H.dvd)
  exact power_multiple_order_bound p L d k s hs v hne U e hnu a q hq hdiv

theorem small_power_restriction_ne_zero (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)))
    (a : ℕ) (ha : a < d) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0) :
    pullbackSection (sectionIdeal k s hs v).subschemeι t ≠ 0 := by
  intro hv
  have ho := (pullback_section_zero_iff_local_coefficient p _ (L.pow a) t U
    (localPowerFrame U.1 e a)).mp hv
  rw [sectionIdeal_on_any_frame k s hs v U (localPowerFrame U.1 e d),
    Ideal.mem_span_singleton] at ho
  change affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v) ∣
    affineCoefficient U (localPowerFrame U.1 e a) t at ho
  have hb := cartier_order_times_degree_le_power p L d k s hs v hne U e hnu a 1 t ht
    (by simpa only [pow_one] using ho)
  omega

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_MaximalCartier
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X]

lemma associated_power_step {R : Type*} [CommMonoid R] (f b c z : R) (j : ℕ)
    (h : Associated (f^j*b) c) (h' : Associated (f*c) z) :
    Associated (f^(j+1)*b) z := by
  have H := h.mul_left f
  rw [← mul_assoc,← pow_succ'] at H
  exact H.trans h'

theorem maximal_cartier_extraction (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) (hd : 0 < d) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)))
    (a : ℕ) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0) :
    ∃ j n : ℕ, a = j*d+n ∧ ∃ q : O X ⟶ (L.pow n).sheaf, q ≠ 0 ∧
      pullbackSection (sectionIdeal k s hs v).subschemeι q ≠ 0 ∧
      Associated ((affineCoefficient U (localPowerFrame U.1 e d)
        (sectionCombination k s v))^j * affineCoefficient U (localPowerFrame U.1 e n) q)
        (affineCoefficient U (localPowerFrame U.1 e a) t) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases hv : pullbackSection (sectionIdeal k s hs v).subschemeι t = 0
    · have hda : d ≤ a := by
        by_contra h
        exact small_power_restriction_ne_zero p L d k s hs v hne U e hnu a
          (by omega) t ht hv
      obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hda
      obtain ⟨q,hq,-⟩ := divide_by_power_section p L d n k s hs v hne t hv
      have hqn : q ≠ 0 := global_quotient_ne_zero _ t ht q hq
      obtain ⟨j,r,he,z,hz,hzv,hassoc⟩ := ih n (by omega) q hqn
      refine ⟨j+1,r,by rw [he]; ring,z,hz,hzv,?_⟩
      have ha := affineCoefficient_division L U e d n (sectionCombination k s v) q
      rw [hq] at ha
      exact associated_power_step _ _ _ _ j hassoc ha
    · exact ⟨0,a,by simp,t,ht,hv,by simpa only [pow_zero,one_mul] using (Associated.refl
        (affineCoefficient U (localPowerFrame U.1 e a) t))⟩
end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_MaximalCartierIso
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X]

theorem maximal_cartier_extraction_of_iso_s01_oai (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L M : LineBundle X) (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U eM (sectionCombination k s v)))
    (a : ℕ) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0)
    (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ∃ j n : ℕ, a = j*d+n ∧ ∃ q : O X ⟶ (L.pow n).sheaf, q ≠ 0 ∧
      pullbackSection (sectionIdeal k s hs v).subschemeι q ≠ 0 ∧
      Associated ((affineCoefficient U eM (sectionCombination k s v))^j *
        affineCoefficient U (localPowerFrame U.1 e n) q) (affineCoefficient U eA t) := by
  let s' := fun i => (Iso.refl (O X)).hom ≫ s i ≫ E.hom
  have hs' := twistedSections_cover (Iso.refl (O X)) E s hs
  have hI := sectionIdeal_twist k (Iso.refl (O X)) E s hs v
  have hc : sectionCombination k s' v = sectionCombination k s v ≫ E.hom := by
    simp only [sectionCombination,s',Iso.refl_hom,Category.id_comp,
      Preadditive.sum_comp,Category.assoc]
  have hn : sectionCombination k s' v ≠ 0 := by
    rw [hc]
    exact fun h => hne ((cancel_mono E.hom).mp (by simpa using h))
  let : IsIntegral (sectionIdeal k s' hs' v).subscheme := by rw [hI]; infer_instance
  let : Nonempty ((sectionIdeal k s' hs' v).subschemeι ⁻¹ᵁ U.1).toScheme := by
    rw [hI]; infer_instance
  have hass : Associated (affineCoefficient U eM (sectionCombination k s v))
      (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s' v)) := by
    have coefficient_eq := congrArg
      (fun globalSection : O X ⟶ (L.pow d).sheaf =>
        affineCoefficient U (localPowerFrame U.1 e d) globalSection) hc
    exact coefficient_eq.symm ▸ affineCoefficient_iso U eM _ E _
  have hnu' : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s' v)) :=
    fun h => hnu (hass.isUnit_iff.mpr h)
  obtain ⟨j,n,ha,q,hq,hqv,hqass⟩ :=
    maximal_cartier_extraction p L d hd k s' hs' v hn U e hnu' a t ht
  rw [hI] at hqv
  refine ⟨j,n,ha,q,hq,hqv,?_⟩
  exact (((hass.pow_pow (n := j)).mul_right _).trans hqass).trans
    (affineCoefficient_change U _ eA t)
end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso_s01_oai := @OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso_s01_oai
