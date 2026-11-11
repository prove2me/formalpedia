-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:37.035763+00:00
-- url     : https://prove2.me/submissions/509279db-3434-41a3-9c11-d902ebac2e9b

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H0_finite_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_power_H2_bounded_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_pow_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_tensor_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_curveDegree_eq_mixedEuler_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_power_euler_difference_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_section_H2_untwist_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_twist_euler_difference_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_mixedEuler_pow_right_s01

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CohomologyIso
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

variable {X : Scheme.{0}}

lemma eulerCharacteristic_iso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (d : ℕ) :
    eulerCharacteristic f d M = eulerCharacteristic f d N := by
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars f)
  let := Module.compHom (cohomology N n) (baseScalars f)
  exact (cohomologyIso f e n).finrank_eq

end
end MaximalSeshadri.Geometry
end


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

lemma affine_function_denom [IsAffine X] (a : Γ(X, ⊤))
    (f : Γ((X.basicOpen a).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ g : Γ(X, ⊤),
      (X.basicOpen a).ι.appTop g = f * (X.basicOpen a).ι.appTop a ^ n := by
  obtain ⟨N, g, hg⟩ := IsLocalization.Away.surj a f
  refine ⟨N, fun n hn => ⟨g * a ^ (n - N), ?_⟩⟩
  change algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) (g * a ^ (n - N)) =
    f * algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) a ^ n
  rw [map_mul, map_pow, ← hg, mul_assoc, ← pow_add, Nat.add_sub_of_le hn]

end
end MaximalSeshadri.Geometry

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
-- module Solutions.Q223_SES.Seshadri_Sheaves_SectionOpens
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.sectionOpen_power (L : LineBundle X) (s : GlobalSections X L.sheaf)
    {n : ℕ} (hn : 0 < n) :
    sectionOpen X (powerSection s n) = sectionOpen X s := by
  have hlocal (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
      U.ι ⁻¹ᵁ sectionOpen X (powerSection s n) = U.ι ⁻¹ᵁ sectionOpen X s := by
    change U.ι ⁻¹ᵁ SectionOpens.isoOpen (powerSection s n) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen s
    calc
      _ = U.toScheme.basicOpen (coefficient (localPowerFrame U e n)
          (restrictSection U.ι (powerSection s n))) :=
        preimage_isoOpen (powerSection s n) U.ι (localPowerFrame U e n)
      _ = U.toScheme.basicOpen (endValue (powerRestrictionUnit U n).hom *
          coefficient e (restrictSection U.ι s) ^ n) :=
        congrArg U.toScheme.basicOpen (local_powerSection_coefficient U e s n)
      _ = U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) := by
        rw [Scheme.basicOpen_mul,
          Scheme.basicOpen_of_isUnit _ (local_powerSection_coefficient_unit U n),
          top_inf_eq]
        exact U.toScheme.basicOpen_pow (coefficient e (restrictSection U.ι s)) hn
      _ = _ := (preimage_isoOpen s U.ι e).symm
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have h := congrArg (fun V : U.toScheme.Opens => (⟨x, hxU⟩ : U.toScheme) ∈ V) (hlocal U e)
  exact Iff.of_eq h

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_Sections
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
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
namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma section_value_natural {M : X.Modules} (s : O X ⟶ M) {U V : X.Opens} (i : U ⟶ V) :
    M.presheaf.map i.op (s.app V (1 : Γ(X, V))) = s.app U (1 : Γ(X, U)) := by
  have h := CategoryTheory.congr_fun (s.mapPresheaf.naturality i.op) (1 : Γ(X, V))
  change s.app U (X.presheaf.map i.op (1 : Γ(X, V))) =
    M.presheaf.map i.op (s.app V (1 : Γ(X, V))) at h
  simpa only [map_one] using h.symm

@[simp] lemma openSectionEquiv_restrict {M : X.Modules} (s : O X ⟶ M) (U : X.Opens) :
    openSectionEquiv M U (restrictSection U.ι s) = s.app U (1 : Γ(X, U)) := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (s.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤)))) = _
  rw [map_one]
  exact section_value_natural s (eqToHom U.ι_image_top.symm)

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma moduleSectionEquiv_scalar {M : X.Modules} (f : Γ(X, ⊤)) (s : O X ⟶ M) :
    moduleSectionEquiv M (scalarEnd f ≫ s) = f • moduleSectionEquiv M s := by
  change s.app ⊤ (endValue (scalarEnd f)) = f • s.app ⊤ (1 : Γ(X, ⊤))
  rw [endValue_scalarEnd]
  have scalar := s.app_smul (r := f) (x := (1 : Γ(X, ⊤)))
  change s.app ⊤ (f * 1 : Γ(X, ⊤)) = _ at scalar
  simpa only [mul_one] using scalar

lemma openSectionEquiv_scalar (M : X.Modules) (U : X.Opens)
    (f : Γ(U.toScheme, ⊤)) (s : O U.toScheme ⟶ M.restrict U.ι) :
    openSectionEquiv M U (scalarEnd f ≫ s) = U.topIso.hom f • openSectionEquiv M U s := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (moduleSectionEquiv (M.restrict U.ι) (scalarEnd f ≫ s)) = _
  rw [moduleSectionEquiv_scalar]
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    ((U.ι.appIso ⊤).inv f • (show Γ(M, U.ι ''ᵁ ⊤) from moduleSectionEquiv (M.restrict U.ι) s)) = _
  rw [M.map_smul, U.ι_appIso]
  rfl

lemma openSectionEquiv_restrict_value (M : X.Modules) (U : X.Opens)
    (s : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U s) =
      s.app W (1 : Γ(U.toScheme, W)) := by
  have h := section_value_natural s (homOfLE (show W ≤ ⊤ from le_top))
  change M.presheaf.map (U.ι.opensFunctor.map (homOfLE (show W ≤ ⊤ from le_top))).op
    (s.app ⊤ (1 : Γ(U.toScheme, ⊤))) = _ at h
  change M.presheaf.map (homOfLE (U.ι_image_le W)).op
    (M.presheaf.map (eqToHom U.ι_image_top.symm).op (s.app ⊤ (1 : Γ(U.toScheme, ⊤)))) = _
  exact (M.presheaf.map_comp_apply (eqToHom U.ι_image_top.symm).op
    (homOfLE (U.ι_image_le W)).op
    (show Γ(M, U.ι ''ᵁ ⊤) from s.app ⊤ (1 : Γ(U.toScheme, ⊤)))).symm.trans h

lemma image_section_extension (M : X.Modules) (U : X.Opens)
    (s t : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens)
    (f : Γ(W.toScheme, ⊤))
    (h : restrictSection W.ι t = scalarEnd f ≫ restrictSection W.ι s) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U t) =
      (U.ι.appIso W).inv (W.topIso.hom f) • M.presheaf.map (homOfLE (U.ι_image_le W)).op
        (openSectionEquiv M U s) := by
  have hh := congrArg (openSectionEquiv (M.restrict U.ι) W) h
  rw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict] at hh
  rw [openSectionEquiv_restrict_value, openSectionEquiv_restrict_value]
  exact hh

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

theorem local_affine_power_extension (U : X.Opens) [IsAffine U.toScheme]
    {M : X.Modules} (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : GlobalSections X M)
    (f : Γ((U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : structureSheaf U.toScheme ⟶ (modulePow X M n).restrict U.ι,
      restrictSection (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).ι t =
        scalarEnd f ≫ restrictSection
          (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).ι
          (restrictSection U.ι (powerSection s n)) := by
  let a := coefficient e (restrictSection U.ι s)
  obtain ⟨N, hN⟩ := affine_function_denom a f
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨g, hg⟩ := hN n hn
  let eₙ := localPowerFrame U e n
  let c := endValue (powerRestrictionUnit U n).hom
  let φ := (U.toScheme.basicOpen a).ι
  refine ⟨scalarEnd (c * g) ≫ eₙ.inv, ?_⟩
  apply coefficient_injective (restrictFrame φ eₙ)
  calc
    _ = φ.appTop (c * g) := (coefficient_restrict φ eₙ _).trans
      (congrArg φ.appTop (coefficient_scalarEnd eₙ (c * g)))
    _ = φ.appTop c * φ.appTop g := map_mul φ.appTop.hom c g
    _ = φ.appTop c * (f * φ.appTop a ^ n) := congrArg (φ.appTop c * ·) hg
    _ = f * φ.appTop (c * a ^ n) := by
      simp only [map_mul, map_pow]
      ring
    _ = f * φ.appTop (coefficient eₙ (restrictSection U.ι (powerSection s n))) :=
      congrArg (fun z => f * φ.appTop z) (local_powerSection_coefficient U e s n).symm
    _ = endValue (scalarEnd f) * coefficient (restrictFrame φ eₙ)
        (restrictSection φ (restrictSection U.ι (powerSection s n))) :=
      congrArg₂ (· * ·) (endValue_scalarEnd f).symm (coefficient_restrict φ eₙ _).symm
    _ = _ := (coefficient_precompose _ _ _).symm

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.glue_dense_subopens [IsIntegral X] (L : LineBundle X)
    (D : X.Opens) {ι : Type*} [Nonempty ι] (U W : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (hWU : ∀ i, W i ≤ U i) (hWD : ∀ i, W i ≤ D)
    (hW : ∀ i, (W i : Set X).Nonempty)
    (sf : ∀ i, Γ(L.sheaf, U i)) (target : Γ(L.sheaf, D))
    (heq : ∀ i, L.sheaf.presheaf.map (homOfLE (hWU i)).op (sf i) =
      L.sheaf.presheaf.map (homOfLE (hWD i)).op target) :
    ∃! g : Γ(L.sheaf, ⊤),
      (∀ i, L.sheaf.presheaf.map (homOfLE le_top).op g = sf i) ∧
        L.sheaf.presheaf.map (homOfLE le_top).op g = target := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨L.sheaf.presheaf, L.sheaf.isSheaf⟩
  have hc : TopCat.Presheaf.IsCompatible L.sheaf.presheaf U sf := by
    intro i j
    have : Nonempty (W i ⊓ W j : X.Opens) := by
      obtain ⟨x, hi, hj⟩ := nonempty_preirreducible_inter (W i).isOpen (W j).isOpen
        (hW i) (hW j)
      exact ⟨⟨x, hi, hj⟩⟩
    apply L.restriction_injective (homOfLE
      (show W i ⊓ W j ≤ U i ⊓ U j from fun _ hx => ⟨hWU i hx.1, hWU j hx.2⟩))
    have hi := congrArg (L.sheaf.presheaf.map (infLELeft (W i) (W j)).op) (heq i)
    have hj := congrArg (L.sheaf.presheaf.map (infLERight (W i) (W j)).op) (heq j)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hi hj ⊢
    exact hi.trans hj.symm
  obtain ⟨g, hg, hguniq⟩ := F.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) hcover sf hc
  have hD : L.sheaf.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op g = target := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have : Nonempty (W i) := by obtain ⟨x, hx⟩ := hW i; exact ⟨⟨x, hx⟩⟩
    apply L.restriction_injective (homOfLE (hWD i))
    have hi : L.sheaf.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op g = sf i := hg i
    have hgi := congrArg (L.sheaf.presheaf.map (homOfLE (hWU i)).op) hi
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hgi ⊢
    exact hgi.trans (heq i)
  exact ⟨g, ⟨hg, hD⟩, fun g' h' => hguniq g' h'.1⟩

end
end MaximalSeshadri.Geometry


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

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]

lemma specializedTaylor_coeff (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n)
    (ρ : S →ₐ[F] F) (s : S) (d : JetIndex σ n) :
    polynomialJetEquiv n (specializeTaylor n τ ρ s) d =
      ρ (regularTaylorCoeffs n τ s d) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (τ s)
  change polynomialJetEquiv n (mapJetAlgebra ρ n (τ s)) d =
    ρ (polynomialJetEquiv n (τ s) d)
  rw [← hp, mapJetAlgebra_mk, polynomialJetEquiv_mk, polynomialJetEquiv_mk]
  exact coeff_map _ _ _

variable [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

theorem regularTaylor_vanishing_iff [Algebra.FormallyEtale (MvPolynomial σ F) S]
    [Algebra.EssFiniteType (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) (s : S) :
    s ∈ (RingHom.ker ρ)^n ↔ ∀ d, ρ (regularTaylorCoeffs n τ s d) = 0 := by
  rw [← regularTaylor_detects_ideal_power n hn τ hτ hcoord ρ]
  change specializeTaylor n τ ρ s = 0 ↔ _
  rw [← (polynomialJetEquiv (σ := σ) (R := F) n).map_eq_zero_iff]
  rw [funext_iff]
  exact forall_congr' fun d => by rw [specializedTaylor_coeff]; rfl

end

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]
  [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

theorem exists_regular_jet_coeffs (n : ℕ) (hn : 0 < n) :
    ∃ D : S →ₗ[F] (JetIndex σ n → S),
      ∀ (ρ : S →ₐ[F] F) s, s ∈ (RingHom.ker ρ)^n ↔ ∀ d, ρ (D s d) = 0 := by
  obtain ⟨τ, hτ, hcoord⟩ := exists_regular_taylor (σ := σ) (F := F) (S := S) n hn
  exact ⟨regularTaylorCoeffs n τ, regularTaylor_vanishing_iff n hn τ hτ hcoord⟩

end
end MaximalSeshadri.AlgebraicJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PowerExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.finite_cover_power_extension [IsIntegral X] (L : LineBundle X)
    {ι : Type*} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ i, IsAffine (U i).toScheme)
    (hU : ∀ i, (U i : Set X).Nonempty)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ structureSheaf (U i).toScheme)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ(X, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) := by
  classical
  let D := sectionOpen X s
  let V (i : ι) := (U i).toScheme.basicOpen (coefficient (e i) (restrictSection (U i).ι s))
  let W (i : ι) := (U i).ι ''ᵁ V i
  have hV (i : ι) : V i = (U i).ι ⁻¹ᵁ D :=
    (preimage_isoOpen s (U i).ι (e i)).symm
  have hW_eq (i : ι) : W i = U i ⊓ D := by
    simp only [W, hV, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hWU (i : ι) : W i ≤ U i := (U i).ι_image_le (V i)
  have hWD (i : ι) : W i ≤ D := (hW_eq i).le.trans inf_le_right
  have hW (i : ι) : (W i : Set X).Nonempty := by
    rw [hW_eq]
    exact nonempty_preirreducible_inter (U i).isOpen D.isOpen (hU i) hD
  let fi (i : ι) : Γ((V i).toScheme, ⊤) :=
    (V i).topIso.inv (((U i).ι.appIso (V i)).hom (X.presheaf.map (homOfLE (hWD i)).op f))
  have hf (i : ι) : ∃ N : ℕ, ∀ n ≥ N,
      ∃ t : structureSheaf (U i).toScheme ⟶ (modulePow X L.sheaf n).restrict (U i).ι,
        restrictSection (V i).ι t = scalarEnd (fi i) ≫
          restrictSection (V i).ι (restrictSection (U i).ι (powerSection s n)) := by
    let := haff i
    exact local_affine_power_extension (U i) (e i) s (fi i)
  choose N hN using hf
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n := (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose t ht using fun i => hN i n (hn' i)
  let M := modulePow X L.sheaf n
  let target : Γ((L.pow n).sheaf, D) := f • (powerSection s n).app D (1 : Γ(X, D))
  have heq (i : ι) : M.presheaf.map (homOfLE (hWU i)).op (openSectionEquiv M (U i) (t i)) =
      M.presheaf.map (homOfLE (hWD i)).op target := by
    have hi := image_section_extension M (U i) (restrictSection (U i).ι (powerSection s n))
      (t i) (V i) (fi i) (ht i)
    have hfi : ((U i).ι.appIso (V i)).inv ((V i).topIso.hom (fi i)) =
        X.presheaf.map (homOfLE (hWD i)).op f := by
      dsimp only [fi]
      rw [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply]
    rw [hfi] at hi
    have hp : openSectionEquiv M (U i) (restrictSection (U i).ι (powerSection s n)) =
        (powerSection s n).app (U i) (1 : Γ(X, U i)) := openSectionEquiv_restrict _ _
    have hs : M.presheaf.map (homOfLE (hWU i)).op
        (openSectionEquiv M (U i) (restrictSection (U i).ι (powerSection s n))) =
        (powerSection s n).app (W i) (1 : Γ(X, W i)) :=
      (congrArg (M.presheaf.map (homOfLE (hWU i)).op) hp).trans
        (section_value_natural (powerSection s n) (homOfLE (hWU i)))
    have hr : M.presheaf.map (homOfLE (hWD i)).op target =
        X.presheaf.map (homOfLE (hWD i)).op f •
          (powerSection s n).app (W i) (1 : Γ(X, W i)) :=
      (M.map_smul (homOfLE (hWD i)) f _).trans
        (congrArg (X.presheaf.map (homOfLE (hWD i)).op f • ·)
          (section_value_natural (powerSection s n) (homOfLE (hWD i))))
    exact (hi.trans (congrArg (X.presheaf.map (homOfLE (hWD i)).op f • ·) hs)).trans hr.symm
  obtain ⟨g, hg, -⟩ := (L.pow n).glue_dense_subopens D U W hcover hWU hWD hW
    (fun i => openSectionEquiv M (U i) (t i)) target heq
  refine ⟨(moduleSectionEquiv M).symm g, ?_⟩
  have H := section_value_natural ((moduleSectionEquiv M).symm g)
    (homOfLE (show D ≤ ⊤ from le_top))
  have Htop : ((moduleSectionEquiv M).symm g).app ⊤ (1 : Γ(X, ⊤)) = g :=
    (moduleSectionEquiv M).apply_symm_apply g
  rw [Htop] at H
  exact H.symm.trans hg.2

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.power_extension [IsIntegral X] [CompactSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ(X, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) := by
  classical
  choose U hUx he using InvertibleLocal.affine_frame L
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x).1 : X → Set X) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  have hic (x : X) : ∃ i ∈ I, x ∈ (U i).1 := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hi, hx⟩
  have : Nonempty I := by
    obtain ⟨x, -⟩ := hD
    obtain ⟨i, hi, -⟩ := hic x
    exact ⟨⟨i, hi⟩⟩
  exact L.finite_cover_power_extension (fun i : I => (U i.val).1)
    (by
      intro x _
      obtain ⟨i, hi, hx⟩ := hic x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩)
    (fun i => (U i.val).2) (fun i => ⟨i.val, hUx i.val⟩)
    (fun i => Classical.choice (he i.val)) s hD f

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.common_degree (L : LineBundle X) {ι : Type} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (s : ∀ i, GlobalSections X (modulePow X L.sheaf (d i))) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : ι → GlobalSections X (modulePow X L.sheaf n),
      ∀ i, sectionOpen X (t i) = sectionOpen X (s i) := by
  classical
  let n := ∏ i, d i
  have hn : 0 < n := Finset.prod_pos (fun i _ => hd i)
  have hdiv (i : ι) : d i ∣ n := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have heq (i : ι) : d i * (n / d i) = n := Nat.mul_div_cancel' (hdiv i)
  let e (i : ι) : modulePow X (modulePow X L.sheaf (d i)) (n / d i) ≅
      modulePow X L.sheaf n :=
    linePowerMul L (d i) (n / d i) ≪≫ eqToIso (congrArg (modulePow X L.sheaf) (heq i))
  refine ⟨n, hn, fun i => powerSection (s i) (n / d i) ≫ (e i).hom, ?_⟩
  intro i
  change SectionOpens.isoOpen (powerSection (s i) (n / d i) ≫ (e i).hom) = _
  rw [SectionOpens.isoOpen_postcomp]
  exact (L.pow (d i)).sectionOpen_power (s i)
    (Nat.div_pos (Nat.le_of_dvd hn (hdiv i)) (hd i))

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FramedMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme}

lemma isIso_restricted_section {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : SectionOpens.isoOpen s = U) : IsIso (restrictSection U.ι s) := by
  subst U
  exact (sectionFrame s).isIso_inv

theorem LineBundle.power_extension_ratio [IsIntegral X] [CompactSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ((sectionOpen X s).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      restrictSection (sectionOpen X s).ι t = scalarEnd f ≫
        restrictSection (sectionOpen X s).ι (powerSection s n) := by
  obtain ⟨N, hN⟩ := L.power_extension s hD ((sectionOpen X s).topIso.hom f)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨t, ht⟩ := hN n hn
  refine ⟨t, ?_⟩
  apply (openSectionEquiv (modulePow X L.sheaf n) (sectionOpen X s)).injective
  erw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict]
  exact ht

lemma coefficient_ratio {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ O U.toScheme) (s t : O X ⟶ M)
    (f : Γ(U.toScheme, ⊤)) (hs : coefficient e (restrictSection U.ι s) = 1)
    (ht : restrictSection U.ι t = scalarEnd f ≫ restrictSection U.ι s) :
    coefficient e (restrictSection U.ι t) = f := by
  rw [ht]
  change endValue (scalarEnd f ≫ restrictSection U.ι s ≫ e.hom) = f
  rw [endValue_comp, endValue_scalarEnd]
  change f * coefficient e (restrictSection U.ι s) = f
  rw [hs, mul_one]

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_MixedLocalExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

attribute [local instance] MaximalSeshadri.TensorPure.sectionModule

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma section_apply {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) (U : X.Opens) :
    (tensorSection s t).app U (1 : Γ(X,U)) = pure M N U (s.app U (1 : Γ(X,U))) (t.app U (1 : Γ(X,U))) := by
  have h : (moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U)) =
      pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U)) := by
    have he := unit_pure (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))
    have he : (moduleTensorUnit (O X)).hom.app U (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = (1 : Γ(X,U)) := by
      exact he.trans (show (1 : Γ(X,U)) * 1 = 1 from one_mul _)
    have hi := congrArg ((moduleTensorUnit (O X)).inv.app U) he
    change ((moduleTensorUnit (O X)).hom ≫ (moduleTensorUnit (O X)).inv).app U
      (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = _ at hi
    rw [Iso.hom_inv_id] at hi
    exact hi.symm
  change (moduleTensorMap s t).app U ((moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U))) = _
  rw [h]
  exact map_pure s t U (1 : Γ(X,U)) (1 : Γ(X,U))

end
end MaximalSeshadri.TensorPure

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem local_affine_mixed_extension (L M : LineBundle X) (U : X.Opens) [IsAffine U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf)
    (w : Γ(M.sheaf, U.ι ''ᵁ (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O U.toScheme ⟶ (((L.pow n).tensor M).sheaf.restrict U.ι),
      let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
      (((L.pow n).tensor M).sheaf).presheaf.map (homOfLE (U.ι_image_le V)).op
        (openSectionEquiv _ U t) =
      pure (L.pow n).sheaf M.sheaf (U.ι ''ᵁ V) ((powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) w := by
  let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let b : Γ(U.toScheme,V) := d.hom.app V w
  let f : Γ(V.toScheme,⊤) := V.topIso.inv b
  obtain ⟨N,hN⟩ := local_affine_power_extension U e s f
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht⟩ := hN n hn
  let q := TensorPure.tensorSection t d.inv ≫ (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv
  refine ⟨q,?_⟩
  change (((L.pow n).tensor M).sheaf).presheaf.map (homOfLE (U.ι_image_le V)).op
    (openSectionEquiv _ U q) = _
  rw [openSectionEquiv_restrict_value (((L.pow n).tensor M).sheaf) U q V]
  have he : t.app V (1 : Γ(U.toScheme,V)) =
      V.topIso.hom f • (restrictSection U.ι (powerSection s n)).app V
        (1 : Γ(U.toScheme,V)) := by
    exact (openSectionEquiv_restrict t V).symm.trans
      ((congrArg (openSectionEquiv ((L.pow n).sheaf.restrict U.ι) V) ht).trans
        ((openSectionEquiv_scalar ((L.pow n).sheaf.restrict U.ι) V f
          (restrictSection V.ι (restrictSection U.ι (powerSection s n)))).trans
            (congrArg (fun sectionValue : Γ((L.pow n).sheaf.restrict U.ι,V) =>
              V.topIso.hom f • sectionValue)
                (openSectionEquiv_restrict (restrictSection U.ι (powerSection s n)) V))))
  have hf : V.topIso.hom f = b := Iso.inv_hom_id_apply _ _
  rw [hf] at he
  have hp : (restrictSection U.ι (powerSection s n)).app V (1 : Γ(U.toScheme,V)) =
      (powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V)) := by
    change (powerSection s n).app (U.ι ''ᵁ V) ((U.ι.appIso V).inv (1 : Γ(U.toScheme,V))) = _
    rw [map_one]
  have he := he.trans (congrArg (fun z : Γ((L.pow n).sheaf.restrict U.ι, V) => (b : Γ(U.toScheme,V)) • z) hp)
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf U.toScheme).mapIso
      (moduleTensorRestrict U (L.pow n).sheaf M.sheaf)).app (op V)).hom).injective
  change (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom.app V
      ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv.app V
        ((TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)))) = _
  have hc : (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom.app V
      ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv.app V
        ((TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)))) = (TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)) := by
    change ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv ≫
      (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom).app V _ = _
    rw [Iso.inv_hom_id]
    rfl
  rw [hc,TensorPure.section_apply t d.inv V]
  refine (congrArg (fun z => pure ((L.pow n).sheaf.restrict U.ι) (M.sheaf.restrict U.ι) V
    z (d.inv.app V (1 : Γ(U.toScheme,V)))) he).trans ?_
  refine (pure_smul_left ((L.pow n).sheaf.restrict U.ι) (M.sheaf.restrict U.ι)
    V b _ _).trans ?_
  refine (pure_smul_right ((L.pow n).sheaf.restrict U.ι) (M.sheaf.restrict U.ι)
    V b _ _).symm.trans ?_
  have hd : b • d.inv.app V (1 : Γ(U.toScheme,V)) = w := by
    refine (d.inv.app_smul (U := V) (r := b) (x := (1 : Γ(U.toScheme,V)))).symm.trans ?_
    change d.inv.app V (b * 1 : Γ(U.toScheme,V)) = w
    rw [mul_one]
    change d.inv.app V (d.hom.app V w) = w
    change (d.hom ≫ d.inv).app V w = w
    rw [Iso.hom_inv_id]
    rfl
  refine (congrArg (fun sectionValue : Γ(M.sheaf.restrict U.ι,V) =>
    pure ((L.pow n).sheaf.restrict U.ι) (M.sheaf.restrict U.ι) V
      ((powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) sectionValue) hd).trans ?_
  exact (restrict_pure U (L.pow n).sheaf M.sheaf V _ w).symm

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_MixedGlobalExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem LineBundle.finite_cover_mixed_extension [IsIntegral X] (L M : LineBundle X)
    {ι : Type*} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ i, IsAffine (U i).toScheme) (hU : ∀ i, (U i : Set X).Nonempty)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ O (U i).toScheme)
    (d : ∀ i, M.sheaf.restrict (U i).ι ≅ O (U i).toScheme)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow n).tensor M).sheaf,
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow n).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  classical
  let D := sectionOpen X s
  let V (i : ι) := (U i).toScheme.basicOpen (coefficient (e i) (restrictSection (U i).ι s))
  let W (i : ι) := (U i).ι ''ᵁ V i
  have hV (i : ι) : V i = (U i).ι ⁻¹ᵁ D := (preimage_isoOpen s (U i).ι (e i)).symm
  have hW_eq (i : ι) : W i = U i ⊓ D := by
    simp only [W,hV,Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
  have hWU (i : ι) : W i ≤ U i := (U i).ι_image_le (V i)
  have hWD (i : ι) : W i ≤ D := (hW_eq i).le.trans inf_le_right
  have hW (i : ι) : (W i : Set X).Nonempty := by
    rw [hW_eq]
    exact nonempty_preirreducible_inter (U i).isOpen D.isOpen (hU i) hD
  let wi (i : ι) : Γ(M.sheaf,W i) := M.sheaf.presheaf.map (homOfLE (hWD i)).op w
  have hh (i : ι) := @local_affine_mixed_extension X L M (U i) (haff i) (e i) (d i) s (wi i)
  choose N hN using hh
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n := (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose t ht using fun i => hN i n (hn' i)
  let P := ((L.pow n).tensor M)
  let target : Γ(P.sheaf,D) := pure (L.pow n).sheaf M.sheaf D
    ((powerSection s n).app D (1 : Γ(X,D))) w
  have heq (i : ι) : P.sheaf.presheaf.map (homOfLE (hWU i)).op
      (openSectionEquiv P.sheaf (U i) (t i)) =
      P.sheaf.presheaf.map (homOfLE (hWD i)).op target := by
    refine (ht i).trans ?_
    have hr := pure_restrict (L.pow n).sheaf M.sheaf (homOfLE (hWD i))
      ((powerSection s n).app D (1 : Γ(X,D))) w
    have hp := section_value_natural (powerSection s n) (homOfLE (hWD i))
    exact (congrArg (fun z => pure (L.pow n).sheaf M.sheaf (W i) z (wi i)) hp).symm.trans hr.symm
  obtain ⟨g,hg,-⟩ := P.glue_dense_subopens D U W hcover hWU hWD hW
    (fun i => openSectionEquiv P.sheaf (U i) (t i)) target heq
  refine ⟨(moduleSectionEquiv P.sheaf).symm g,?_⟩
  have H := section_value_natural ((moduleSectionEquiv P.sheaf).symm g)
    (homOfLE (show D ≤ ⊤ from le_top))
  have Htop : ((moduleSectionEquiv P.sheaf).symm g).app ⊤ (1 : Γ(X,⊤)) = g :=
    (moduleSectionEquiv P.sheaf).apply_symm_apply g
  rw [Htop] at H
  exact H.symm.trans hg.2

theorem LineBundle.mixed_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow n).tensor M).sheaf,
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow n).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  classical
  choose U hUx he hd using common_affine_frames L M
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x).1 : X → Set X) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hUx x⟩)
  have hic (x : X) : ∃ i ∈ I, x ∈ (U i).1 := by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i,hi,hx⟩
  have : Nonempty I := by
    obtain ⟨x,-⟩ := hD
    obtain ⟨i,hi,-⟩ := hic x
    exact ⟨⟨i,hi⟩⟩
  exact L.finite_cover_mixed_extension M (fun i : I => (U i.val).1)
    (by intro x _; obtain ⟨i,hi,hx⟩ := hic x; exact Opens.mem_iSup.mpr ⟨⟨i,hi⟩,hx⟩)
    (fun i => (U i.val).2) (fun i => ⟨i.val,hUx i.val⟩)
    (fun i => Classical.choice (he i.val)) (fun i => Classical.choice (hd i.val)) s hD w

end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorAssocPure
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

attribute [local instance] sectionModule

lemma assoc_pure (L M N : LineBundle X) (U : X.Opens)
    (l : Γ(L.sheaf,U)) (m : Γ(M.sheaf,U)) (n : Γ(N.sheaf,U)) :
    (lineTensorAssoc L M N).hom.val.app (op U)
      (pure (moduleTensor X L.sheaf M.sheaf) N.sheaf U (pure L.sheaf M.sheaf U l m) n) =
      pure L.sheaf (moduleTensor X M.sheaf N.sheaf) U l (pure M.sheaf N.sheaf U m n) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let P := L.sheaf.val ⊗ M.sheaf.val
  let Q := M.sheaf.val ⊗ N.sheaf.val
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let a := (lineTensorAssoc L M N)
  let v := ((adj X).unit.app (P ⊗ N.sheaf.val)).app (op U)
    ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)
  have hr : (sheafificationTensorRight P N).hom.val.app (op U) v =
      pure (moduleTensor X L.sheaf M.sheaf) N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
    have h := (adj X).unit.naturality
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
        ((adj X).unit.app P) (𝟙 N.sheaf.val))
    exact (congrArg (fun q => q.app (op U) ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)) h).symm
  have ha : (F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom).val.app (op U) v =
      ((adj X).unit.app (L.sheaf.val ⊗ Q)).app (op U)
        (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n)) := by
    have h := (adj X).unit.naturality (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom
    exact (congrArg (fun q => q.app (op U) ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)) h).symm
  have hl : (sheafificationTensorLeft Q L).hom.val.app (op U)
      (((adj X).unit.app (L.sheaf.val ⊗ Q)).app (op U)
        (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n))) =
      pure L.sheaf (moduleTensor X M.sheaf N.sheaf) U l (pure M.sheaf N.sheaf U m n) := by
    have h := (adj X).unit.naturality
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
        (𝟙 L.sheaf.val) ((adj X).unit.app Q))
    exact (congrArg (fun q => q.app (op U) (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n))) h).symm
  change a.hom.val.app (op U) _ = _
  have hc : a.hom.val.app (op U) ((sheafificationTensorRight P N).hom.val.app (op U) v) =
      (sheafificationTensorLeft Q L).hom.val.app (op U)
        ((F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom).val.app (op U) v) := by
    have cancel := (sheafificationTensorRight P N).hom_inv_id_assoc
      (F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom ≫
        (sheafificationTensorLeft Q L).hom)
    exact congrArg (fun morphism : F.obj (P ⊗ N.sheaf.val) ⟶
        moduleTensor X L.sheaf (moduleTensor X M.sheaf N.sheaf) =>
      morphism.val.app (op U) v) cancel
  exact (congrArg (a.hom.val.app (op U)) hr).symm.trans (hc.trans ((congrArg
    ((sheafificationTensorLeft Q L).hom.val.app (op U)) ha).trans hl))

lemma assoc_inv_pure (L M N : LineBundle X) (U : X.Opens)
    (l : Γ(L.sheaf,U)) (m : Γ(M.sheaf,U)) (n : Γ(N.sheaf,U)) :
    (lineTensorAssoc L M N).inv.app U
      (pure L.sheaf (moduleTensor X M.sheaf N.sheaf) U l (pure M.sheaf N.sheaf U m n)) =
      pure (moduleTensor X L.sheaf M.sheaf) N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
  have h := congrArg ((lineTensorAssoc L M N).inv.app U) (assoc_pure L M N U l m n)
  have hc : (lineTensorAssoc L M N).inv.app U
      ((lineTensorAssoc L M N).hom.val.app (op U)
        (pure (moduleTensor X L.sheaf M.sheaf) N.sheaf U (pure L.sheaf M.sheaf U l m) n)) =
      pure (moduleTensor X L.sheaf M.sheaf) N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
    change ((lineTensorAssoc L M N).hom ≫ (lineTensorAssoc L M N).inv).app U _ = _
    rw [Iso.hom_inv_id]
    rfl
  exact h.symm.trans hc

end
end MaximalSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorOpenSection
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma openSection_tensor (M N : X.Modules) (U : X.Opens)
    (s : O U.toScheme ⟶ M.restrict U.ι) (t : O U.toScheme ⟶ N.restrict U.ι) :
    openSectionEquiv (moduleTensor X M N) U
      (tensorSection s t ≫ (moduleTensorRestrict U M N).inv) =
    pure M N U (openSectionEquiv M U s) (openSectionEquiv N U t) := by
  change (moduleTensor X M N).presheaf.map (eqToHom U.ι_image_top.symm).op
    ((moduleTensorRestrict U M N).inv.app ⊤ ((tensorSection s t).app ⊤ (1 : Γ(U.toScheme,⊤)))) = _
  have h := (congrArg ((moduleTensorRestrict U M N).inv.app ⊤)
    (section_apply s t ⊤)).trans (restrict_pure_inv U M N ⊤ _ _)
  exact (congrArg ((moduleTensor X M N).presheaf.map (eqToHom U.ι_image_top.symm).op) h).trans
    (pure_restrict M N (eqToHom U.ι_image_top.symm) _ _)

lemma mixed_value_restrict {M N : X.Modules} (U : X.Opens) (a : O X ⟶ M)
    (b : O U.toScheme ⟶ N.restrict U.ι) (t : O X ⟶ moduleTensor X M N)
    (ht : t.app U (1 : Γ(X,U)) = pure M N U (a.app U (1 : Γ(X,U))) (openSectionEquiv N U b)) :
    restrictSection U.ι t = tensorSection (restrictSection U.ι a) b ≫ (moduleTensorRestrict U M N).inv := by
  apply (openSectionEquiv (moduleTensor X M N) U).injective
  rw [openSectionEquiv_restrict,openSection_tensor,openSectionEquiv_restrict]
  exact ht

lemma mixed_value_open {M N : X.Modules} (U : X.Opens) (a : O X ⟶ M)
    (b : O U.toScheme ⟶ N.restrict U.ι) [IsIso (restrictSection U.ι a)] [IsIso b]
    (t : O X ⟶ moduleTensor X M N)
    (ht : t.app U (1 : Γ(X,U)) = pure M N U (a.app U (1 : Γ(X,U))) (openSectionEquiv N U b)) :
    U ≤ SectionOpens.isoOpen t := by
  have hi : IsIso (restrictSection U.ι t) := by
    rw [mixed_value_restrict U a b t ht]
    infer_instance
  intro x hx
  apply (SectionOpens.mem_isoOpen_iff t x).mpr
  refine ⟨U,hx,?_⟩
  let unitIso : (Scheme.Modules.restrictFunctor U.ι).obj (O X) ≅ O U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  exact (isIso_comp_left_iff unitIso.inv
    ((Scheme.Modules.restrictFunctor U.ι).map t)).mp hi

end
end MaximalSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorPowerPure
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma unit_inv_apply (M : X.Modules) (U : X.Opens) (m : Γ(M,U)) :
    (moduleTensorUnit M).inv.app U m = pure (O X) M U (1 : Γ(X,U)) m := by
  have h := congrArg ((moduleTensorUnit M).inv.app U) (unit_pure M U (1 : Γ(X,U)) m)
  have hc : (moduleTensorUnit M).inv.app U
      ((moduleTensorUnit M).hom.app U (pure (O X) M U (1 : Γ(X,U)) m)) =
      pure (O X) M U (1 : Γ(X,U)) m := by
    change ((moduleTensorUnit M).hom ≫ (moduleTensorUnit M).inv).app U _ = _
    rw [Iso.hom_inv_id]
    rfl
  exact (congrArg ((moduleTensorUnit M).inv.app U) (one_smul Γ(X,U) m)).symm.trans (h.symm.trans hc)

lemma power_succ_apply {M : X.Modules} (s : O X ⟶ M) (n : ℕ) (U : X.Opens) :
    (powerSection s (n+1)).app U (1 : Γ(X,U)) =
      pure M (modulePow X M n) U (s.app U (1 : Γ(X,U)))
        ((powerSection s n).app U (1 : Γ(X,U))) := by
  change (moduleTensorMap s (modulePowMap s n)).app U
    ((moduleTensorUnit (modulePow X (O X) n)).inv.app U
      ((unitPowerIso n).inv.app U (1 : Γ(X,U)))) = _
  exact (congrArg ((moduleTensorMap s (modulePowMap s n)).app U)
    (unit_inv_apply _ U _)).trans (map_pure _ _ U _ _)

end
end MaximalSeshadri.TensorPure

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorFramePure
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma framed_pure {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorIso e d ≪≫ moduleTensorUnit (O X)).hom.app U (pure M N U m n) =
      (show Γ(X,U) from e.hom.app U m) * (show Γ(X,U) from d.hom.app U n) := by
  change (moduleTensorUnit (O X)).hom.app U ((moduleTensorMap e.hom d.hom).app U
    (pure M N U m n)) = _
  exact (congrArg (fun tensorSection => (moduleTensorUnit (O X)).hom.app U tensorSection)
    (map_pure e.hom d.hom U m n)).trans
      (unit_pure (O X) U (e.hom.app U m) (d.hom.app U n))

lemma local_framed_pure (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (V : U.toScheme.Opens) (m : L.sheaf.val.obj (op (U.ι ''ᵁ V)))
    (n : M.sheaf.val.obj (op (U.ι ''ᵁ V))) :
    (tensorFrame L M U e d).hom.app V (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n) =
      (show Γ(U.toScheme,V) from e.hom.app V m) * (show Γ(U.toScheme,V) from d.hom.app V n) := by
  change (moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V
    ((moduleTensorRestrict U L.sheaf M.sheaf).hom.app V
      (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n)) = _
  exact (congrArg (fun tensorSection =>
    (moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V tensorSection)
    (restrict_pure U L.sheaf M.sheaf V m n)).trans (framed_pure e d V m n)

end
end MaximalSeshadri.TensorPure

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorSectionOpen
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

lemma local_section_coefficient (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    coefficient (tensorFrame L M U e d) (restrictSection U.ι (tensorSection s t)) =
      coefficient e (restrictSection U.ι s) * coefficient d (restrictSection U.ι t) := by
  change (tensorFrame L M U e d).hom.app ⊤
    ((tensorSection s t).app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ (s.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))))) *
    (show Γ(U.toScheme,⊤) from d.hom.app ⊤ (t.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))))
  rw [map_one]
  exact (congrArg (fun value => (tensorFrame L M U e d).hom.app ⊤ value)
    (section_apply s t _)).trans
    (local_framed_pure L M U e d ⊤ _ _)

lemma section_open (L M : LineBundle X) (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    isoOpen (tensorSection s t) = isoOpen s ⊓ isoOpen t := by
  apply SetLike.coe_injective
  ext x
  obtain ⟨U,hx,⟨e⟩,⟨d⟩⟩ := common_affine_frames L M x
  have h : U.1.ι ⁻¹ᵁ isoOpen (tensorSection s t) =
      U.1.ι ⁻¹ᵁ (isoOpen s ⊓ isoOpen t) := by
    refine (preimage_isoOpen (tensorSection s t) U.1.ι (tensorFrame L M U.1 e d)).trans ?_
    refine (congrArg (fun value : Γ(U.1.toScheme,⊤) => U.1.toScheme.basicOpen value)
      (local_section_coefficient L M U.1 e d s t)).trans ?_
    rw [Scheme.basicOpen_mul]
    change _ = (U.1.ι ⁻¹ᵁ isoOpen s) ⊓ (U.1.ι ⁻¹ᵁ isoOpen t)
    exact congrArg₂ (fun left right : U.1.toScheme.Opens => left ⊓ right)
      (preimage_isoOpen s U.1.ι e).symm (preimage_isoOpen t U.1.ι d).symm
  exact SetLike.ext_iff.mp h ⟨x,hx⟩

end
end MaximalSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_MixedDivisibleExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem LineBundle.divisible_mixed_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t ≤ sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  obtain ⟨N,hN⟩ := L.mixed_extension M s hD w
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht⟩ := hN n hn
  let q : O X ⟶ ((L.pow (n+1)).tensor M).sheaf :=
    tensorSection s t ≫ (lineTensorAssoc L (L.pow n) M).inv
  refine ⟨q,?_,?_⟩
  · change SectionOpens.isoOpen (tensorSection s t ≫ (lineTensorAssoc L (L.pow n) M).symm.hom) ≤ _
    exact (SectionOpens.isoOpen_postcomp (tensorSection s t)
      (lineTensorAssoc L (L.pow n) M).symm).le.trans
      ((section_open L ((L.pow n).tensor M) s t).le.trans inf_le_left)
  · let D := sectionOpen X s
    change (lineTensorAssoc L (L.pow n) M).inv.app D ((tensorSection s t).app D (1 : Γ(X,D))) = _
    have h := (section_apply s t D).trans
      (congrArg (pure L.sheaf ((L.pow n).tensor M).sheaf D (s.app D (1 : Γ(X,D)))) ht)
    exact (congrArg (fun sectionValue =>
      (lineTensorAssoc L (L.pow n) M).inv.app D sectionValue) h).trans
      ((assoc_inv_pure L (L.pow n) M D _ _ w).trans
       (congrArg (fun z => pure (L.pow (n+1)).sheaf M.sheaf D z w) (power_succ_apply s n D).symm))

theorem LineBundle.mixed_frame_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (e : M.sheaf.restrict (sectionOpen X s).ι ≅ O (sectionOpen X s).toScheme) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t = sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)))
          (openSectionEquiv M.sheaf (sectionOpen X s) e.inv) := by
  obtain ⟨N,hN⟩ := L.divisible_mixed_extension M s hD
    (openSectionEquiv M.sheaf (sectionOpen X s) e.inv)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht,hv⟩ := hN n hn
  refine ⟨t,le_antisymm ht ?_,hv⟩
  have hi : IsIso (restrictSection (sectionOpen X s).ι (powerSection s (n+1))) := by
    have hs := L.sectionOpen_power s (by omega : 0 < n+1)
    exact isIso_restricted_section _ _ hs
  exact mixed_value_open (sectionOpen X s) (powerSection s (n+1)) e.inv t hv

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AmpleFramedCover
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

theorem LineBundle.ample_framed_cover [CompactSpace X] (L M : LineBundle X)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ d : ℕ, 0 < d ∧ a ∣ d ∧ ∃ ι : Type, ∃ _ : Fintype ι,
      ∃ s : ι → GlobalSections X (L.pow d).sheaf,
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) ∧
        (∀ i, Nonempty (M.sheaf.restrict (sectionOpen X (s i)).ι ≅ O (sectionOpen X (s i)).toScheme)) := by
  classical
  choose V hV e using M.locallyRankOne
  have hh (x : X) := hL x (V x) (hV x)
  choose d hd s hs hsub haff using hh
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hs x⟩)
  obtain ⟨n,hn,t,ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let f := linePowerMul L n a
  let q (i : I) : GlobalSections X (L.pow (n*a)).sheaf :=
    powerSection (t i) a ≫ f.hom
  have hq (i : I) : sectionOpen X (q i) = sectionOpen X (s i.val) := by
    change SectionOpens.isoOpen (powerSection (t i) a ≫ f.hom) = _
    exact (SectionOpens.isoOpen_postcomp (powerSection (t i) a) f).trans
      (((L.pow n).sectionOpen_power (t i) ha).trans (ht i))
  refine ⟨n*a,Nat.mul_pos hn ha,dvd_mul_left a n,I,inferInstance,q,?_,?_,?_,?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    refine Opens.mem_iSup.mpr ⟨⟨i,hi⟩,?_⟩
    rw [hq]
    exact hx
  · intro i
    rw [hq]
    exact haff i.val
  · intro i
    rw [hq]
    exact ⟨i.val,hs i.val⟩
  · intro i
    exact ⟨frameOnSmaller (Classical.choice (e i.val)) (sectionOpen X (q i)) ((hq i).le.trans (hsub i.val))⟩

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_QuadraticSequence
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.EulerNumerics

lemma periodic_nat_gcd {α : Type*} (f : ℕ → α) (a b : ℕ)
    (ha : Function.Periodic f a) (hb : Function.Periodic f b) :
    Function.Periodic f (Nat.gcd a b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases hz : a = 0
    · simpa [hz] using hb
    have hm : Function.Periodic f (b % a) := by
      intro n
      have H := ha.nat_mul (b/a) (n+b%a)
      rw [Nat.cast_id, Nat.add_assoc,Nat.mod_add_div'] at H
      exact H.symm.trans (hb n)
    rw [Nat.gcd_rec]
    exact ih (b%a) (Nat.mod_lt b (Nat.pos_of_ne_zero hz)) a hm ha

lemma periodic_nat_coprime_constant {α : Type*} (f : ℕ → α) (a b : ℕ)
    (hab : Nat.Coprime a b) (ha : Function.Periodic f a)
    (hb : Function.Periodic f b) (n : ℕ) : f n = f 0 := by
  have H := periodic_nat_gcd f a b ha hb
  rw [hab.gcd_eq_one] at H
  simpa only [Nat.cast_id,mul_one] using H.nat_mul_eq n

theorem quadratic_of_coprime_differences (f : ℕ → ℤ) (a b : ℕ)
    (hab : Nat.Coprime a b) (d e c h : ℤ)
    (ha : ∀ n, f (n+a) - f n = (n : ℤ)*d+c)
    (hb : ∀ n, f (n+b) - f n = (n : ℤ)*e+h) (n : ℕ) :
    2*f n = (n : ℤ)*((n : ℤ)-1)*(f 2-2*f 1+f 0) +
      2*(n : ℤ)*(f 1-f 0)+2*f 0 := by
  let g (n : ℕ) := f (n+2)-2*f (n+1)+f n
  have periodic (a : ℕ) (d c : ℤ)
      (ha : ∀ n, f (n+a)-f n = (n : ℤ)*d+c) : Function.Periodic g a := by
    intro n
    have H₀ := ha n
    have H₁ := ha (n+1)
    have H₂ := ha (n+2)
    dsimp [g]
    rw [show n+a+2 = n+2+a by omega,show n+a+1 = n+1+a by omega]
    push_cast at H₁ H₂
    nlinarith
  have hg (n : ℕ) : g n = f 2-2*f 1+f 0 :=
    periodic_nat_coprime_constant g a b hab (periodic a d c ha) (periodic b e h hb) n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp <;> ring
  | more n hn hn₁ =>
    have H := hg n
    dsimp [g] at H
    push_cast at hn₁ ⊢
    nlinarith

end MaximalSeshadri.EulerNumerics

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceQuadraticEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

lemma Surface.euler_power_one (S : Surface) (L : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 (L.pow 1).sheaf =
      eulerCharacteristic S.structureMap 2 L.sheaf :=
  eulerCharacteristic_iso S.structureMap (moduleTensorRightUnit L.sheaf) 2

lemma Surface.euler_power_second_difference (S : Surface) (L : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 (L.pow 2).sheaf -
      2*eulerCharacteristic S.structureMap 2 (L.pow 1).sheaf +
      eulerCharacteristic S.structureMap 2 (L.pow 0).sheaf = selfIntersection S L := by
  rw [S.euler_power_one]
  rfl

theorem Surface.power_euler_quadratic (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (n : ℕ) :
    2*eulerCharacteristic S.structureMap 2 (L.pow n).sheaf =
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) := by
  classical
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  obtain ⟨a,ha,-,N,s,hs,v,hne,hi,hd⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  obtain ⟨b,hb,hab,N',s',hs',v',hne',hi',hd'⟩ := S.coprime_integral_section_s01 L hL a ha
  let := hi'
  let D : IntegralCurve S := ⟨(sectionIdeal k s' hs' v').subscheme,
      (sectionIdeal k s' hs' v').subschemeι,inferInstance,inferInstance,hd'⟩
  have ha' (m : ℕ) : f (m+a)-f m = (m : ℤ)*curveDegree S L C +
      ((a : ℤ)*curveDegree S L C+eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)) := by
    have H := generated_power_euler_difference_s01 S L hL L a k s hs v hne hd m
    change f (m+a)-f m = _ at H
    push_cast at H
    linarith
  have hb' (m : ℕ) : f (m+b)-f m = (m : ℤ)*curveDegree S L D +
      ((b : ℤ)*curveDegree S L D+eulerCharacteristic (D.embedding ≫ S.structureMap) 1 (O D.scheme)) := by
    have H := generated_power_euler_difference_s01 S L hL L b k s' hs' v' hne' hd' m
    change f (m+b)-f m = _ at H
    push_cast at H
    linarith
  have H := EulerNumerics.quadratic_of_coprime_differences f a b hab _ _ _ _ ha' hb' n
  have hq := S.euler_power_second_difference L
  have h1 := S.euler_power_one L
  change f 2-2*f 1+f 0 = selfIntersection S L at hq
  change f 1 = _ at h1
  rw [hq,h1] at H
  exact H

end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SurfaceTopGrowth
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

local instance instHasExtModules_solutions_1_r913aef_1 : HasExt.{1} X.Modules := schemeHasExt
lemma cohomologyDimension_iso (p : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    cohomologyDimension p M n = cohomologyDimension p N n := by
  let := Module.compHom (cohomology M n) (baseScalars p)
  let := Module.compHom (cohomology N n) (baseScalars p)
  exact (cohomologyIso p e n).finrank_eq

lemma surface_euler_expansion (S : Surface) (M : S.scheme.Modules) :
    eulerCharacteristic S.structureMap 2 M =
      (cohomologyDimension S.structureMap M 0 : ℤ) -
      (cohomologyDimension S.structureMap M 1 : ℤ) +
      (cohomologyDimension S.structureMap M 2 : ℤ) := by
  simp [eulerCharacteristic,Finset.sum_range_succ,sub_eq_add_neg]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_AmpleFromCover
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem LineBundle.section_basicOpen [IsIntegral X] [CompactSpace X]
    (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (hne : (sectionOpen X s : Set X).Nonempty) (f : Γ(X,sectionOpen X s)) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : O X ⟶ (L.pow n).sheaf,
      sectionOpen X t = X.basicOpen f := by
  let U := sectionOpen X s
  obtain ⟨N,hN⟩ := L.power_extension_ratio s hne (U.topIso.inv f)
  let n := max N 1
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0<1) (le_max_right N 1)
  obtain ⟨t,ht⟩ := hN n (le_max_left N 1)
  let q := tensorSection s t
  have hsub : SectionOpens.isoOpen q ≤ U := by
    exact (section_open L (L.pow n) s t).le.trans inf_le_left
  have hi : IsIso (restrictSection U.ι (powerSection s n)) :=
    isIso_restricted_section _ _ (L.sectionOpen_power s hn)
  let e : (L.pow n).sheaf.restrict U.ι ≅ O U.toScheme :=
    (asIso (restrictSection U.ι (powerSection s n))).symm
  have hcoef : coefficient e (restrictSection U.ι t) = U.topIso.inv f := by
    apply coefficient_ratio e (powerSection s n) t
    · exact coefficient_frame e
    · exact ht
  let sectionTrivialization : L.sheaf.restrict U.ι ≅ O U.toScheme := sectionFrame s
  have hnorm : coefficient sectionTrivialization (restrictSection U.ι s) = 1 :=
    sectionFrame_normalized s
  have hpre : U.ι ⁻¹ᵁ SectionOpens.isoOpen q = U.toScheme.basicOpen (U.topIso.inv f) := by
    refine (preimage_isoOpen q U.ι (tensorFrame L (L.pow n) U sectionTrivialization e)).trans ?_
    exact congrArg (fun value : Γ(U.toScheme,⊤) => U.toScheme.basicOpen value)
      ((local_section_coefficient L (L.pow n) U sectionTrivialization e s t).trans
        (by rw [hnorm,hcoef,one_mul]))
  refine ⟨n+1,by omega,q,?_⟩
  change SectionOpens.isoOpen q = _
  calc
    _ = U.ι ''ᵁ (U.ι ⁻¹ᵁ SectionOpens.isoOpen q) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι,inf_eq_right.mpr hsub]
    _ = _ := by rw [hpre,U.ι_image_basicOpen_topIso_inv]

theorem LineBundle.ample_of_affine_section_cover [IsIntegral X] [CompactSpace X]
    (L : LineBundle X) {ι : Type*} (s : ι → (O X ⟶ L.sheaf))
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (ha : ∀ i, IsAffineOpen (sectionOpen X (s i))) : L.IsAmple := by
  intro x V hx
  have hc' : x ∈ ⨆ i, sectionOpen X (s i) := by rw [hc]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hc'
  obtain ⟨f,hf,hxf⟩ := (ha i).exists_basicOpen_le ⟨x,hx⟩ hi
  obtain ⟨n,hn,t,ht⟩ := L.section_basicOpen (s i) ⟨x,hi⟩ f
  exact ⟨n,hn,t,ht.symm ▸ hxf,ht.le.trans hf,ht.symm ▸ (ha i).basicOpen f⟩

theorem LineBundle.exists_ample_twist [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ((L.pow d).tensor M).IsAmple := by
  classical
  obtain ⟨a,ha,-,ι,hi,s,hs,hsa,hsn,he⟩ := L.ample_framed_cover M hL 1 (by decide)
  choose N hN using fun i => (L.pow a).mixed_frame_extension M (s i) (hsn i)
    (Classical.choice (he i))
  let n := Finset.univ.sup N
  choose t ht hval using fun i => hN i n (Finset.le_sup (Finset.mem_univ i))
  let e : (((L.pow a).pow (n+1)).tensor M).sheaf ≅ ((L.pow (a*(n+1))).tensor M).sheaf :=
    moduleTensorIso (linePowerMul L a (n+1)) (Iso.refl M.sheaf)
  let q (i : ι) : O X ⟶ ((L.pow (a*(n+1))).tensor M).sheaf := t i ≫ e.hom
  have hq (i : ι) : sectionOpen X (q i) = sectionOpen X (s i) := by
    exact (SectionOpens.isoOpen_postcomp (t i) e).trans (ht i)
  refine ⟨a*(n+1),Nat.mul_pos ha (by omega),
    ((L.pow (a*(n+1))).tensor M).ample_of_affine_section_cover q ?_ ?_⟩
  · simpa only [hq] using hs
  · intro i
    rw [hq]
    exact hsa i
end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_AmplePowers
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

theorem LineBundle.IsAmple.pow {L : LineBundle X} (hL : L.IsAmple) (d : ℕ) (hd : 0 < d) :
    (L.pow d).IsAmple := by
  intro x V hx
  obtain ⟨n,hn,s,hs,hsub,ha⟩ := hL x V hx
  let e : ((L.pow n).pow d).sheaf ≅ ((L.pow d).pow n).sheaf :=
    linePowerMul L n d ≪≫ eqToIso (congrArg (fun j => (L.pow j).sheaf) (Nat.mul_comm n d)) ≪≫
      (linePowerMul L d n).symm
  let t := powerSection s d ≫ e.hom
  have ht : sectionOpen X t = sectionOpen X s := by
    change SectionOpens.isoOpen (powerSection s d ≫ e.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    exact (L.pow n).sectionOpen_power s hd
  refine ⟨n,hn,t,?_,?_,?_⟩ <;> (erw [ht]; assumption)

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_TwistNumerics
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.EulerNumerics

theorem affine_of_coprime_differences (f : ℕ → ℤ) (a b : ℕ)
    (hab : Nat.Coprime a b) (c d : ℤ)
    (ha : ∀ n, f (n+a)-f n=c) (hb : ∀ n, f (n+b)-f n=d) (n : ℕ) :
    f n = (n : ℤ)*(f 1-f 0)+f 0 := by
  let g (n : ℕ) := f (n+1)-f n
  have per (a : ℕ) (c : ℤ) (hh : ∀ n, f (n+a)-f n=c) : Function.Periodic g a := by
    intro n
    dsimp [g]
    have h1 := hh (n+1)
    have h0 := hh n
    rw [show n+1+a = n+a+1 by omega] at h1
    omega
  have hg (n : ℕ) : g n = g 0 := periodic_nat_coprime_constant g a b hab (per a c ha) (per b d hb) n
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hg n
    dsimp [g] at h
    rw [ih] at h
    push_cast
    nlinarith
end MaximalSeshadri.EulerNumerics

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceTwistEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

theorem Surface.twist_euler (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) (n : ℕ) :
    eulerCharacteristic S.structureMap 2 ((L.pow n).tensor M).sheaf =
      eulerCharacteristic S.structureMap 2 (L.pow n).sheaf +
      eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (O S.scheme) + (n : ℤ)*mixedEuler S L M := by
  classical
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 ((L.pow n).tensor M).sheaf -
    eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  have h0 : f 0 = eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (O S.scheme) := by
    change eulerCharacteristic S.structureMap 2 (moduleTensor S.scheme (O S.scheme) M.sheaf) -
      eulerCharacteristic S.structureMap 2 (O S.scheme) = _
    exact congrArg (fun z : ℤ => z - eulerCharacteristic S.structureMap 2 (O S.scheme))
      (eulerCharacteristic_iso S.structureMap (moduleTensorUnit M.sheaf) 2)
  have h1 : f 1 - f 0 = mixedEuler S L M := by
    have ht := eulerCharacteristic_iso S.structureMap
      (moduleTensorIso (moduleTensorRightUnit L.sheaf) (Iso.refl M.sheaf)) 2
    change eulerCharacteristic S.structureMap 2 ((L.pow 1).tensor M).sheaf =
      eulerCharacteristic S.structureMap 2 (L.tensor M).sheaf at ht
    dsimp [f] at h0 ⊢
    rw [ht,S.euler_power_one L]
    unfold mixedEuler
    omega
  obtain ⟨a,ha,-,N,s,hs,v,hne,hi,hd⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  obtain ⟨b,hb,hab,N',s',hs',v',hne',hi',hd'⟩ := S.coprime_integral_section_s01 L hL a ha
  let := hi'
  let D : IntegralCurve S := ⟨(sectionIdeal k s' hs' v').subscheme,
      (sectionIdeal k s' hs' v').subschemeι,inferInstance,inferInstance,hd'⟩
  have ha' (m : ℕ) : f (m+a)-f m = curveDegree S M C := by
    have h := generated_twist_euler_difference_s01 S L hL L M a k s hs v hne hd m
    have h' := generated_power_euler_difference_s01 S L hL L a k s hs v hne hd m
    dsimp only [f]
    dsimp only at h h'
    linarith
  have hb' (m : ℕ) : f (m+b)-f m = curveDegree S M D := by
    have h := generated_twist_euler_difference_s01 S L hL L M b k s' hs' v' hne' hd' m
    have h' := generated_power_euler_difference_s01 S L hL L b k s' hs' v' hne' hd' m
    dsimp only [f]
    dsimp only at h h'
    linarith
  have H := EulerNumerics.affine_of_coprime_differences f a b hab _ _ ha' hb' n
  rw [h1,h0] at H
  dsimp only [f] at H
  omega

end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfacePositiveSquare
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

lemma quadratic_lower_eventually_pos (q l c : ℤ) (hq : 0 < q) (B : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      0 < (n : ℤ)*((n : ℤ)-1)*q + 2*(n : ℤ)*l + 2*c - 2*B := by
  let N := (2*|l|+2*|c|+2*(B : ℤ)+3).toNat
  have hN : (N : ℤ) = 2*|l|+2*|c|+2*(B : ℤ)+3 := Int.toNat_of_nonneg (by positivity)
  refine ⟨N,?_,fun n hn => ?_⟩
  · have : (0 : ℤ) < N := by rw [hN]; positivity
    exact_mod_cast this
  · have hn' : (N : ℤ) ≤ n := by exact_mod_cast hn
    rw [hN] at hn'
    have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    have hB : (0 : ℤ) ≤ B := Nat.cast_nonneg B
    have hq' : 1 ≤ q := hq
    have hbase : 0 ≤ (n : ℤ)*((n : ℤ)-1) := mul_nonneg hn0 (by omega)
    have hmul := mul_le_mul_of_nonneg_left hq' hbase
    have hl := neg_abs_le l
    have hc := neg_abs_le c
    have hlmul := mul_le_mul_of_nonneg_left hl
      (show (0 : ℤ) ≤ 2 * (n : ℤ) by positivity)
    have habsl := abs_nonneg l
    have habsc := abs_nonneg c
    nlinarith

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_GeneralSurfaceH2
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

theorem Surface.power_H2_linear_bound (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hM : 0 ≤ mixedEuler S L M) :
    ∃ B C : ℕ, ∀ n : ℕ, cohomologyDimension S.structureMap (M.pow n).sheaf 2 ≤ B+C*n := by
  classical
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  let P := L.pow d
  have hP : P.IsAmple := hL.pow d hd
  have hdegP : 0 ≤ curveDegree S P C := le_of_lt (C.ample_degree_positive_s01 S P hP)
  have hdegM : 0 ≤ curveDegree S M C := by
    have H := generated_curveDegree_eq_mixedEuler_s01 S L hL M d k s hs v hne hC
    change curveDegree S M C = (d : ℤ)*mixedEuler S L M at H
    rw [H]
    exact mul_nonneg (Nat.cast_nonneg _) hM
  obtain ⟨e,he,hA⟩ := P.exists_ample_twist M hP
  let A := (P.pow e).tensor M
  obtain ⟨B,hB⟩ := S.power_H2_bounded_s01 A hA
  let g := cohomologyDimension (C.embedding ≫ S.structureMap) (O C.scheme) 1
  refine ⟨B,e*g,fun n => ?_⟩
  let T (j : ℕ) := (P.pow j).tensor (M.pow n)
  let f (j : ℕ) := cohomologyDimension S.structureMap (T j).sheaf 2
  have hstep (j : ℕ) : f j ≤ g+f (j+1) := by
    have hdeg : 0 ≤ curveDegree S (P.tensor (T j)) C := by
      rw [curveDegree_tensor_s01 S L hL]
      change 0 ≤ curveDegree S P C + curveDegree S ((P.pow j).tensor (M.pow n)) C
      rw [curveDegree_tensor_s01 S L hL (P.pow j) (M.pow n) C,
        curveDegree_pow_s01 S L hL P C j,curveDegree_pow_s01 S L hL M C n]
      exact add_nonneg hdegP (add_nonneg
        (mul_nonneg (Nat.cast_nonneg _) hdegP) (mul_nonneg (Nat.cast_nonneg _) hdegM))
    have H := generated_section_H2_untwist_s01 S L hL P (T j) k s hs v hne hC hdeg
    let e' : (P.tensor (T j)).sheaf ≅ (T (j+1)).sheaf :=
      (lineTensorAssoc P (P.pow j) (M.pow n)).symm
    have E := cohomologyDimension_iso S.structureMap e' 2
    rw [E] at H
    exact H
  have H (j : ℕ) : f 0 ≤ j*g+f j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := hstep j
      rw [Nat.succ_mul]
      omega
  have E := cohomologyDimension_iso S.structureMap (lineTwistPower P M e n) 2
  change cohomologyDimension S.structureMap (A.pow n).sheaf 2 = f (e*n) at E
  have hlast : f (e*n) ≤ B := E ▸ hB n
  have hzero : f 0 = cohomologyDimension S.structureMap (M.pow n).sheaf 2 :=
    cohomologyDimension_iso S.structureMap (moduleTensorUnit (M.pow n).sheaf) 2
  calc
    cohomologyDimension S.structureMap (M.pow n).sheaf 2 = f 0 := hzero.symm
    _ ≤ (e*n)*g+f (e*n) := H (e*n)
    _ ≤ (e*n)*g+B := Nat.add_le_add_left hlast _
    _ = B+(e*g)*n := by ring

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionGermSystem
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

variable {X : Scheme.{0}}

lemma Surface.sections_finite (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) :
    letI := complexSectionModule S.structureMap M.sheaf
    Module.Finite ℂ (GlobalSections S.scheme M.sheaf) := by
  let := complexSectionModule S.structureMap M.sheaf
  let := Module.compHom (cohomology M.sheaf 0) (baseScalars S.structureMap)
  let := S.H0_finite_s01 L hL M
  let e := Ext.linearEquiv₀ (R := Γ(S.scheme,⊤)) (X := structureSheaf S.scheme) (Y := M.sheaf)
  exact Module.Finite.equiv (show cohomology M.sheaf 0 ≃ₗ[ℂ] GlobalSections S.scheme M.sheaf from
    { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars S.structureMap r) x })

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeneralQuadraticNumerics
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MaximalSeshadri.EulerNumerics

lemma Quadratic.reindex (f : ℕ → ℤ) (hf : Quadratic f) (d : ℕ) :
    Quadratic (fun n => f (d*n)) := by
  intro n
  dsimp only
  have h := hf (d*n)
  have h2 := hf (d*2)
  have h1 := hf (d*1)
  simp only [Nat.mul_zero,Nat.mul_one] at h1 ⊢
  push_cast at h h2 h1
  have H : 2*(2*f (d*n) - ((n : ℤ)*((n : ℤ)-1)*(f (d*2)-2*f d+f 0) +
      2*(n : ℤ)*(f d-f 0)+2*f 0)) = 0 := by
    linear_combination 2*h - ((n : ℤ)*((n : ℤ)-1))*h2 +
      (2*(n : ℤ)*((n : ℤ)-2))*h1
  omega

theorem quadratic_of_twisted (f g h : ℕ → ℤ) (d : ℕ) (c j : ℤ)
    (hg : Quadratic g) (hh : Quadratic h)
    (he : ∀ n : ℕ, f n = g n - h (d*n) + c - (d : ℤ)*(n : ℤ)^2*j) :
    Quadratic f := by
  intro n
  have H := hg n
  have H' := Quadratic.reindex h hh d n
  simp only [Nat.mul_zero,Nat.mul_one] at H'
  rw [he n,he 2,he 1,he 0]
  norm_num only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,zero_pow,one_pow,
    Nat.mul_zero,Nat.mul_one]
  linear_combination H-H'
end MaximalSeshadri.EulerNumerics

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_GeneralSurfaceEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

theorem Surface.arbitrary_power_euler_quadratic (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme) (n : ℕ) :
    2*eulerCharacteristic S.structureMap 2 (M.pow n).sheaf =
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S M +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 M.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) := by
  obtain ⟨d,_,hB⟩ := L.exists_ample_twist M hL
  let B := (L.pow d).tensor M
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 (M.pow n).sheaf
  let g (n : ℕ) := eulerCharacteristic S.structureMap 2 (B.pow n).sheaf
  let h (n : ℕ) := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  have hQ (A : LineBundle S.scheme) (hA : A.IsAmple) :
      EulerNumerics.Quadratic (fun n => eulerCharacteristic S.structureMap 2 (A.pow n).sheaf) := by
    intro j
    dsimp only
    rw [S.euler_power_second_difference A,S.euler_power_one A]
    exact S.power_euler_quadratic A hA j
  have he (j : ℕ) : f j = g j - h (d*j) +
      eulerCharacteristic S.structureMap 2 (O S.scheme) -
      (d : ℤ)*(j : ℤ)^2*mixedEuler S L M := by
    have H := S.twist_euler L hL (M.pow j) (d*j)
    have E := eulerCharacteristic_iso S.structureMap (lineTwistPower L M d j) 2
    change g j = eulerCharacteristic S.structureMap 2 ((L.pow (d*j)).tensor (M.pow j)).sheaf at E
    rw [← E,mixedEuler_pow_right_s01 S L hL] at H
    dsimp only [f,h]
    push_cast at H
    linear_combination -H
  have H := EulerNumerics.quadratic_of_twisted f g h d
    (eulerCharacteristic S.structureMap 2 (O S.scheme)) (mixedEuler S L M)
    (hQ B hB) (hQ L hL) he n
  dsimp only [f] at H
  rw [S.euler_power_second_difference M,S.euler_power_one M] at H
  exact H

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_BinaryJetDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators

lemma card_binaryJet (n : ℕ) :
    2 * Nat.card (JetIndex (Fin 2) n) = n*(n+1) := by
  rw [Nat.card_congr (binaryJetEquiv n)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_fin]
  have h : ∀ n : ℕ, 2 * (∑ i ∈ Finset.range n, (i+1)) = n*(n+1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; nlinarith
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i+1) n]
  exact h n

end
end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_SectionJetDimensions
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.AlgebraicJets MaximalSeshadri.ProjectiveBertini

lemma Surface.sections_finrank (S : Surface) (M : LineBundle S.scheme) :
    letI := complexSectionModule S.structureMap M.sheaf
    Module.finrank ℂ (GlobalSections S.scheme M.sheaf) =
      cohomologyDimension S.structureMap M.sheaf 0 := by
  let := complexSectionModule S.structureMap M.sheaf
  let := Module.compHom (cohomology M.sheaf 0) (baseScalars S.structureMap)
  let e := Ext.linearEquiv₀ (R := Γ(S.scheme,⊤)) (X := structureSheaf S.scheme) (Y := M.sheaf)
  let e' : cohomology M.sheaf 0 ≃ₗ[ℂ] GlobalSections S.scheme M.sheaf :=
    { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars S.structureMap r) x }
  exact e'.finrank_eq.symm

lemma finite_affine_jet_test {A : Type} [CommRing A] [Algebra ℂ A]
    (t : Fin 2 → A) (het : (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (ρ : A →ₐ[ℂ] ℂ) (n : ℕ) :
    ∃ J : A →ₗ[ℂ] (JetIndex (Fin 2) n → ℂ),
      ∀ a, J a = 0 ↔ a ∈ (RingHom.ker ρ)^n := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨0,fun a => ?_⟩
    simp
  let φ := MvPolynomial.aeval (R := ℂ) t
  let := φ.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) A := RingHom.etale_algebraMap.mp het
  obtain ⟨D,hD⟩ := exists_regular_jet_coeffs (σ := Fin 2) (F := ℂ) (S := A) n (Nat.pos_of_ne_zero hn)
  let J : A →ₗ[ℂ] (JetIndex (Fin 2) n → ℂ) :=
    LinearMap.pi fun d => ρ.toLinearMap.comp ((LinearMap.proj d).comp D)
  refine ⟨J,fun a => ?_⟩
  rw [hD ρ a,funext_iff]
  rfl

theorem Surface.exists_section_with_point_orders (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    {r : ℕ} (U : Fin r → S.scheme.affineOpens)
    (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
    (t : ∀ i, Fin 2 → Γ(S.scheme,(U i).1))
    (het : ∀ i, (MvPolynomial.eval₂Hom (openScalars S.structureMap (U i).1) (t i)).Etale)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ) (n : Fin r → ℕ)
    (hd : ∑ i, n i*(n i+1) < 2*cohomologyDimension S.structureMap M.sheaf 0) :
    ∃ s : O S.scheme ⟶ M.sheaf, s ≠ 0 ∧
      ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i) := by
  classical
  let := complexSectionModule S.structureMap M.sheaf
  let := S.sections_finite L hL M
  let (i : Fin r) : Algebra ℂ Γ(S.scheme,(U i).1) := (openScalars S.structureMap (U i).1).toAlgebra
  choose J hJ using fun i => finite_affine_jet_test (t i) (het i) (ρ i) (n i)
  let T : GlobalSections S.scheme M.sheaf →ₗ[ℂ] ((i : Fin r) → JetIndex (Fin 2) (n i) → ℂ) :=
    LinearMap.pi fun i => (J i).comp (affineCoefficientLinear S.structureMap (U i) (e i))
  have hT (s : GlobalSections S.scheme M.sheaf) : T s = 0 ↔
      ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i) := by
    rw [funext_iff]
    exact forall_congr' fun i => hJ i _
  have hdim : 2 * Module.finrank ℂ ((i : Fin r) → JetIndex (Fin 2) (n i) → ℂ) =
      ∑ i, n i*(n i+1) := by
    let (i : Fin r) : Fintype (JetIndex (Fin 2) (n i)) := Fintype.ofFinite _
    rw [Module.finrank_pi_fintype,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Module.finrank_pi]
    simpa only [Nat.card_eq_fintype_card,Finset.card_univ] using card_binaryJet (n i)
  by_contra hnon
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro s hs
    by_contra hn
    exact hnon ⟨s,hn,(hT s).mp hs⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [S.sections_finrank M] at hle
  omega

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_EffectiveJets
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.eventually_effective_with_jets_s01_oai (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hm : 0 ≤ mixedEuler S L M) {r : ℕ} (m : Fin r → ℕ)
    (hq : (∑ i, (m i)^2 : ℕ) < selfIntersection S M)
    (U : Fin r → S.scheme.affineOpens)
    (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
    (t : ∀ i, Fin 2 → Γ(S.scheme,(U i).1))
    (het : ∀ i, (MvPolynomial.eval₂Hom (openScalars S.structureMap (U i).1) (t i)).Etale)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ s : O S.scheme ⟶ (M.pow n).sheaf, s ≠ 0 ∧
        ∀ i, affineCoefficient (U i) (localPowerFrame (U i).1 (e i) n) s ∈
          (RingHom.ker (ρ i))^(n*m i) := by
  classical
  let W : ℕ := ∑ i, (m i)^2
  let T : ℕ := ∑ i, m i
  obtain ⟨B,C,hB⟩ := S.power_H2_linear_bound L hL M hm
  obtain ⟨N,hN,hpos⟩ := quadratic_lower_eventually_pos (selfIntersection S M-W)
    (eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (O S.scheme) - C - (W+T))
    (eulerCharacteristic S.structureMap 2 (O S.scheme)) (by omega) B
  refine ⟨N,hN,fun n hn => ?_⟩
  refine S.exists_section_with_point_orders L hL (M.pow n) U
    (fun i => localPowerFrame (U i).1 (e i) n) t het ρ (fun i => n*m i) ?_
  have he := S.arbitrary_power_euler_quadratic L hL M n
  rw [surface_euler_expansion] at he
  have hb : (cohomologyDimension S.structureMap (M.pow n).sheaf 2 : ℤ) ≤
      B+(C:ℤ)*n := by exact_mod_cast hB n
  have hi : (0 : ℤ) ≤ cohomologyDimension S.structureMap (M.pow n).sheaf 1 := Nat.cast_nonneg _
  have hsum : (∑ i, (n*m i)*(n*m i+1)) = n*n*W+n*T := by
    dsimp only [W,T]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hsum]
  have hp := hpos n hn
  have hnon : 0 ≤ (n : ℤ)*(W+T) := by positivity
  have HH : (n : ℤ)*n*W+n*T <
      2*(cohomologyDimension S.structureMap (M.pow n).sheaf 0 : ℤ) := by
    nlinarith only [he,hb,hi,hp,hnon]
  exact_mod_cast HH

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01_oai
