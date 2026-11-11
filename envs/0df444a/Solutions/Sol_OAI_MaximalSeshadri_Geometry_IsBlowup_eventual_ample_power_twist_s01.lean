-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:08.286215+00:00
-- url     : https://prove2.me/submissions/787bfe2f-95b4-4e3a-ad50-4d952f29d673

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PrincipalCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.ReesGrading

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
variable (X : Scheme.{u}) (f : R →+* Γ(X, ⊤)) (r : Γ(X, ⊤))
variable (hI : I.map f = Ideal.span {r}) (hr : IsRegular r)

lemma principalScheme_preimage (a : I) :
    principalScheme I X f r hI hr ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) =
      X.basicOpen (BlowupLift.coefficient I f r hI a) := by
  exact (Proj.fromOfGlobalSections_preimage_basicOpen (piece I)
    (principalMap I f r hI hr) (principalMap_irrelevant I f r hI hr)
    Nat.zero_lt_one (generator_mem I a)).trans
    (congrArg X.basicOpen (principalMap_generator I f r hI hr a))

end
end MaximalSeshadri.ReesGrading


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

theorem LineBundle.ample_common_degree_cover [CompactSpace X] (L : LineBundle X)
    (hL : LineBundle.IsAmple X L) :
    ∃ n : ℕ, 0 < n ∧ ∃ l : ℕ,
      ∃ s : Fin l → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) := by
  classical
  have hex (x : X) := hL x ⊤ (by trivial)
  choose d hd s hs hst ha using hex
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hs x⟩)
  obtain ⟨n, hn, t, ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let e := (Fintype.equivFin I).symm
  refine ⟨n, hn, Fintype.card I, fun i => t (e i), ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    change x ∈ sectionOpen X (t (e (e.symm ⟨i, hi⟩)))
    rw [Equiv.apply_symm_apply, ht]
    exact hx
  · intro i
    rw [ht]
    exact ha (e i).val
  · intro i
    rw [ht]
    exact ⟨(e i).val, hs (e i).val⟩

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
-- module Solutions.Q223_SES.Seshadri_Geometry_GeometricDivision
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_ReesSections
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y Z : Scheme.{0}}

lemma frame_ideal [IsAffine X] {I : X.IdealSheafData} {f : Y ⟶ X}
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] [IsAffine Z]
    (e : J.sheaf.restrict j ≅ O Z) :
    ((I.comap f).comap j).ideal ⟨⊤,isAffineOpen_top Z⟩ =
      Ideal.span {endValue (e.inv ≫ restrictedInclusion J ι j)} := by
  change _ = Ideal.span {UnitEndomorphism.equation (e.inv ≫ restrictedInclusion J ι j) ⊤}
  rw [← UnitEndomorphism.image_principal _ ⊤, ← restricted_image J ι h j ⟨⊤, isAffineOpen_top Z⟩]
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι j).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s :=
      congrArg (fun k : J.sheaf.restrict j ⟶ J.sheaf.restrict j => k.val.app (op ⊤) s) e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩
end
end MaximalSeshadri.InvertibleLocal

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_RelativeReesSections
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.ReesGrading
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.SpecMaps

variable {R : Type} [CommRing R] (I : Ideal R)
variable {B : Scheme.{0}} (f : B ⟶ Spec (.of R))
  (J : LineBundle B) (ι : J.sheaf ⟶ O B)
  (hJ : PresentsPullbackIdeal (IdealPullback.specIdeal I) f J ι)
include hJ

theorem relative_generator_section (a : I) :
    ∃ s : O B ⟶ J.sheaf,
      s ≫ ι = scalarEnd ((coordinate f) a.val) := by
  let : Mono ι := hJ.1
  obtain ⟨s,hs,-⟩ := global_division_of_local_lifts ι
      (scalarEnd ((coordinate f) a.val)) (by
    intro x
    obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
    let r := endValue (e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι)
    have hI : I.map (coordinate (U.1.ι ≫ f)).hom = Ideal.span {r} := by
      rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
      exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
    have hmem : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
        (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) ∈ Ideal.span {r} := by
      rw [← hI]
      have he : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
          (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) =
          coordinate (U.1.ι ≫ f) a.val := by
        change endValue (restrictSection U.1.ι
          (scalarEnd ((coordinate f) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom) = _
        rw [endValue_restrict, endValue_scalarEnd,coordinate_comp]
        rfl
      rw [he]
      exact Ideal.mem_map_of_mem _ a.property
    obtain ⟨t,ht⟩ := framed_local_division e (Scheme.Modules.restrictUnitIso U.1.ι)
      ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
      (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) hmem
    exact ⟨U.1,hx,t,ht⟩)
  exact ⟨s,hs⟩

theorem relative_generator_section_open (β : B ⟶ affineBlowup I) (hβ : β ≫ projection I = f) (a : I)
    (s : O B ⟶ J.sheaf)
    (hs : s ≫ ι = scalarEnd ((coordinate f) a.val)) :
    SectionOpens.isoOpen s = β ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
  have : Mono (C := B.Modules) (X := J.sheaf) (Y := structureSheaf B) ι := hJ.1
  ext x
  obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
  let g : UnitEndomorphism.unit U.1.toScheme ⟶
      UnitEndomorphism.unit U.1.toScheme :=
    e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι
  have : Mono (InvertibleLocal.restrictedInclusion J ι U.1.ι) :=
    InvertibleLocal.restrictedInclusion_mono J ι U.1.ι
  have : Mono g := mono_comp (C := U.1.toScheme.Modules) e.inv
    (InvertibleLocal.restrictedInclusion J ι U.1.ι)
  let r := endValue g
  have hr : IsRegular r := UnitEndomorphism.equation_regular g ⊤
  have hI : I.map (coordinate (U.1.ι ≫ f)).hom = Ideal.span {r} := by
    rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
    exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
  let h := principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ f)).hom r hI hr
  have hh : h = U.1.ι ≫ β := by
    apply invertible_unique I h (U.1.ι ≫ β) (U.1.ι ≫ f)
    · exact (principalScheme_projection I U.1.toScheme _ r hI hr).trans (factor _)
    · rw [Category.assoc,hβ]
    · exact InvertibleLocal.invertible_restrict _ _ ⟨J,ι,hJ⟩ U.1.ι
  have hscalar : coefficient e (restrictSection U.1.ι s) * r =
      coordinate (U.1.ι ≫ f) a.val := by
    have hcomp : (restrictSection U.1.ι s ≫ e.hom) ≫ g =
        restrictSection U.1.ι (scalarEnd ((coordinate f) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom := by
      change (restrictSection U.1.ι s ≫ e.hom) ≫
        (e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι) = _
      rw [Category.assoc, e.hom_inv_id_assoc]
      rw [← hs]
      change ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.1.ι).map s) ≫
        ((Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom) =
        ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
          (Scheme.Modules.restrictFunctor U.1.ι).map (s ≫ ι)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom
      calc
        _ = ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
            ((Scheme.Modules.restrictFunctor U.1.ι).map s ≫
              (Scheme.Modules.restrictFunctor U.1.ι).map ι)) ≫
            (Scheme.Modules.restrictUnitIso U.1.ι).hom :=
          (Category.assoc (obj := U.1.toScheme.Modules)
            ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
              (Scheme.Modules.restrictFunctor U.1.ι).map s)
            ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
            (Scheme.Modules.restrictUnitIso U.1.ι).hom).symm.trans
          (congrArg (fun sectionMap => sectionMap ≫
            (Scheme.Modules.restrictUnitIso U.1.ι).hom)
            (Category.assoc (obj := U.1.toScheme.Modules)
              (Scheme.Modules.restrictUnitIso U.1.ι).inv
              ((Scheme.Modules.restrictFunctor U.1.ι).map s)
              ((Scheme.Modules.restrictFunctor U.1.ι).map ι)))
        _ = _ := congrArg (fun sectionMap =>
          ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫ sectionMap) ≫
            (Scheme.Modules.restrictUnitIso U.1.ι).hom)
          ((Scheme.Modules.restrictFunctor U.1.ι).map_comp s ι).symm
    calc
      coefficient e (restrictSection U.1.ι s) * r =
          endValue ((restrictSection U.1.ι s ≫ e.hom) ≫ g) :=
        (endValue_comp (restrictSection U.1.ι s ≫ e.hom) g).symm
      _ = endValue (restrictSection U.1.ι
          (scalarEnd ((coordinate f) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom) := congrArg endValue hcomp
      _ = _ := by
        rw [endValue_restrict, endValue_scalarEnd, coordinate_comp]
        rfl
  have hc : coefficient e (restrictSection U.1.ι s) =
      BlowupLift.coefficient I (coordinate (U.1.ι ≫ f)).hom r hI a := by
    apply hr.left
    exact (mul_comm _ _).trans (hscalar.trans
      (BlowupLift.mul_coefficient I _ r hI a).symm)
  have hloc : U.1.ι ⁻¹ᵁ SectionOpens.isoOpen s =
      U.1.ι ⁻¹ᵁ β ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
    rw [preimage_isoOpen s U.1.ι e,hc]
    have H := principalScheme_preimage I U.1.toScheme _ r hI hr a
    change h ⁻¹ᵁ _ = _ at H
    rw [hh] at H
    exact H.symm
  exact SetLike.ext_iff.mp hloc ⟨x,hx⟩

end
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.ReesGrading
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)
variable {B : Scheme.{0}} (f : B ⟶ Spec (.of R))
  (J : LineBundle B) (ι : J.sheaf ⟶ O B)
  (hJ : PresentsPullbackIdeal (IdealPullback.specIdeal I) f J ι)
include hJ

theorem relative_affine_section_cover (hf : IsBlowup (IdealPullback.specIdeal I) f) :
    ∃ s : I → (O B ⟶ J.sheaf),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  classical
  let e : B ≅ Proj (piece I) := hf.iso (rees_isBlowup I)
  choose s hs using relative_generator_section I f J ι hJ
  have ho a := relative_generator_section_open I f J ι hJ e.hom
    (hf.iso_hom_comp (rees_isBlowup I)) a (s a) (hs a)
  refine ⟨s,?_,fun a => ?_⟩
  · simp only [ho]
    exact e.hom.iSup_preimage_eq_top (iSup_generator_basicOpen I)
  · rw [ho]
    exact (Proj.isAffineOpen_basicOpen (piece I) (generator I a) (generator_mem I a)
      (by decide : 0 < (1:ℕ))).preimage_of_isIso e.hom
end
end MaximalSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupAffineSections
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames

variable {X B B' : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.preIso (hπ : IsBlowup I π) (e : B' ≅ B) :
    IsBlowup I (e.hom ≫ π) := by
  refine ⟨InvertibleLocal.invertible_restrict_general I π hπ.1 e.hom,?_⟩
  intro Y f hf
  obtain ⟨g,hg,huniq⟩ := hπ.2 Y f hf
  refine ⟨g ≫ e.inv,by simp only [Category.assoc,Iso.inv_hom_id_assoc,hg],?_⟩
  intro g' hg'
  rw [← cancel_mono e.hom]
  simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using huniq (g' ≫ e.hom) hg'

lemma IsBlowup.morphismRestrict (hπ : IsBlowup I π) (U : X.Opens) :
    IsBlowup (I.comap U.ι) (π ∣_ U) := by
  have H := (hπ.open_baseChange U.ι).preIso (isPullback_morphismRestrict π U).isoPullback
  rwa [(isPullback_morphismRestrict π U).isoPullback_hom_fst] at H

lemma presents_post_toSpec [IsAffine X] (J : LineBundle B)
    (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    PresentsPullbackIdeal (IdealPullback.specIdeal (I.ideal ⟨⊤,isAffineOpen_top X⟩))
      (π ≫ X.isoSpec.hom) J ι := by
  refine ⟨hJ.1,?_⟩
  intro U V e
  rw [InvertibleLocal.image_eq_comap I π J ι hJ U,
    ← IdealPullback.comap_ideal _ (π ≫ X.isoSpec.hom) U V e,
      Scheme.IdealSheafData.comap_comp]
  rw [show (IdealPullback.specIdeal (I.ideal ⟨⊤,isAffineOpen_top X⟩)).comap
    X.isoSpec.hom = I from IdealPullback.specIdeal_comap_toSpec I]

theorem IsBlowup.affine_section_cover [IsAffine X] (hπ : IsBlowup I π)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ (α : Type) (s : α → (O B ⟶ J.sheaf)),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  let A := I.ideal ⟨⊤,isAffineOpen_top X⟩
  have hp := hπ.postIso X.isoSpec (IdealPullback.specIdeal A)
    (IdealPullback.specIdeal_comap_toSpec I)
  obtain ⟨s,hs,ha⟩ := ReesGrading.relative_affine_section_cover A
    (π ≫ X.isoSpec.hom) J ι (presents_post_toSpec J ι hJ) hp
  exact ⟨A,s,hs,ha⟩

lemma presents_morphismRestrict (J : LineBundle B) (ι : J.sheaf ⟶ O B)
    (hJ : PresentsPullbackIdeal I π J ι) (U : X.affineOpens) :
    PresentsPullbackIdeal (I.comap U.1.ι) (π ∣_ U.1)
      (J.restrict (π ⁻¹ᵁ U.1).ι) (InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι) := by
  have : Mono (C := B.Modules) (X := J.sheaf) (Y := structureSheaf B) ι := hJ.1
  refine ⟨InvertibleLocal.restrictedInclusion_mono J ι (π ⁻¹ᵁ U.1).ι, ?_⟩
  intro V W hVW
  change ((InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι).val.app
    (Opposite.op V.1)).hom.range = _
  rw [InvertibleLocal.restricted_image_on_chart J ι hJ (π ⁻¹ᵁ U.1).ι V U (by
    rintro _ ⟨x,hx,rfl⟩; exact x.property),
    ← Scheme.IdealSheafData.comap_comp,← morphismRestrict_ι π U.1,
      Scheme.IdealSheafData.comap_comp]
  exact IdealPullback.comap_ideal _ (π ∣_ U.1) V W hVW

end
end MaximalSeshadri.Geometry

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

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_MixedSectionOpen
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
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

theorem LineBundle.mixed_section_open_extension [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (s : O X ⟶ L.sheaf)
    (hne : (sectionOpen X s : Set X).Nonempty)
    (w : O (sectionOpen X s).toScheme ⟶ M.sheaf.restrict (sectionOpen X s).ι) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t = (sectionOpen X s).ι ''ᵁ isoOpen w := by
  let U := sectionOpen X s
  obtain ⟨N,hN⟩ := L.divisible_mixed_extension M s hne (openSectionEquiv M.sheaf U w)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht,hv⟩ := hN n hn
  have hi : IsIso (restrictSection U.ι (powerSection s (n+1))) :=
    isIso_restricted_section _ _ (L.sectionOpen_power s (by omega))
  have hpre : U.ι ⁻¹ᵁ isoOpen t = isoOpen w := by
    rw [← isoOpen_restrictSection]
    have hval := mixed_value_restrict U (powerSection s (n+1)) w t hv
    have hpost := isoOpen_postcomp (tensorSection (restrictSection U.ι (powerSection s (n+1))) w)
      (moduleTensorRestrict U (L.pow (n+1)).sheaf M.sheaf).symm
    have hopen := section_open ((L.pow (n+1)).restrict U.ι) (M.restrict U.ι)
      (restrictSection U.ι (powerSection s (n+1))) w
    refine (congrArg isoOpen hval).trans (hpost.trans (hopen.trans ?_))
    have he : isoOpen (restrictSection U.ι (powerSection s (n+1))) = ⊤ := by
      apply top_unique
      intro x _
      apply (mem_isoOpen_iff _ x).mpr
      exact ⟨⊤, trivial, by infer_instance⟩
    exact (congrArg (fun sectionDomain : U.toScheme.Opens => sectionDomain ⊓ isoOpen w)
      he).trans (top_inf_eq _)
  refine ⟨t,?_⟩
  change isoOpen t = _
  rw [← hpre,Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
  exact (inf_eq_right.mpr ht).symm
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

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PullbackSectionOpenExact
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
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.SectionOpens

variable {X Y : Scheme.{0}}

theorem pullback_isoOpen_eq (L : LineBundle X) (s : O X ⟶ L.sheaf) (f : Y ⟶ X) :
    isoOpen (pullbackSection f s) = f ⁻¹ᵁ isoOpen s := by
  ext y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame_all f U e
  calc
    y ∈ isoOpen (pullbackSection f s) ↔
        (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ (f ⁻¹ᵁ U).toScheme.basicOpen
          (coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s))) :=
      (congrArg (fun V => (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ V)
        (preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι eF)).to_iff
    _ ↔ (⟨f y,hy⟩ : U.toScheme) ∈ U.toScheme.basicOpen
          (coefficient e (restrictSection U.ι s)) := by
      rw [he,← Scheme.preimage_basicOpen_top]
      change (f ∣_ U) ⟨y,hy⟩ ∈ U.toScheme.basicOpen
        (coefficient e (restrictSection U.ι s)) ↔ _
      rw [morphismRestrict_base]
      rfl
    _ ↔ f y ∈ isoOpen s :=
      (congrArg (fun V => (⟨f y,hy⟩ : U.toScheme) ∈ V)
        (preimage_isoOpen s U.ι e)).to_iff.symm

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_EventualExceptionalAmple
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens MaximalSeshadri.Projective

variable {X : Scheme.{0}}

theorem LineBundle.eventual_twist_affine_cover [IsIntegral X] [CompactSpace X]
    (P J : LineBundle X) {κ : Type} (t : κ → (O X ⟶ P.sheaf))
    (ht : (⨆ i,isoOpen (t i)) = ⊤)
    (hlocal : ∀ i, ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ (σ : Type) (_ : Fintype σ)
      (s : σ → (O X ⟶ ((P.pow (n+1)).tensor J).sheaf)),
        (⨆ a,isoOpen (s a)) = ⊤ ∧
        (∀ a, IsAffineOpen (isoOpen (s a))) ∧
        (∀ a, (isoOpen (s a) : Set X).Nonempty) := by
  classical
  choose α w hw hwa using hlocal
  have hex (x : X) : ∃ i, x ∈ isoOpen (t i) := by
    apply Opens.mem_iSup.mp
    rw [ht]; trivial
  choose i hi using hex
  have hex' (x : X) : ∃ a, (⟨x,hi x⟩ : (isoOpen (t (i x))).toScheme) ∈
      isoOpen (w (i x) a) := by
    apply Opens.mem_iSup.mp
    exact (hw (i x)).ge trivial
  choose a ha using hex'
  let V (x : X) : X.Opens := (isoOpen (t (i x))).ι ''ᵁ isoOpen (w (i x) (a x))
  have hxV (x : X) : x ∈ V x := ⟨⟨x,hi x⟩,ha x,rfl⟩
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hxV x⟩)
  choose N hN using fun x : F => P.mixed_section_open_extension J (t (i x.val))
    ⟨x.val,hi x.val⟩ (w (i x.val) (a x.val))
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose s hs using fun x : F => hN x n ((Finset.le_sup (Finset.mem_univ x)).trans hn)
  refine ⟨F,inferInstance,s,?_,?_,?_⟩
  · apply top_unique
    intro x _
    obtain ⟨y,hy⟩ := Set.mem_iUnion.mp (hF (show x ∈ Set.univ from trivial))
    obtain ⟨hyF,hxy⟩ := Set.mem_iUnion.mp hy
    apply Opens.mem_iSup.mpr
    refine ⟨⟨y,hyF⟩,?_⟩
    rw [show isoOpen (s ⟨y,hyF⟩) = V y from hs ⟨y,hyF⟩]
    exact hxy
  · intro x
    rw [show isoOpen (s x) = V x.val from hs x]
    exact (hwa (i x.val) (a x.val)).image_of_isOpenImmersion _
  · intro x
    rw [show isoOpen (s x) = V x.val from hs x]
    exact ⟨x.val,hxV x.val⟩

variable {B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.eventual_ample_exceptional_twist [IsIntegral B] [CompactSpace B]
    [CompactSpace X] (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
      ((((L.pow a).pullback π).pow (n+1)).tensor J).IsAmple := by
  classical
  obtain ⟨a,ha,l,s,hs,hsa,-⟩ := L.ample_common_degree_cover hL
  let P := (L.pow a).pullback π
  let t (i : Fin l) : O B ⟶ P.sheaf := pullbackSection π (s i)
  have ht i : isoOpen (t i) = π ⁻¹ᵁ isoOpen (s i) := pullback_isoOpen_eq (L.pow a) (s i) π
  have hc : (⨆ i,isoOpen (t i)) = ⊤ := pullback_sections_cover s hs π
  have hloc (i : Fin l) : ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a)) := by
    rw [ht]
    let U : X.affineOpens := ⟨isoOpen (s i),hsa i⟩
    let : IsAffine U.1.toScheme := U.2
    exact (hπ.morphismRestrict U.1).affine_section_cover (J.restrict (π ⁻¹ᵁ U.1).ι)
      (InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι)
      (presents_morphismRestrict J ι hJ U)
  obtain ⟨N,hN⟩ := P.eventual_twist_affine_cover J t hc hloc
  refine ⟨a,N,ha,fun n hn => ?_⟩
  obtain ⟨σ,hσ,q,hq,hqa,-⟩ := hN n hn
  exact ((P.pow (n+1)).tensor J).ample_of_affine_section_cover q hq hqa

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntersection
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
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

lemma LineBundle.ample_of_iso {X : Scheme.{0}} (L M : LineBundle X)
    (e : L.sheaf ≅ M.sheaf) (hL : L.IsAmple) : M.IsAmple := by
  intro x V hx
  obtain ⟨n,hn,s,hs,hsub,ha⟩ := hL x V hx
  let c := (modulePowFunctor n).mapIso e
  have he : sectionOpen X (s ≫ c.hom) = sectionOpen X s :=
    SectionOpens.isoOpen_postcomp _ _
  exact ⟨n,hn,s ≫ c.hom,he ▸ hs,he ▸ hsub,he ▸ ha⟩

lemma IsBlowup.eventual_ample_power_twist_s01_oai {X Y : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [CompactSpace X] {I : X.IdealSheafData} {f : Y ⟶ X}
    (hb : IsBlowup I f) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι) :
    ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
      (((L.pullback f).pow (a*(n+1))).tensor J).IsAmple := by
  obtain ⟨a,N,ha,h⟩ := hb.eventual_ample_exceptional_twist L hL J ι hJ
  refine ⟨a,N,ha,fun n hn => ?_⟩
  apply LineBundle.ample_of_iso _ _ _ (h n hn)
  exact moduleTensorIso ((modulePowFunctor (n+1)).mapIso (PullbackTensor.powIso f L a) ≪≫
    linePowerMul (L.pullback f) a (n+1)) (Iso.refl _)

end
end MaximalSeshadri.Geometry

end



end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist_s01_oai := @OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist_s01_oai
