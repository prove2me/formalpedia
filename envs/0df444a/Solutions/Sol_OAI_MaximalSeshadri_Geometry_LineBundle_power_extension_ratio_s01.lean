-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.LineBundle.power_extension_ratio_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:00.314891+00:00
-- url     : https://prove2.me/submissions/6631b114-4d81-4198-aeff-87cda2b4b9c6

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_Sections
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FramedMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

theorem LineBundle.power_extension_ratio_s01_oai [IsIntegral X] [CompactSpace X] (L : LineBundle X)
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

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.LineBundle.power_extension_ratio_s01_oai := @OAI.MaximalSeshadri.Geometry.LineBundle.power_extension_ratio_s01_oai
