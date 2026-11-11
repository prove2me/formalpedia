-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:19:42.332817+00:00
-- url     : https://prove2.me/submissions/f1fc5e8e-a6d2-4d38-8b5d-fb25f606e6af

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_exists_projective_sections_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_cohomology_finite_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_pow_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_tensor_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_power_euler_difference_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_H1_le_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_cohomology_finite_s01
import Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_on_any_frame_s01

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
-- module Solutions.Q223_SES.Seshadri_Sheaves_CartierModule
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.IdealModule

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

lemma equationToIdeal_app (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (U : X.Opens) (a : Γ(X, U)) :
    (inclusion f).val.app (op U) ((equationToIdeal f r hr).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a :=
  congrArg (fun g => g.val.app (op U) a) (equationToIdeal_inclusion f r hr)

lemma isIso_equationToIdeal (f : Y ⟶ X) [QuasiCompact f]
    (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (hprincipal : ∀ U : X.affineOpens,
      f.ker.ideal U = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (equationToIdeal f r hr) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective ((inclusion f).val.app (op U.1)) := by
    let : Mono (inclusion f).val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map (inclusion f)))
    exact PresheafOfModules.injective_of_mono (inclusion f).val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg ((inclusion f).val.app (op U.1)) hab
    change (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) a) =
      (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) b) at he
    exact (equationToIdeal_app f r hr U.1 a).symm.trans
      (he.trans (equationToIdeal_app f r hr U.1 b))
  · intro y
    have hy : (inclusion f).val.app (op U.1) y ∈ f.ker.ideal U := by
      rw [← image_eq_ideal f U]
      exact ⟨y, rfl⟩
    rw [hprincipal U] at hy
    have hd : X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r ∣
        (show Γ(X, U.1) from (inclusion f).val.app (op U.1) y) :=
      Ideal.mem_span_singleton.mp hy
    obtain ⟨a, ha⟩ := hd
    refine ⟨a, hinj ?_⟩
    exact (equationToIdeal_app f r hr U.1 a).trans ha.symm

end

end MaximalSeshadri.IdealModule

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceCurveDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open MaximalSeshadri.Frames MaximalSeshadri.Projective
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

theorem IntegralCurve.cohomology_finite (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A)
    (L : LineBundle C.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n)
      (baseScalars (C.embedding ≫ S.structureMap))
    Module.Finite ℂ (cohomology L.sheaf n) := by
  obtain ⟨σ,hσ,M,a,ha,hc⟩ := C.exists_projective_sections_s01 S A hA
  let := hσ
  let := hc
  let : IsClosedImmersion (sectionsMorphism
    ((C.embedding ≫ S.structureMap).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) := hc
  exact projective_curve_cohomology_finite_s01 (C.embedding ≫ S.structureMap)
    C.dimension a ha L n

end
end MaximalSeshadri.Geometry
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

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ModuleLocal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.ModuleLocal
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X : Scheme.{0}} {M N : X.Modules}

lemma exact_of_local (S : ShortComplex X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (S.map (Scheme.Modules.restrictFunctor U.ι)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) := by
    have : PreservesFiniteLimits
        (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf U.toScheme) := by
      change PreservesFiniteLimits
        (Scheme.Modules.toPresheaf X ⋙ (Functor.whiskeringLeft _ _ _).obj U.ι.opensFunctor.op)
      have : PreservesFiniteLimits (Scheme.Modules.toPresheaf X) := inferInstance
      have : PreservesFiniteLimits
          ((Functor.whiskeringLeft _ _ Ab).obj U.ι.opensFunctor.op) := inferInstance
      exact comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_reflects_of_preserves _
      (Scheme.Modules.toPresheaf U.toScheme)
  have hz : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj S.homology) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp hU).of_iso
      (S.mapHomologyIso (Scheme.Modules.restrictFunctor U.ι)).symm
  refine ⟨U,hx,?_⟩
  rw [CategoryTheory.Functor.map_id]
  exact hz.eq_of_src _ _

end
end MaximalSeshadri.ModuleLocal

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ClosedModuleExact
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma structureMap_epi (f : X ⟶ Y) [IsClosedImmersion f] : Epi (structureMap f) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map (structureMap f)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    obtain ⟨_,⟨V,hA,rfl⟩,hyV,hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    obtain ⟨s,hs⟩ := f.app_surjective V hA
      (((F.obj ((Scheme.Modules.pushforward f).obj (unit X))).obj.map
        (homOfLE hVU).op) t)
    exact ⟨V,hVU,⟨s,hs⟩,hyV⟩
  let : Epi (F.map (structureMap f)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact F.epi_of_epi_map inferInstance

theorem closedSequence_exact (f : X ⟶ Y) [IsClosedImmersion f] :
    (ShortComplex.mk (inclusion f) (structureMap f) (kernel.condition _)).ShortExact := by
  let := structureMap_epi f
  exact { exact := ShortComplex.exact_kernel _ }

end
end MaximalSeshadri.IdealModule
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_LineClosedUnit
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.LineClosedUnit
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma framed_map (L : LineBundle Y) (U : Y.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom = IdealModule.structureMap (f ∣_ U) := by
  dsimp only [map, IdealModule.structureMap]
  have hu := OpenBaseChange.unit_compatibility f U L.sheaf
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit_naturality e.hom
  have hb := pullbackUnit_adjunction (f ∣_ U)
  rw [Adjunction.homEquiv_unit] at hb
  dsimp only [frame, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [← Category.assoc]
  rw [Category.assoc e.inv, hu]
  simp only [Category.assoc]
  have hec : (OpenBaseChange.leftSquare f U).hom.app L.sheaf ≫
      ((OpenBaseChange.leftSquare f U).app L.sheaf).inv = 𝟙 _ :=
    ((OpenBaseChange.leftSquare f U).app L.sheaf).hom_inv_id
  rw [← Functor.map_comp_assoc, hec]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change e.inv ≫ (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app _ ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.pullback (f ∣_ U)).map e.hom ≫ (pullbackUnitIso (f ∣_ U)).hom) = _
  rw [Functor.map_comp]
  have hn' := congrArg (fun t => e.inv ≫ t ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map (pullbackUnitIso (f ∣_ U)).hom) hn
  simp only [Category.assoc, hb] at hn'
  exact hn'.trans (e.inv_hom_id_assoc _)

theorem epi [IsClosedImmersion f] (L : LineBundle Y) : Epi (map f L) := by
  apply ModuleLocal.epi_of_local
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U,hy,?_⟩
  have hg : Epi (IdealModule.structureMap (f ∣_ U)) := IdealModule.structureMap_epi _
  have he := framed_map f L U e
  have : Epi (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
    (frame f L U e).hom) := he.symm ▸ hg
  have h1 : Epi ((Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom) := epi_of_epi e.inv _
  exact (epi_comp_iff_of_isIso _ _).mp h1

end
end MaximalSeshadri.LineClosedUnit

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PrincipalSequence
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.coefficient_scalarEnd _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.PrincipalSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma scalarEnd_eq_multiply (r : Γ(X,⊤)) : scalarEnd r = IdealModule.multiply r := rfl

lemma end_regular_of_mono (a : O X ⟶ O X) [Mono a] : IsLeftRegular (endValue a) := by
  have hinj : Function.Injective (a.val.app (op ⊤)) :=
    PresheafOfModules.injective_of_mono
      ((Scheme.Modules.toPresheafOfModules X).map a) (op ⊤)
  intro r s hrs
  apply hinj
  change a.app ⊤ r = a.app ⊤ s
  rw [end_apply a ⊤ r, end_apply a ⊤ s]
  change r * endValue a = s * endValue a
  simpa only [mul_comm] using hrs

theorem exact [IsAffine Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (a : O Y ⟶ O Y) [Mono a]
    (h : f.ker.ideal ⟨⊤,isAffineOpen_top Y⟩ = Ideal.span {endValue a}) :
    ∃ hz : a ≫ IdealModule.structureMap f = 0,
      (ShortComplex.mk a (IdealModule.structureMap f) hz).ShortExact := by
  let r := endValue a
  have hr : f.appTop r = 0 := by
    apply f.ideal_ker_le ⟨⊤, isAffineOpen_top Y⟩
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hreg : IsLeftRegular r := end_regular_of_mono a
  have hprincipal (U : Y.affineOpens) : f.ker.ideal U =
      Ideal.span {Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r} := by
    rw [← f.ker.map_ideal (U := U) (V := ⟨⊤,isAffineOpen_top Y⟩) (by change U.1 ≤ ⊤; exact le_top), h]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have hi : IsIso (IdealModule.equationToIdeal f r hr) :=
    IdealModule.isIso_equationToIdeal f r hr hprincipal
      (IdealModule.restriction_regular r hreg)
  have he : a = IdealModule.multiply r := by
    rw [← scalarEnd_eq_multiply]
    apply endValue_injective
    simp [r]
  have hz : a ≫ IdealModule.structureMap f = 0 := by
    rw [he]
    exact IdealModule.multiply_structure_zero f r hr
  refine ⟨hz,?_⟩
  let S := ShortComplex.mk a (IdealModule.structureMap f) hz
  let T := ShortComplex.mk (IdealModule.inclusion f) (IdealModule.structureMap f)
    (kernel.condition (IdealModule.structureMap f))
  let equationIso := asIso (IdealModule.equationToIdeal f r hr)
  let e : S ≅ T := ShortComplex.isoMk equationIso
    (Iso.refl _) (Iso.refl _) (by
      change IdealModule.equationToIdeal f r hr ≫ IdealModule.inclusion f = a ≫ 𝟙 _
      rw [Category.comp_id]
      exact (IdealModule.equationToIdeal_inclusion f r hr).trans he.symm) (by
      change 𝟙 (IdealModule.unit Y) ≫ IdealModule.structureMap f =
        IdealModule.structureMap f ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id])
  exact ShortComplex.shortExact_of_iso e.symm (IdealModule.closedSequence_exact f)

end
end MaximalSeshadri.PrincipalSequence

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CartierSequence
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.CartierSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma restriction_principal (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (U : X.affineOpens) (r : Γ(U.1.toScheme,⊤))
    (hI : I.ideal U = Ideal.span {U.1.topIso.hom r}) :
    (I.subschemeι ∣_ U.1).ker.ideal ⟨⊤,isAffineOpen_top U.1.toScheme⟩ =
      Ideal.span {r} := by
  ext z
  rw [Scheme.Hom.ker_apply,RingHom.mem_ker]
  change (I.subschemeι ∣_ U.1).appTop z = 0 ↔ z ∈ Ideal.span {r}
  have hz : (I.subschemeι ∣_ U.1).appTop z = 0 ↔
      U.1.topIso.hom z ∈ I.ideal U := by
    rw [← structuralOpenChartMap_ker p I U]
    change (I.subschemeι ∣_ U.1).appTop z = 0 ↔
      (I.subschemeι ∣_ U.1).appTop (U.1.topIso.inv (U.1.topIso.hom z)) = 0
    rw [U.1.topIso.hom_inv_id_apply]
  rw [hz,hI,Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.inv a,?_⟩
    have h := congrArg U.1.topIso.inv ha
    simpa only [map_mul,U.1.topIso.hom_inv_id_apply] using h
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.hom a,?_⟩
    simpa only [map_mul] using congrArg U.1.topIso.hom ha

theorem exact (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :
    ∃ hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0,
      (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).ShortExact := by
  have local_exact (U : X.affineOpens)
      (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (hI : I.ideal U = Ideal.span {U.1.topIso.hom
        (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :=
    PrincipalSequence.exact (I.subschemeι ∣_ U.1)
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
      (restriction_principal p I U _ hI)
  have hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0 := by
    apply ModuleLocal.eq_zero_of_local
    intro x
    obtain ⟨U,hx,e,d,hI⟩ := heq x
    obtain ⟨hzero,hex⟩ := local_exact U e d hI
    refine ⟨U.1,hx,?_⟩
    apply (cancel_epi e.inv).mp
    apply (cancel_mono (LineClosedUnit.frame I.subschemeι N U.1 d).hom).mp
    rw [Functor.map_comp,comp_zero,zero_comp]
    rw [Category.assoc,Category.assoc]
    rw [← d.hom_inv_id_assoc ((Scheme.Modules.restrictFunctor U.1.ι).map
      (LineClosedUnit.map I.subschemeι N))]
    simp only [Category.assoc]
    rw [LineClosedUnit.framed_map]
    exact (congrArg (fun morphism => e.inv ≫ morphism)
      (Category.assoc ((Scheme.Modules.restrictFunctor U.1.ι).map φ) d.hom
        (IdealModule.structureMap (I.subschemeι ∣_ U.1)))).symm.trans
          ((Category.assoc _ _ _).symm.trans hzero)
  refine ⟨hz,{ exact := ?_, epi_g := LineClosedUnit.epi _ _ }⟩
  apply ModuleLocal.exact_of_local
  intro x
  obtain ⟨U,hx,e,d,hI⟩ := heq x
  obtain ⟨hzero,hex⟩ := local_exact U e d hI
  refine ⟨U.1,hx,?_⟩
  let S := (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).map
    (Scheme.Modules.restrictFunctor U.1.ι)
  let T := ShortComplex.mk (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
    (IdealModule.structureMap (I.subschemeι ∣_ U.1)) hzero
  let ee : S ≅ T := ShortComplex.isoMk e d (LineClosedUnit.frame I.subschemeι N U.1 d)
    (by simp [S,T]; exact e.hom_inv_id_assoc _) (by
      change d.hom ≫ IdealModule.structureMap (I.subschemeι ∣_ U.1) =
        (Scheme.Modules.restrictFunctor U.1.ι).map (LineClosedUnit.map I.subschemeι N) ≫ _
      exact (congrArg (fun morphism => d.hom ≫ morphism)
        (LineClosedUnit.framed_map I.subschemeι N U.1 d)).symm.trans
          (d.hom_inv_id_assoc _))
  exact ShortComplex.exact_of_iso ee.symm hex.exact

end
end MaximalSeshadri.CartierSequence

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.pushforward_cohomology_finite (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n)
      (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n) := by
  let := Module.compHom (cohomology L.sheaf n) (baseScalars (C.embedding ≫ S.structureMap))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n)
    (baseScalars S.structureMap)
  let := C.cohomology_finite S A hA L n
  exact Module.Finite.equiv (ClosedPushforward.cohomologyEquiv C.embedding S.structureMap L.sheaf n)

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

local instance instHasExtModules_solutions_1_r4bc9aa_1 : HasExt.{1} X.Modules := schemeHasExt
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
-- module Solutions.Q223_SES.Seshadri_Cohomology_CurveH1Bound
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

theorem IntegralCurve.H1_le (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (M : LineBundle C.scheme)
    (hdeg : 0 ≤ eulerCharacteristic (C.embedding ≫ S.structureMap) 1 M.sheaf -
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)) :
    cohomologyDimension (C.embedding ≫ S.structureMap) M.sheaf 1 ≤
      cohomologyDimension (C.embedding ≫ S.structureMap) (O C.scheme) 1 := by
  obtain ⟨σ,hσ,N,a,ha,hclosed⟩ := C.exists_projective_sections_s01 S A hA
  let := hσ
  have := hclosed
  exact projective_curve_H1_le_s01 (C.embedding ≫ S.structureMap) C.dimension a ha M hdeg
end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_ExactDimensionBound
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

lemma finrank_middle_le_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K U]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.finrank K V ≤ Module.finrank K U + Module.finrank K W := by
  have he := g.finrank_range_add_finrank_ker
  rw [LinearMap.exact_iff.mp h] at he
  have hf := f.finrank_range_le
  have hg := g.range.finrank_le
  omega

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceH2Untwist
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

lemma cohomologyDimension_pushforward {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    cohomologyDimension p ((Scheme.Modules.pushforward i).obj M) n =
      cohomologyDimension (i ≫ p) M n := by
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward i).obj M) n) (baseScalars p)
  let := Module.compHom (cohomology M n) (baseScalars (i ≫ p))
  exact (ClosedPushforward.cohomologyEquiv i p M n).finrank_eq.symm

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceH1Growth
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
local instance instHasExtModules_solutions_2 : HasExt.{1} X.Modules := schemeHasExt

lemma cohomologyDimension_middle_bound (p : X ⟶ Spec (CommRingCat.of ℂ))
    {T : ShortComplex X.Modules} (hT : T.ShortExact) (n : ℕ)
    (hf₁ : letI := Module.compHom (cohomology T.X₁ n) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₁ n))
    (hf₂ : letI := Module.compHom (cohomology T.X₂ n) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₂ n))
    (hf₃ : letI := Module.compHom (cohomology T.X₃ n) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₃ n)) :
    cohomologyDimension p T.X₂ n ≤ cohomologyDimension p T.X₁ n +
      cohomologyDimension p T.X₃ n := by
  let := Module.compHom (cohomology T.X₁ n) (baseScalars p)
  let := Module.compHom (cohomology T.X₂ n) (baseScalars p)
  let := Module.compHom (cohomology T.X₃ n) (baseScalars p)
  let := hf₁
  let := hf₂
  let := hf₃
  let f : cohomology T.X₁ n →ₗ[ℂ] cohomology T.X₂ n :=
    { toFun := (Ext.mk₀ T.f).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)
      map_add' := (Ext.mk₀ T.f).postcompOfLinear Γ(X,⊤) (O X) (add_zero n) |>.map_add
      map_smul' := fun r x => ((Ext.mk₀ T.f).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)).map_smul (baseScalars p r) x }
  let g : cohomology T.X₂ n →ₗ[ℂ] cohomology T.X₃ n :=
    { toFun := (Ext.mk₀ T.g).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)
      map_add' := (Ext.mk₀ T.g).postcompOfLinear Γ(X,⊤) (O X) (add_zero n) |>.map_add
      map_smul' := fun r x => ((Ext.mk₀ T.g).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)).map_smul (baseScalars p r) x }
  apply finrank_middle_le_of_exact f g
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₂ (O X) hT x
  · rintro ⟨y,rfl⟩
    change (y.comp (Ext.mk₀ T.f) (add_zero n)).comp (Ext.mk₀ T.g) (add_zero n) = 0
    rw [Ext.comp_assoc,Ext.mk₀_comp_mk₀,T.zero,Ext.mk₀_zero,Ext.comp_zero] <;> omega

theorem Surface.power_H1_linear_bound (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B G : ℕ, ∀ n : ℕ, cohomologyDimension S.structureMap (L.pow n).sheaf 1 ≤ B+G*n := by
  classical
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let I := sectionIdeal k s hs v
  let C : IntegralCurve S := ⟨I.subscheme,I.subschemeι,inferInstance,inferInstance,hC⟩
  let G := cohomologyDimension (C.embedding ≫ S.structureMap) (O C.scheme) 1
  let f (n : ℕ) := cohomologyDimension S.structureMap (L.pow n).sheaf 1
  have hstep (n : ℕ) : f (n+d) ≤ f n+G := by
    let M := L.pow n
    let P := L.pow d
    let Q := (P.tensor M).pullback C.embedding
    let φ : M.sheaf ⟶ (P.tensor M).sheaf :=
      sectionMultiply P M (sectionCombination k s v)
    let : Mono φ := sectionMultiply_mono P M (sectionCombination k s v) hne
    obtain ⟨hz,hseq⟩ := CartierSequence.exact S.structureMap M (P.tensor M) φ I (by
      intro x
      obtain ⟨U,hx,⟨e⟩,⟨g⟩⟩ := common_affine_frames P M x
      refine ⟨U,hx,g,tensorFrame P M U.1 e g,?_⟩
      exact (sectionIdeal_on_any_frame_s01 k s hs v U e).trans
        (tensor_multiply_ideal P M (sectionCombination k s v) U e g).symm)
    have H := cohomologyDimension_middle_bound S.structureMap hseq 1
      (S.cohomology_finite_s01 L hL M 1) (S.cohomology_finite_s01 L hL (P.tensor M) 1)
      (C.pushforward_cohomology_finite S L hL Q 1)
    rw [cohomologyDimension_pushforward] at H
    have hdeg : 0 ≤ curveDegree S (P.tensor M) C := by
      rw [curveDegree_tensor_s01 S L hL,curveDegree_pow_s01 S L hL,curveDegree_pow_s01 S L hL]
      have hp := (C.ample_degree_positive_s01 S L hL).le
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hp) (mul_nonneg (Nat.cast_nonneg _) hp)
    have hg := C.H1_le S L hL Q hdeg
    have he := cohomologyDimension_iso S.structureMap (linePowerAdd L d n) 1
    change f (d+n) = cohomologyDimension S.structureMap (P.tensor M).sheaf 1 at he
    rw [Nat.add_comm d n] at he
    rw [he]
    exact H.trans (Nat.add_le_add_left hg _)
  let B := ∑ j ∈ Finset.range d, f j
  refine ⟨B,G,?_⟩
  intro n
  change f n ≤ B+G*n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < d
    · have H : f n ≤ B := Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_range.mpr hn)
      exact H.trans (Nat.le_add_right _ _)
    · have hdn : d ≤ n := by omega
      have H := hstep (n-d)
      rw [Nat.sub_add_cancel hdn] at H
      have HH := ih (n-d) (by omega)
      have hm : G*(n-d)+G ≤ G*n := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ (by omega)
      omega

theorem Surface.power_H0_quadratic_upper_s01_oai (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B G : ℕ, ∀ n : ℕ,
      2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) ≤
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) + 2*B+2*G*n := by
  obtain ⟨B,G,hG⟩ := S.power_H1_linear_bound L hL
  refine ⟨B,G,fun n => ?_⟩
  have he := S.power_euler_quadratic L hL n
  rw [surface_euler_expansion] at he
  have h := hG n
  have hb : (cohomologyDimension S.structureMap (L.pow n).sheaf 1 : ℤ) ≤ B+(G:ℤ)*n := by exact_mod_cast h
  have hn : (0:ℤ) ≤ cohomologyDimension S.structureMap (L.pow n).sheaf 2 := Nat.cast_nonneg _
  nlinarith
end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01_oai
