-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:11.953757+00:00
-- url     : https://prove2.me/submissions/b71094a7-56f9-4fc5-b3b1-18ee3c1b44f9

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_pow_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_tensor_s01

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CohomologyIso
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
-- module Solutions.Q223_SES.Seshadri_Geometry_GeometricDivision
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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

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
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorInclusion
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

lemma tensor_inclusion_framed (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.Opens) (e : J.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame J M U e f).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (tensorInclusion J M ι) ≫ f.hom =
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom) ≫ (tensorUnitTwist M U f).inv := by
  let restrictionFunctor : X.Modules ⥤ U.toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι
  let unitRestriction : restrictionFunctor.obj (O X) ≅ O U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  let sourceUnit : moduleTensor X (O X) M.sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let targetUnit : moduleTensor U.toScheme (O U.toScheme) (O U.toScheme) ≅
      O U.toScheme := moduleTensorUnit (O U.toScheme)
  let sourceRestriction : restrictionFunctor.obj (moduleTensor X J.sheaf M.sheaf) ≅
      moduleTensor U.toScheme (restrictionFunctor.obj J.sheaf)
        (restrictionFunctor.obj M.sheaf) := moduleTensorRestrict U J.sheaf M.sheaf
  let targetRestriction : restrictionFunctor.obj (moduleTensor X (O X) M.sheaf) ≅
      moduleTensor U.toScheme (restrictionFunctor.obj (O X))
        (restrictionFunctor.obj M.sheaf) := moduleTensorRestrict U (O X) M.sheaf
  let tensorMap : moduleTensor X J.sheaf M.sheaf ⟶ moduleTensor X (O X) M.sheaf :=
    moduleTensorMap ι (𝟙 M.sheaf)
  let inclusion : moduleTensor X J.sheaf M.sheaf ⟶ M.sheaf := tensorInclusion J M ι
  let frame : restrictionFunctor.obj (moduleTensor X J.sheaf M.sheaf) ≅
      O U.toScheme := tensorFrame J M U e f
  let twist : O U.toScheme ≅ O U.toScheme := tensorUnitTwist M U f
  let scalar : O U.toScheme ⟶ O U.toScheme :=
    e.inv ≫ restrictionFunctor.map ι ≫ unitRestriction.hom
  have inclusion_eq : inclusion = tensorMap ≫ sourceUnit.hom := rfl
  have naturality : restrictionFunctor.map tensorMap ≫ targetRestriction.hom =
      sourceRestriction.hom ≫ moduleTensorMap (restrictionFunctor.map ι)
        (𝟙 (restrictionFunctor.obj M.sheaf)) := by
    have naturality' : restrictionFunctor.map tensorMap ≫ targetRestriction.hom =
        sourceRestriction.hom ≫ moduleTensorMap (restrictionFunctor.map ι)
          (restrictionFunctor.map (𝟙 M.sheaf)) :=
      moduleTensorRestrict_natural U ι (𝟙 M.sheaf)
    simpa only [restrictionFunctor.map_id] using naturality'
  change frame.inv ≫ restrictionFunctor.map inclusion ≫ f.hom = scalar ≫ twist.inv
  apply (cancel_mono twist.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have frame_inv : frame.inv =
      (targetUnit.inv ≫ moduleTensorMap (X := U.toScheme) e.inv f.inv) ≫
        sourceRestriction.inv := rfl
  have twist_hom : twist.hom = f.inv ≫
      restrictionFunctor.map sourceUnit.inv ≫ targetRestriction.hom ≫
      moduleTensorMap unitRestriction.hom f.hom ≫ targetUnit.hom := rfl
  rw [frame_inv, twist_hom]
  rw [inclusion_eq, restrictionFunctor.map_comp]
  simp only [Category.assoc, f.hom_inv_id_assoc]
  rw [← restrictionFunctor.map_comp_assoc sourceUnit.hom sourceUnit.inv,
    sourceUnit.hom_inv_id,
    restrictionFunctor.map_id, Category.id_comp]
  rw [← Category.assoc (restrictionFunctor.map tensorMap), naturality]
  simp only [Category.assoc, sourceRestriction.inv_hom_id_assoc]
  rw [← Category.assoc (moduleTensorMap (X := U.toScheme) e.inv f.inv),
    ← moduleTensorMap_comp (X := U.toScheme), Category.comp_id,
    ← Category.assoc (moduleTensorMap (X := U.toScheme) _ _),
    ← moduleTensorMap_comp (X := U.toScheme), f.inv_hom_id]
  have hscalar : moduleTensorMap scalar (𝟙 (O U.toScheme)) ≫ targetUnit.hom =
      targetUnit.hom ≫ scalar := by
    exact (moduleTensorUnit_scalar (X := U.toScheme) scalar (𝟙 (O U.toScheme))).trans
      (congrArg (fun morphism : O U.toScheme ⟶ O U.toScheme =>
        targetUnit.hom ≫ morphism) (Category.comp_id scalar))
  rw [Category.assoc e.inv, hscalar, targetUnit.inv_hom_id_assoc]

theorem tensorInclusion_mono (J M : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι] :
    Mono (tensorInclusion J M ι) := by
  apply ModuleLocal.mono_of_local
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U.1,hx,?_⟩
  have : CategoryTheory.Limits.PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor U.1.ι) := by
    have : CategoryTheory.Limits.PreservesFiniteLimits
        (Scheme.Modules.restrictFunctor U.1.ι ⋙ Scheme.Modules.toPresheaf U.1.toScheme) := by
      change CategoryTheory.Limits.PreservesFiniteLimits
        (Scheme.Modules.toPresheaf X ⋙ (Functor.whiskeringLeft _ _ _).obj U.1.ι.opensFunctor.op)
      have : CategoryTheory.Limits.PreservesFiniteLimits
          (Scheme.Modules.toPresheaf X) := inferInstance
      have : CategoryTheory.Limits.PreservesFiniteLimits
          ((Functor.whiskeringLeft _ _ Ab).obj U.1.ι.opensFunctor.op) := inferInstance
      exact CategoryTheory.Limits.comp_preservesFiniteLimits _ _
    exact CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves _
      (Scheme.Modules.toPresheaf U.1.toScheme)
  have hm : Mono ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom) := by
    let restrictionFunctor : X.Modules ⥤ U.1.toScheme.Modules :=
      Scheme.Modules.restrictFunctor U.1.ι
    let unitRestriction : restrictionFunctor.obj (O X) ≅ O U.1.toScheme :=
      Scheme.Modules.restrictUnitIso U.1.ι
    let twist : O U.1.toScheme ≅ O U.1.toScheme := tensorUnitTwist M U.1 f
    have restricted_mono : Mono (restrictionFunctor.map ι) := inferInstance
    have scalar_mono : Mono ((e.inv ≫ restrictionFunctor.map ι ≫ unitRestriction.hom) ≫
        twist.inv) := inferInstance
    exact (congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme => Mono morphism)
      (tensor_inclusion_framed J M ι U.1 e f)).mpr scalar_mono
  exact (mono_comp_iff_of_mono _ f.hom).mp
    ((mono_comp_iff_of_isIso (tensorFrame J M U.1 e f).inv _).mp hm)

lemma tensor_inclusion_ideal (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom))} =
    Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let scalar : O U.1.toScheme ⟶ O U.1.toScheme := e.inv ≫
    (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom
  let twist : O U.1.toScheme ≅ O U.1.toScheme := tensorUnitTwist M U.1 f
  have framed : (tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom =
      scalar ≫ twist.inv := tensor_inclusion_framed J M ι U.1 e f
  refine (congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme =>
    Ideal.span {U.1.topIso.hom (endValue morphism)}) framed).trans ?_
  change Ideal.span {U.1.topIso.hom (endValue (scalar ≫ twist.inv))} =
    Ideal.span {U.1.topIso.hom (endValue scalar)}
  rw [endValue_comp, map_mul, ← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue twist.inv) :=
    (end_isIso_iff twist.inv).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom), Ideal.mul_top]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_PowerIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

lemma affineMapCoefficient_comp {M N P : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme)
    (g : P.restrict U.1.ι ≅ O U.1.toScheme) (a : M ⟶ N) (b : N ⟶ P) :
    affineMapCoefficient U e g (a ≫ b) =
      affineMapCoefficient U e f a * affineMapCoefficient U f g b := by
  unfold affineMapCoefficient
  rw [← map_mul,← endValue_comp]
  simp only [Functor.map_comp,Category.assoc,Iso.hom_inv_id_assoc]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_IdealSectionLifting
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma InvertibleLocal.pullback_frame_equation {I : X.IdealSheafData} {f : Y ⟶ X}
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    (I.ideal V).map (f.appLE V.1 U.1 hUV).hom =
      Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι} := by
  let g : O U.1.toScheme ⟶ O U.1.toScheme :=
    e.inv ≫ MaximalSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι
  have H : ((I.comap f).comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ =
      Ideal.span {endValue g} := by
    change _ = Ideal.span {UnitEndomorphism.equation g ⊤}
    rw [← UnitEndomorphism.image_principal g ⊤,
      ← MaximalSeshadri.InvertibleLocal.restricted_image_on_chart J ι hJ U.1.ι
        ⟨⊤,isAffineOpen_top _⟩ V (by simpa only [Scheme.Opens.ι_image_top] using hUV)]
    ext r
    change (∃ s, (MaximalSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤) s = r) ↔
      ∃ s, (MaximalSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤)
        (e.inv.val.app (.op ⊤) s) = r
    constructor
    · rintro ⟨s,hs⟩
      refine ⟨e.hom.val.app (.op ⊤) s,?_⟩
      have ht : e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) s) = s :=
        congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
          k.val.app (.op ⊤) s) e.hom_inv_id
      rw [ht]; exact hs
    · rintro ⟨s,hs⟩; exact ⟨e.inv.val.app (.op ⊤) s,hs⟩
  rw [IdealPullback.comap_ι_top,IdealPullback.comap_ideal I f U V hUV] at H
  have H' := congrArg (Ideal.map U.1.topIso.hom.hom) H
  rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H'
  have hi : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ := by
    ext x; exact U.1.topIso.inv_hom_id_apply x
  rw [hi,Ideal.map_id] at H'
  exact H'

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_IdealProductDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma lift_of_local_module_lifts {M N P : X.Modules} (ι : N ⟶ P) [Mono ι]
    (s : M ⟶ P) (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ t : M.restrict U.ι ⟶ N.restrict U.ι,
        t ≫ (Scheme.Modules.restrictFunctor U.ι).map ι =
          (Scheme.Modules.restrictFunctor U.ι).map s) :
    ∃ t : M ⟶ N, t ≫ ι = s := by
  have hz : s ≫ cokernel.π ι = 0 := by
    apply MaximalSeshadri.ModuleLocal.eq_zero_of_local
    intro x
    obtain ⟨U,hx,t,ht⟩ := hs x
    refine ⟨U,hx,?_⟩
    rw [Functor.map_comp,← ht,Category.assoc,← Functor.map_comp,
      cokernel.condition,Functor.map_zero,comp_zero]
  exact ⟨Abelian.monoLift _ s hz,Abelian.monoLift_comp _ s hz⟩

lemma ideal_inclusion_lift (A B : LineBundle X) (a : A.sheaf ⟶ O X)
    (b : B.sheaf ⟶ O X) [Mono b]
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : A.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ f : B.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) a} ≤
        Ideal.span {affineMapCoefficient U f (Scheme.Modules.restrictUnitIso U.1.ι) b}) :
    ∃ φ : A.sheaf ⟶ B.sheaf, φ ≫ b = a := by
  apply lift_of_local_module_lifts b a
  intro x
  obtain ⟨U,hx,e,f,hh⟩ := h x
  have hm := hh (Ideal.subset_span (Set.mem_singleton
    (affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) a)))
  obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp hm
  obtain ⟨t,ht⟩ := framed_local_division f (Scheme.Modules.restrictUnitIso U.1.ι)
    ((Scheme.Modules.restrictFunctor U.1.ι).map b)
    (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map a) (by
      rw [Ideal.mem_span_singleton]
      refine ⟨U.1.topIso.inv c,?_⟩
      have H := congrArg U.1.topIso.inv hc
      simpa only [affineMapCoefficient,map_mul,U.1.topIso.hom_inv_id_apply,
        coefficient,Category.assoc] using H)
  refine ⟨U.1,hx,e.hom ≫ t,?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun morphism : O U.1.toScheme ⟶ (O X).restrict U.1.ι =>
      e.hom ≫ morphism) ht).trans (e.hom_inv_id_assoc _))

lemma ideal_inclusions_iso (A B : LineBundle X) (a : A.sheaf ⟶ O X)
    (b : B.sheaf ⟶ O X) [Mono a] [Mono b]
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : A.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ f : B.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) a} =
        Ideal.span {affineMapCoefficient U f (Scheme.Modules.restrictUnitIso U.1.ι) b}) :
    Nonempty (A.sheaf ≅ B.sheaf) := by
  obtain ⟨φ,hφ⟩ := ideal_inclusion_lift A B a b (fun x => by
    obtain ⟨U,hx,e,f,he⟩ := h x
    exact ⟨U,hx,e,f,he.le⟩)
  obtain ⟨ψ,hψ⟩ := ideal_inclusion_lift B A b a (fun x => by
    obtain ⟨U,hx,e,f,he⟩ := h x
    exact ⟨U,hx,f,e,he.ge⟩)
  exact ⟨⟨φ,ψ,by apply (cancel_mono a).mp; simp [Category.assoc,hφ,hψ],
    by apply (cancel_mono b).mp; simp [Category.assoc,hφ,hψ]⟩⟩

lemma finiteTensorInclusion_mono (n : ℕ) (J : Fin n → LineBundle X)
    (a : ∀ i, (J i).sheaf ⟶ O X) (ha : ∀ i, Mono (a i)) :
    Mono (finiteTensorInclusion n J a) := by
  induction n with
  | zero => change Mono (𝟙 _); infer_instance
  | succ n ih =>
    exact mono_comp'
      (@tensorInclusion_mono X (J 0) (finiteTensor n (fun i => J i.succ)) (a 0) (ha 0))
      (ih (fun i => J i.succ) (fun i => a i.succ) (fun i => ha i.succ))

lemma finiteTensorInclusion_ideal (U : X.affineOpens) (n : ℕ) (J : Fin n → LineBundle X)
    (a : ∀ i, (J i).sheaf ⟶ O X)
    (e : ∀ i, (J i).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {affineMapCoefficient U (finiteTensorFrame U.1 n J e)
      (Scheme.Modules.restrictUnitIso U.1.ι) (finiteTensorInclusion n J a)} =
    ∏ i : Fin n, Ideal.span {affineMapCoefficient U (e i) (Scheme.Modules.restrictUnitIso U.1.ι) (a i)} := by
  let unitFrame : (O X).restrict U.1.ι ≅ O U.1.toScheme :=
    Scheme.Modules.restrictUnitIso U.1.ι
  change Ideal.span {affineMapCoefficient U (finiteTensorFrame U.1 n J e)
    unitFrame (finiteTensorInclusion n J a)} =
    ∏ i : Fin n, Ideal.span {affineMapCoefficient U (e i) unitFrame (a i)}
  induction n with
  | zero =>
    change Ideal.span {affineMapCoefficient U unitFrame unitFrame (𝟙 (O X))} = _
    have hidentity : affineMapCoefficient U unitFrame unitFrame (𝟙 (O X)) = 1 := by
      let restrictionFunctor : X.Modules ⥤ U.1.toScheme.Modules :=
        Scheme.Modules.restrictFunctor U.1.ι
      change U.1.topIso.hom (endValue
        (unitFrame.inv ≫ restrictionFunctor.map (𝟙 (O X)) ≫ unitFrame.hom)) = 1
      rw [restrictionFunctor.map_id,Category.id_comp,unitFrame.inv_hom_id,
        endValue_id,map_one]
    simp only [hidentity,Ideal.span_singleton_one,Fin.prod_univ_zero,Ideal.one_eq_top]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change Ideal.span {affineMapCoefficient U (tensorFrame (J 0)
      (finiteTensor n (fun i => J i.succ)) U.1 (e 0)
      (finiteTensorFrame U.1 n (fun i => J i.succ) (fun i => e i.succ)))
      unitFrame (tensorInclusion (J 0) (finiteTensor n (fun i => J i.succ)) (a 0) ≫
        finiteTensorInclusion n (fun i => J i.succ) (fun i => a i.succ))} = _
    rw [affineMapCoefficient_comp U _
      (finiteTensorFrame U.1 n (fun i => J i.succ) (fun i => e i.succ)) unitFrame
      (tensorInclusion (J 0) (finiteTensor n (fun i => J i.succ)) (a 0))
      (finiteTensorInclusion n (fun i => J i.succ) (fun i => a i.succ)),
      ← Ideal.span_singleton_mul_span_singleton,ih]
    congr 1
    exact tensor_inclusion_ideal _ _ _ _ _ _

lemma finite_common_frames {α : Type} [Fintype α] (J : α → LineBundle X)
    (x : X) (W : X.Opens) (hxW : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      Nonempty (∀ i, (J i).sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
  classical
  choose V hx e using fun i => (J i).locallyRankOne x
  let V' := W ⊓ ⨅ i, V i
  have hx' : x ∈ V' := ⟨hxW,by rw [Opens.coe_iInf]; exact Set.mem_iInter.mpr hx⟩
  obtain ⟨U,hU,hxU,hUV⟩ := exists_isAffineOpen_mem_and_subset hx'
  refine ⟨⟨U,hU⟩,hxU,hUV.trans inf_le_left,⟨fun i =>
    frameOnSmaller (Classical.choice (e i)) U (hUV.trans (inf_le_right.trans (iInf_le V i)))⟩⟩

lemma idealSheaf_prod_ideal {α : Type*} (s : Finset α) (I : α → X.IdealSheafData)
    (U : X.affineOpens) : (∏ i ∈ s, I i).ideal U = ∏ i ∈ s, (I i).ideal U := by
  classical
  induction s using Finset.induction with
  | empty => simp [Scheme.IdealSheafData.ideal_top]
  | insert a s ha ih => simp only [Finset.prod_insert ha,Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply,ih]

lemma curveDegree_finiteTensor (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (n : ℕ) (J : Fin n → LineBundle S.scheme) (C : IntegralCurve S) :
    curveDegree S (finiteTensor n J) C = ∑ i, curveDegree S (J i) C := by
  induction n with
  | zero =>
    change curveDegree S (A.pow 0) C = _
    rw [curveDegree_pow_s01 S A hA]
    simp
  | succ n ih =>
    change curveDegree S ((J 0).tensor (finiteTensor n (fun i => J i.succ))) C = _
    rw [curveDegree_tensor_s01 S A hA,ih,Fin.sum_univ_succ]

theorem PointBlowup.total_ideal_degree_s01_oai (S : Surface) {r : ℕ} {p : Configuration S r}
    (B : PointBlowup S r p) (A : LineBundle B.surface.scheme) (hA : A.IsAmple)
    (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
    (C : IntegralCurve B.surface) :
    curveDegree B.surface J C = ∑ i,curveDegree B.surface (B.exceptionalIdeal i) C := by
  classical
  let T := finiteTensor r B.exceptionalIdeal
  let a := finiteTensorInclusion r B.exceptionalIdeal B.exceptionalInclusion
  let : Mono (C := B.surface.scheme.Modules) ι := hJ.1
  let : Mono (C := B.surface.scheme.Modules) a :=
    finiteTensorInclusion_mono r B.exceptionalIdeal B.exceptionalInclusion
    (fun i => (B.exceptionalPullback i).1)
  obtain ⟨e⟩ := ideal_inclusions_iso J T ι a (fun y => by
    obtain ⟨V,hV,hyV,-⟩ := exists_isAffineOpen_mem_and_subset
      (show B.projection y ∈ (⊤ : S.scheme.Opens) from trivial)
    let VV : S.scheme.affineOpens := ⟨V,hV⟩
    obtain ⟨W,hyW,⟨eW⟩⟩ := J.locallyRankOne y
    obtain ⟨U,hyU,hUW,⟨f⟩⟩ := finite_common_frames B.exceptionalIdeal y
      (W ⊓ B.projection ⁻¹ᵁ V) ⟨hyW,hyV⟩
    let eU := frameOnSmaller eW U.1 (hUW.trans inf_le_left)
    refine ⟨U,hyU,eU,finiteTensorFrame U.1 r B.exceptionalIdeal f,?_⟩
    refine (InvertibleLocal.pullback_frame_equation J ι hJ U VV
      (hUW.trans inf_le_right) eU).symm.trans ?_
    refine Eq.trans ?_ (finiteTensorInclusion_ideal U r B.exceptionalIdeal
      B.exceptionalInclusion f).symm
    change ((∏ i, (p.val i).left.ker).ideal VV).map _ = _
    rw [idealSheaf_prod_ideal,show Ideal.map _ (∏ i, (p.val i).left.ker.ideal VV) =
      ∏ i, Ideal.map _ ((p.val i).left.ker.ideal VV) from
        map_prod (Ideal.mapHom _) _ _]
    apply Finset.prod_congr rfl
    intro i hi
    exact InvertibleLocal.pullback_frame_equation _ _ (B.exceptionalPullback i) U VV
      (hUW.trans inf_le_right) (f i))
  have he : curveDegree B.surface J C = curveDegree B.surface T C := by
    unfold curveDegree
    rw [eulerCharacteristic_iso (C.embedding ≫ B.surface.structureMap)
      ((Scheme.Modules.pullback C.embedding).mapIso e) 1]
  rw [he]
  exact curveDegree_finiteTensor B.surface A hA r B.exceptionalIdeal C

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree_s01_oai := @OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree_s01_oai
