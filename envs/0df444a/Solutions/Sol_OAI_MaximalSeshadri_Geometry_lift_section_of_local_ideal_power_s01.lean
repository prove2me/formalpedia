-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:18:26.412244+00:00
-- url     : https://prove2.me/submissions/359879d7-7a1e-4c72-8f02-b379e6e90584

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

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

lemma idealPowerInclusion_mono (J : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι]
    (n : ℕ) : Mono (idealPowerInclusion J ι n) := by
  induction n with
  | zero => change Mono (𝟙 (O X)); infer_instance
  | succ n ih =>
    let := ih
    let := tensorInclusion_mono J (J.pow n) ι
    change Mono (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n)
    infer_instance

lemma affineMapCoefficient_comp {M N P : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme)
    (g : P.restrict U.1.ι ≅ O U.1.toScheme) (a : M ⟶ N) (b : N ⟶ P) :
    affineMapCoefficient U e g (a ≫ b) =
      affineMapCoefficient U e f a * affineMapCoefficient U f g b := by
  unfold affineMapCoefficient
  rw [← map_mul,← endValue_comp]
  simp only [Functor.map_comp,Category.assoc,Iso.hom_inv_id_assoc]

lemma idealPowerInclusion_ideal (J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (n : ℕ) :
    Ideal.span {affineMapCoefficient U (idealPowerFrame J U.1 e n)
      (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n)} =
      (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^n := by
  let unitFrame : (O X).restrict U.1.ι ≅ O U.1.toScheme :=
    Scheme.Modules.restrictUnitIso U.1.ι
  change Ideal.span {affineMapCoefficient U (idealPowerFrame J U.1 e n)
    unitFrame (idealPowerInclusion J ι n)} = (Ideal.span {affineMapCoefficient U e unitFrame ι})^n
  induction n with
  | zero =>
    change Ideal.span {affineMapCoefficient U unitFrame unitFrame (𝟙 (O X))} = _
    have hidentity : affineMapCoefficient U unitFrame unitFrame (𝟙 (O X)) = 1 := by
      let restrictionFunctor : X.Modules ⥤ U.1.toScheme.Modules :=
        Scheme.Modules.restrictFunctor U.1.ι
      change U.1.topIso.hom (endValue
        (unitFrame.inv ≫ restrictionFunctor.map (𝟙 (O X)) ≫ unitFrame.hom)) = 1
      rw [restrictionFunctor.map_id, Category.id_comp, unitFrame.inv_hom_id,
        endValue_id, map_one]
    rw [hidentity, Ideal.span_singleton_one, pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    change Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      unitFrame (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n)} = _
    rw [affineMapCoefficient_comp U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (idealPowerFrame J U.1 e n) unitFrame (tensorInclusion J (J.pow n) ι)
      (idealPowerInclusion J ι n),
      ← Ideal.span_singleton_mul_span_singleton,ih]
    rw [show Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (idealPowerFrame J U.1 e n) (tensorInclusion J (J.pow n) ι)} =
      Ideal.span {affineMapCoefficient U e unitFrame ι} from
        tensor_inclusion_ideal J (J.pow n) ι U e (idealPowerFrame J U.1 e n)]
    rw [pow_succ']

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

lemma ideal_power_tensor_equation (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (M : LineBundle Y) (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (d : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {affineMapCoefficient U
      (tensorFrame (J.pow n) M U.1 (idealPowerFrame J U.1 d n) e) e
      (tensorInclusion (J.pow n) M (idealPowerInclusion J ι n))} =
      ((I.ideal V)^n).map (f.appLE V.1 U.1 hUV).hom := by
  trans Ideal.span {affineMapCoefficient U (idealPowerFrame J U.1 d n)
    (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n)}
  · exact tensor_inclusion_ideal (J.pow n) M (idealPowerInclusion J ι n) U _ e
  rw [idealPowerInclusion_ideal,← InvertibleLocal.pullback_frame_equation J ι hJ U V hUV,
    Ideal.map_pow]

theorem lift_section_of_local_ideal_power_s01_oai (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (M : LineBundle X) (n : ℕ) (s : O X ⟶ M.sheaf)
    (hs : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ e : M.sheaf.restrict V.1.ι ≅ O V.1.toScheme,
        affineCoefficient V e s ∈ (I.ideal V)^n) :
    ∃! q : O Y ⟶ ((J.pow n).tensor (M.pullback f)).sheaf,
      q ≫ tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n) =
        pullbackSection f s := by
  let hmono : Mono (C := Y.Modules) (idealPowerInclusion J ι n) :=
    @idealPowerInclusion_mono Y J ι hJ.1 n
  let : Mono (C := Y.Modules)
      (tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n)) :=
    @tensorInclusion_mono Y (J.pow n) (M.pullback f) (idealPowerInclusion J ι n) hmono
  apply global_division_of_local_lifts
  intro y
  obtain ⟨V,hyV,eV,hsV⟩ := hs (f y)
  obtain ⟨eF,heF⟩ := pullback_affine_coefficient f V eV
  obtain ⟨W,hyW,⟨eW⟩⟩ := J.locallyRankOne y
  obtain ⟨_,⟨U₀,hU₀,rfl⟩,hyU,hUW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ W ⊓ f ⁻¹ᵁ V.1 from ⟨hyW,hyV⟩) (W ⊓ f ⁻¹ᵁ V.1).isOpen
  let U : Y.affineOpens := ⟨U₀,hU₀⟩
  let d := frameOnSmaller eW U.1 (fun z hz => (hUW hz).1)
  let e : (M.pullback f).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
    frameOnSmaller eF U.1 (fun z hz => (hUW hz).2)
  let d' := idealPowerFrame J U.1 d n
  have hm : affineCoefficient U e (pullbackSection f s) ∈
      Ideal.span {affineMapCoefficient U (tensorFrame (J.pow n) (M.pullback f) U.1 d' e)
        e (tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n))} := by
    dsimp only [d']
    rw [ideal_power_tensor_equation f I J ι hJ (M.pullback f) n U V
      (fun z hz => (hUW hz).2) d e]
    have hcoeff : affineCoefficient U e (pullbackSection f s) =
        f.appLE V.1 U.1 (fun z hz => (hUW hz).2) (affineCoefficient V eV s) :=
      heF U (fun z hz => (hUW hz).2) s
    rw [hcoeff]
    exact Ideal.mem_map_of_mem _ hsV
  refine ⟨U.1,hyU,?_⟩
  apply framed_local_division (tensorFrame (J.pow n) (M.pullback f) U.1 d' e) e
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp hm
  rw [Ideal.mem_span_singleton]
  refine ⟨U.1.topIso.inv a,?_⟩
  have H := congrArg U.1.topIso.inv ha
  simpa only [affineCoefficient,affineMapCoefficient,map_mul,U.1.topIso.hom_inv_id_apply] using H

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power_s01_oai := @OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power_s01_oai
