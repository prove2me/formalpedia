-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_ideal_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:18:27.721527+00:00
-- url     : https://prove2.me/submissions/501c969f-2b5b-412e-ad82-d40d21fac5b1

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

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
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_TwistedIdealPower
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

lemma affineMapCoefficient_iso_left {M N P : X.Modules} (U : X.affineOpens)
    (c : M ≅ N) (e : N.restrict U.1.ι ≅ O U.1.toScheme)
    (f : P.restrict U.1.ι ≅ O U.1.toScheme) (a : N ⟶ P) :
    affineMapCoefficient U ((Scheme.Modules.restrictFunctor U.1.ι).mapIso c ≪≫ e)
      f (c.hom ≫ a) = affineMapCoefficient U e f a := by
  simp only [affineMapCoefficient,Iso.trans_inv,Functor.mapIso_inv,Functor.map_comp,Category.assoc]
  rw [← Functor.map_comp_assoc,c.inv_hom_id,CategoryTheory.Functor.map_id,Category.id_comp]

lemma twistedIdealPowerInclusion_ideal_s01_oai (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (a b n : ℕ) (U : X.affineOpens)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : (L.pow (a*n)).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {affineMapCoefficient U (twistedIdealPowerFrame L J a b n U.1 e f)
      f (twistedIdealPowerInclusion L J ι a b n)} =
    (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^(b*n) := by
  unfold twistedIdealPowerFrame twistedIdealPowerInclusion
  rw [affineMapCoefficient_iso_left]
  change Ideal.span {U.1.topIso.hom (endValue _)} = _
  rw [tensor_inclusion_ideal]
  exact idealPowerInclusion_ideal J ι U e (b*n)

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_ideal_s01_oai := @OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_ideal_s01_oai
