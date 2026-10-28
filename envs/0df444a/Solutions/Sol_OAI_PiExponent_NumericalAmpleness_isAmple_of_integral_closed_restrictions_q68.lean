-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:24:16.277989+00:00
-- url     : https://prove2.me/submissions/6292b764-b00d-4fd0-bb3d-ed89b097d26c

import Mathlib
import Definitions.Def_OAIQ068A039
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A041
import Theorems.Thm_OAI_PiExponentSeshadri_ComponentAmpleDescent_isAmple_of_reduced_closed_cover_q68
import Theorems.Thm_OAI_PiExponentSeshadri_Geometry_eventual_twist_ext_zero_of_closed_pushforward_q68
import Theorems.Thm_OAI_PiExponentSeshadri_Geometry_isAffineOpen_of_fullSupport_preimage_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ClosedAmpleBaseChange
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_additive _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_preservesZero _root_.OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_additive _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ReducedComponentAmple
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}}

theorem isAmple_comap_restriction (I : X.IdealSheafData) (f : Y ⟶ X)
    [IsClosedImmersion f] (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) :
    ((L.pullback f).pullback (I.comap f).subschemeι).IsAmple :=
  PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ (closedBaseChangeLineIso I f L)
    (LineBundle.IsAmple.pullback_closedImmersion _ hL (closedBaseChange I f))

end PiExponent.ReducedComponentAmple

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedRestrictionTensor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ClosedRestrictionTensor
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure

lemma tensor_map_pure_val {Z : Scheme.{0}} {M N P Q : Z.Modules}
    (a : M ⟶ P) (b : N ⟶ Q) (U : Z.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorMap a b).val.app (op U) (pure M N U m n) =
      pure P Q U (a.val.app (op U) m) (b.val.app (op U) n) :=
  map_pure a b U m n

lemma tensor_comm_pure_val {Z : Scheme.{0}} (M N : Z.Modules) (U : Z.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorComm M N).hom.val.app (op U) (pure M N U m n) =
      pure N M U n m := moduleTensorComm_pure M N U m n

lemma projection_hom_pure_val {X Y : Scheme.{0}} (f : X ⟶ Y)
    (M : X.Modules) (L : Y.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (s : L.val.obj (op U)) :
    (ProjectionFormula.hom f M L).val.app (op U)
      (pure ((Scheme.Modules.pushforward f).obj M) L U m s) =
      pure M ((Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U) m
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (op U) s) :=
  ProjectionFormula.hom_pure f M L U m s

lemma pushforward_hom_pure_val {X Y : Scheme.{0}} (f : X ⟶ Y)
    (M N : X.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (n : N.val.obj (op (f ⁻¹ᵁ U))) :
    (PiExponentSeshadri.PushforwardTensor.hom f M N).val.app (op U)
      (pure ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) U m n) =
      pure M N (f ⁻¹ᵁ U) m n :=
  PiExponentSeshadri.PushforwardTensor.hom_pure f M N U m n

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LineBundle Y)

lemma powerProjectionIso_succ_pure (n : ℕ) (U : Y.Opens)
    (m : ((moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj (O X))).val.obj (op U))
    (s : L.sheaf.val.obj (op U)) :
    (powerProjectionIso f L (n+1)).hom.val.app (op U)
      (pure _ L.sheaf U m s) =
      pure (L.pullback f).sheaf ((L.pullback f).pow n).sheaf (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
        ((powerProjectionIso f L n).hom.val.app (op U) m) := by
  change (moduleTwistUnitIso (L.pullback f) (n+1)).hom.val.app (op (f ⁻¹ᵁ U))
    ((ProjectionFormula.hom f ((moduleTwistFunctor (L.pullback f) n).obj (O X)) L.sheaf).val.app (op U)
      ((moduleTensorMap (ProjectionFormula.twistIso f (O X) L n).inv (𝟙 L.sheaf)).val.app (op U)
        (pure _ L.sheaf U m s))) = _
  rw [tensor_map_pure_val]
  change (moduleTensorComm ((L.pullback f).pow n).sheaf (L.pullback f).sheaf).hom.val.app (op (f ⁻¹ᵁ U))
    ((moduleTensorMap (moduleTwistUnitIso (L.pullback f) n).hom (𝟙 (L.pullback f).sheaf)).val.app (op (f ⁻¹ᵁ U))
      ((ProjectionFormula.hom f ((moduleTwistFunctor (L.pullback f) n).obj (O X)) L.sheaf).val.app (op U)
        (pure _ L.sheaf U ((ProjectionFormula.twistIso f (O X) L n).inv.val.app (op U) m) s))) = _
  erw [projection_hom_pure_val f ((moduleTwistFunctor (L.pullback f) n).obj (O X))
    L.sheaf U ((ProjectionFormula.twistIso f (O X) L n).inv.val.app (op U) m) s]
  have ht := tensor_map_pure_val (Z := X) (moduleTwistUnitIso (L.pullback f) n).hom
    (𝟙 (L.pullback f).sheaf) (f ⁻¹ᵁ U)
    ((ProjectionFormula.twistIso f (O X) L n).inv.val.app (op U) m)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
  exact (congrArg (fun r => (moduleTensorComm ((L.pullback f).pow n).sheaf
    (L.pullback f).sheaf).hom.val.app (op (f ⁻¹ᵁ U)) r) ht).trans
      (tensor_comm_pure_val _ _ _ _ _)

lemma powerUnit_succ_pure (n : ℕ) (U : Y.Opens)
    (s : L.sheaf.val.obj (op U)) (m : (L.pow n).sheaf.val.obj (op U)) :
    (powerUnit f L (n+1)).val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m) =
      pure (L.pullback f).sheaf ((L.pullback f).pow n).sheaf (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
        ((powerUnit f L n).val.app (op U) m) := by
  have h := PiExponentSeshadri.PullbackTensor.unit_hom f L.sheaf (L.pow n).sheaf
  have hp := congrArg (fun q => q.val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m)) h
  change (PiExponentSeshadri.PullbackTensor.hom f L.sheaf (L.pow n).sheaf).val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (moduleTensor Y L.sheaf (L.pow n).sheaf)).val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m)) =
    (PiExponentSeshadri.PushforwardTensor.hom f _ _).val.app (op U)
      ((moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf)).val.app (op U)
        (pure L.sheaf (L.pow n).sheaf U s m)) at hp
  have hm := tensor_map_pure_val (Z := Y)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf) U s m
  have hv := pushforward_hom_pure_val f ((Scheme.Modules.pullback f).obj L.sheaf)
    ((Scheme.Modules.pullback f).obj (L.pow n).sheaf) U
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf).val.app (op U) m)
  have hp' := hp.trans ((congrArg (fun r => (PiExponentSeshadri.PushforwardTensor.hom f
    ((Scheme.Modules.pullback f).obj L.sheaf) ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).val.app
      (op U) r) hm).trans hv)
  change (moduleTensorMap (𝟙 (L.pullback f).sheaf) (PiExponentSeshadri.PullbackTensor.powIso f L n).hom).app
    (f ⁻¹ᵁ U)
    ((PiExponentSeshadri.PullbackTensor.hom f L.sheaf (L.pow n).sheaf).val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (moduleTensor Y L.sheaf (L.pow n).sheaf)).val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m))) = _
  exact (congrArg (fun r => (moduleTensorMap (𝟙 (L.pullback f).sheaf)
    (PiExponentSeshadri.PullbackTensor.powIso f L n).hom).val.app (op (f ⁻¹ᵁ U)) r) hp').trans
      (tensor_map_pure_val (Z := X) (𝟙 (L.pullback f).sheaf)
        (PiExponentSeshadri.PullbackTensor.powIso f L n).hom _ _ _)

theorem twist_structureMap_power (n : ℕ) :
    (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
        (powerProjectionIso f L n).hom =
      (moduleTwistUnitIso L n).hom ≫ powerUnit f L n := by
  induction n with
  | zero =>
    change PiExponentSeshadri.IdealModule.structureMap f =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
        (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom
    exact (pullbackUnit_adjunction f).symm
  | succ n ih =>
    apply PiExponentSeshadri.TensorPure.hom_ext
    intro U m s
    change (powerProjectionIso f L (n+1)).hom.val.app (op U)
      ((moduleTensorMap ((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f))
        (𝟙 L.sheaf)).val.app (op U) (pure _ L.sheaf U m s)) =
      (powerUnit f L (n+1)).val.app (op U)
        ((moduleTensorComm (L.pow n).sheaf L.sheaf).hom.val.app (op U)
          ((moduleTensorMap (moduleTwistUnitIso L n).hom (𝟙 L.sheaf)).val.app (op U)
            (pure _ L.sheaf U m s)))
    have h1 := tensor_map_pure_val (Z := Y)
      ((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)) (𝟙 L.sheaf) U m s
    have h2 := powerProjectionIso_succ_pure f L n U
      (((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)).val.app (op U) m) s
    have h3 := tensor_map_pure_val (Z := Y) (moduleTwistUnitIso L n).hom (𝟙 L.sheaf) U m s
    have h4 := tensor_comm_pure_val (L.pow n).sheaf L.sheaf U
      ((moduleTwistUnitIso L n).hom.val.app (op U) m) s
    have h5 := powerUnit_succ_pure f L n U s ((moduleTwistUnitIso L n).hom.val.app (op U) m)
    have hleft := (congrArg (fun r => (powerProjectionIso f L (n+1)).hom.val.app (op U) r) h1).trans h2
    have hright := (congrArg (fun r => (powerUnit f L (n+1)).val.app (op U) r)
      ((congrArg (fun r => (moduleTensorComm (L.pow n).sheaf L.sheaf).hom.val.app (op U) r) h3).trans h4)).trans h5
    exact hleft.trans ((congrArg (fun r => pure (L.pullback f).sheaf ((L.pullback f).pow n).sheaf
      (f ⁻¹ᵁ U) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s) r)
      (congrArg (fun q => q.val.app (op U) m) ih)).trans hright.symm)

theorem power_restriction_eq (n : ℕ) :
    (moduleTwistUnitIso L n).inv ≫
      (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
      (ProjectionFormula.twistIso f (O X) L n).inv ≫
      (Scheme.Modules.pushforward f).map (moduleTwistUnitIso (L.pullback f) n).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf ≫
      (Scheme.Modules.pushforward f).map (PiExponentSeshadri.PullbackTensor.powIso f L n).hom := by
  change (moduleTwistUnitIso L n).inv ≫
    ((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
      (powerProjectionIso f L n).hom) = powerUnit f L n
  erw [twist_structureMap_power, Iso.inv_hom_id_assoc]

theorem push_pullbackSection {M : Y.Modules} (s : O Y ⟶ M) :
    PiExponentSeshadri.IdealModule.structureMap f ≫
      (Scheme.Modules.pushforward f).map (pullbackSection f s) =
      s ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
  have hu : PiExponentSeshadri.IdealModule.structureMap f =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
        (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom :=
    (pullbackUnit_adjunction f).symm
  let F := Scheme.Modules.pushforward f
  let P := Scheme.Modules.pullback f
  let e := pullbackUnitIso f
  have h := (F.map_comp e.hom (e.inv ≫ P.map s)).symm.trans
    (congrArg F.map (e.hom_inv_id_assoc (P.map s)))
  calc
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
        F.map e.hom) ≫ F.map (e.inv ≫ P.map s) :=
      congrArg (fun q : O Y ⟶ F.obj (O X) => q ≫ F.map (pullbackSection f s)) hu
    _ = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫ F.map (P.map s) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫ q) h)
    _ = _ := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality s).symm

theorem section_restriction_eq (n : ℕ) (s : O Y ⟶ (L.pow n).sheaf) :
    s ≫ (moduleTwistUnitIso L n).inv ≫
      (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
      (ProjectionFormula.twistIso f (O X) L n).inv ≫
      (Scheme.Modules.pushforward f).map (moduleTwistUnitIso (L.pullback f) n).hom =
    PiExponentSeshadri.IdealModule.structureMap f ≫
      (Scheme.Modules.pushforward f).map (pullbackPowerSection L f n s) := by
  erw [power_restriction_eq]
  symm
  simp only [pullbackPowerSection]
  erw [(Scheme.Modules.pushforward f).map_comp (pullbackSection f s)
    (PiExponentSeshadri.PullbackTensor.powIso f L n).hom, ← Category.assoc,
    push_pullbackSection f s, Category.assoc]

end
end PiExponent.ClosedRestrictionTensor

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FullSupportNilpotence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme}

lemma idealSheaf_le_nilradical_of_fullSupport (I : X.IdealSheafData)
    (hI : I.support = ⊤) : I ≤ X.nilradical := by
  have h : (⊤ : Closeds X) ≤ I.support := by rw [hI]
  simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h

lemma affineIdeal_isNilpotent_of_fullSupport [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (U : X.affineOpens) :
    IsNilpotent (I.ideal U) := by
  let := IsLocallyNoetherian.component_noetherian U
  apply (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr
  exact idealSheaf_le_nilradical_of_fullSupport I hI U

theorem exists_pos_pow_eq_bot_of_fullSupport [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) :
    ∃ n : ℕ, 0 < n ∧ I ^ n = ⊥ := by
  classical
  have hlocal : ∀ U : X.affineOpens, ∃ n : ℕ, I.ideal U ^ n = ⊥ :=
    fun U => affineIdeal_isNilpotent_of_fullSupport I hI U
  choose n hn using hlocal
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen)
    (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, U.1) := by
        rw [iSup_affineOpens_eq_top X]
        trivial
      obtain ⟨U, hU⟩ := Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  refine ⟨S.sup n + 1, Nat.succ_pos _, ?_⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : S => U.val)
  · apply top_unique
    intro x _
    obtain ⟨U, hU⟩ := Set.mem_iUnion.mp (hS (show x ∈ Set.univ from trivial))
    obtain ⟨hUS, hxU⟩ := Set.mem_iUnion.mp hU
    exact Opens.mem_iSup.mpr ⟨⟨U, hUS⟩, hxU⟩
  · intro U
    change I.ideal U.val ^ (S.sup n + 1) = ⊥
    apply le_bot_iff.mp
    calc
      I.ideal U.val ^ (S.sup n + 1) ≤ I.ideal U.val ^ n U.val :=
        Ideal.pow_le_pow_right ((Finset.le_sup U.property).trans (Nat.le_succ _))
      _ = ⊥ := hn U.val

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedThickeningSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

attribute [local instance] OAI.PiExponentSeshadri.Geometry.instHasExtModules_solutions
theorem globalSections_surjective_of_ext_one_zero (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) S.X₁ 1, x = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  intro s
  obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS (Ext.mk₀ s)
    rfl (hzero _)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

theorem subscheme_surjective_of_fullSupport (I : X.IdealSheafData)
    (hI : I.support = ⊤) : Function.Surjective I.subschemeι := by
  apply Set.range_eq_univ.mp
  rw [I.range_subschemeι, hI]
  rfl

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPowerSectionLifting
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

attribute [local instance] OAI.PiExponentSeshadri.Geometry.instHasExtModules_solutions_1
theorem pullbackPowerSection_surjective_of_ideal_ext_zero (i : Y ⟶ X)
    [IsClosedImmersion i] (L : LineBundle X) (n : ℕ)
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (IdealModule.idealModule i)) 1, x = 0) :
    Function.Surjective (pullbackPowerSection L i n) := by
  let S := ShortComplex.mk (IdealModule.inclusion i) (IdealModule.structureMap i)
    (kernel.condition _)
  have hS := moduleTwistFunctor_shortExact L n S (IdealModule.closedSequence_exact i)
  have hsurj := globalSections_surjective_of_ext_one_zero (S.map (moduleTwistFunctor L n)) hS hzero
  intro σ
  let e := PiExponent.ClosedRestrictionTensor.powerProjectionIso i L n
  let b : GlobalSections X ((Scheme.Modules.pushforward i).obj ((L.pullback i).pow n).sheaf) :=
    IdealModule.structureMap i ≫ (Scheme.Modules.pushforward i).map σ
  obtain ⟨a,ha⟩ := hsurj (b ≫ e.inv)
  let t : GlobalSections X (L.pow n).sheaf := a ≫ (moduleTwistUnitIso L n).hom
  refine ⟨t, ?_⟩
  apply (PiExponent.ClosedImmersionSerreTransfer.globalHom_push_bijective i
    ((L.pullback i).pow n).sheaf).injective
  have ht := PiExponent.ClosedRestrictionTensor.section_restriction_eq i L n t
  change t ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (IdealModule.structureMap i) ≫ e.hom =
      IdealModule.structureMap i ≫ (Scheme.Modules.pushforward i).map
        (pullbackPowerSection L i n t) at ht
  change IdealModule.structureMap i ≫ (Scheme.Modules.pushforward i).map
    (pullbackPowerSection L i n t) = b
  rw [← ht]
  dsimp only [t]
  erw [Category.assoc a (moduleTwistUnitIso L n).hom,
    (moduleTwistUnitIso L n).hom_inv_id_assoc]
  change (a ≫ (moduleTwistFunctor L n).map (IdealModule.structureMap i)) ≫ e.hom = b
  have ha' : a ≫ (moduleTwistFunctor L n).map (IdealModule.structureMap i) = b ≫ e.inv := ha
  exact (congrArg (fun z => z ≫ e.hom) ha').trans (by simp only [Category.assoc,
    Iso.inv_hom_id, Category.comp_id])

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerFiltration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X : Scheme.{0}}

theorem powerSequence_shortExact (I : X.IdealSheafData) (n : ℕ) :
    (powerSequence I n).ShortExact := by
  change (ShortComplex.mk (powerMap I n) (cokernel.π (powerMap I n)) _).ShortExact
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (powerMap I n)) }

theorem closedModule_bot_isZero : IsZero (closedModule (⊥ : X.IdealSheafData)) := by
  have hmono : Mono (structureMap (Scheme.IdealSheafData.subschemeι (⊥ : X.IdealSheafData))) := by
    let F := Scheme.Modules.toPresheafOfModules X
    apply F.mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    exact (ConcreteCategory.bijective_of_isIso
      ((⊥ : X.IdealSheafData).subschemeι.app U.unop)).injective
  exact isZero_kernel_of_mono _

theorem powerModule_eventually_isZero [IsNoetherian X] (I : X.IdealSheafData)
    (hI : I.support = ⊤) : ∃ n : ℕ, 0 < n ∧ IsZero (closedModule (I^n)) := by
  obtain ⟨n, hn, he⟩ := Geometry.exists_pos_pow_eq_bot_of_fullSupport I hI
  exact ⟨n,hn,he ▸ closedModule_bot_isZero⟩

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_IdealPowerCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

attribute [local instance] OAI.PiExponentSeshadri.IdealModule.instHasExtModules_solutions
theorem ext_eq_zero_of_isZero (A M : X.Modules) (hM : IsZero M) (q : ℕ)
    (x : Abelian.Ext.{1} A M q) : x = 0 := by
  have hz := (extFunctorObj A q).map_isZero hM
  exact @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero hz) x 0

theorem powerModule_twist_ext_zero_of_layers (I : X.IdealSheafData) (L : LineBundle X)
    (N n q : ℕ) (hN : IsZero (closedModule (I^N)))
    (hLayer : ∀ k < N, ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (powerLayer I k)) q, x = 0)
    (k : ℕ) (hk : k ≤ N)
    (x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule (I^k))) q) : x = 0 := by
  have hzero : ∀ k ≤ N, ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule (I^k))) q, x = 0 := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      exact ext_eq_zero_of_isZero _ _ ((moduleTwistFunctor L n).map_isZero hN) q
    | @of_succ k hk ih =>
      intro x
      let S := (powerSequence I k).map (moduleTwistFunctor L n)
      have hS : S.ShortExact := moduleTwistFunctor_shortExact L n _ (powerSequence_shortExact I k)
      obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₂ (structureSheaf X) hS x
        (hLayer k hk _)
      have hiy : y = 0 := ih y
      exact hy.symm.trans
        ((congrArg (fun z : Abelian.Ext.{1} (structureSheaf X) S.X₁ q =>
          z.comp (Ext.mk₀ S.f) (add_zero q)) hiy).trans
            (Ext.zero_comp (structureSheaf X) q (Ext.mk₀ S.f) q (add_zero q)))
  exact hzero k hk x

attribute [local irreducible] closedModule moduleTwistFunctor powerLayer

theorem eventual_ideal_twist_vanishing_of_layers [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (L : LineBundle X)
    (hLayer : ∀ k, ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (powerLayer I k)) q, x = 0) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (closedModule I)) q, x = 0 := by
  classical
  obtain ⟨N,hNpos,hN⟩ := powerModule_eventually_isZero I hI
  choose B hB using hLayer
  refine ⟨(Finset.range N).sup B, fun n hn q hq x => ?_⟩
  have hL (k : ℕ) (hk : k < N) := hB k n
    ((Finset.le_sup (Finset.mem_range.mpr hk)).trans hn) q hq
  have h := powerModule_twist_ext_zero_of_layers I L N n q hN hL 1 hNpos
  have h' : ∀ z : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule I)) q, z = 0 := by
    exact (congrArg (fun J : X.IdealSheafData =>
      ∀ z : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (closedModule J)) q, z = 0) (pow_one I)).mp h
  exact h' x
end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ModulePullbackCoherent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponent.FiniteGlobalPresentation

theorem pullback_isFinitePresentation {X Y : Scheme.{0}} (f : Y ⟶ X)
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro y
  obtain ⟨U, hy, P, hP⟩ := exists_local_finitePresentation M (f y)
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
    Scheme.Modules.pullback (f ∣_ U)
  let : PreservesColimitsOfSize.{0,0} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let Q := P.map F (pullbackUnitIso (f ∣_ U)).symm
  let e := (pullbackRestrictNatIso f U).app M
  exact ⟨f ⁻¹ᵁ U, hy, presentationOfIso (f ⁻¹ᵁ U).toScheme e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerDescent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.ClosedAnnihilatedDescent
variable {X : Scheme.{0}}

instance descendedPowerLayer_isFinitePresentation [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) : (descendedPowerLayer I n).IsFinitePresentation := by
  have := powerLayer_isFinitePresentation I n
  exact pullback_isFinitePresentation I.subschemeι (powerLayer I n)

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_NilpotentIdealVanishing
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}}
attribute [local irreducible] closedModule powerLayer moduleTwistFunctor

local instance localInst_r1a20f2_1 : HasExt.{1} X.Modules := HasExt.standard _
theorem fullSupport_eventual_ideal_twist_ext_zero [IsNoetherian X]
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support = ⊤)
    (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (closedModule I)) q, x = 0 := by
  apply eventual_ideal_twist_vanishing_of_layers I hI L
  intro k
  exact eventual_twist_ext_zero_of_closed_pushforward_q68 p I.subschemeι L hL
    (powerLayer I k) (descendedPowerLayer I k) (powerLayerPushforwardIso I k).symm

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_NilpotentAmpleDescent
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem fullSupport_eventual_powerSection_surjective [IsNoetherian X]
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support = ⊤)
    (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) :
    ∃ B, ∀ n, B ≤ n → Function.Surjective (pullbackPowerSection L I.subschemeι n) := by
  obtain ⟨B,hB⟩ := fullSupport_eventual_ideal_twist_ext_zero p I hI L hL
  exact ⟨B, fun n hn => pullbackPowerSection_surjective_of_ideal_ext_zero I.subschemeι L n
    (hB n hn 1 (by decide))⟩

theorem LineBundle.isAmple_of_fullSupport [IsNoetherian X]
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support = ⊤)
    (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) : L.IsAmple := by
  obtain ⟨B,hB⟩ := fullSupport_eventual_powerSection_surjective p I hI L hL
  intro x V hx
  obtain ⟨y,hy⟩ := subscheme_surjective_of_fullSupport I hI x
  have hyV : y ∈ I.subschemeι ⁻¹ᵁ V := by change I.subschemeι y ∈ V; rwa [hy]
  obtain ⟨d,hd,s,hys,hsV,hsa⟩ := hL y (I.subschemeι ⁻¹ᵁ V) hyV
  let m := B+1
  have hm : 0 < m := Nat.succ_pos B
  let σ : GlobalSections I.subscheme ((L.pullback I.subschemeι).pow (d*m)).sheaf :=
    powerSection s m ≫ (linePowerMul (L.pullback I.subschemeι) d m).hom
  have hσ : sectionOpen I.subscheme σ = sectionOpen I.subscheme s := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso
      (powerSection s m) (linePowerMul (L.pullback I.subschemeι) d m)).trans
      (((L.pullback I.subschemeι).pow d).sectionOpen_power s hm)
  have hBd : B ≤ d*m := (Nat.le_succ B).trans (Nat.le_mul_of_pos_left m hd)
  obtain ⟨t,ht⟩ := hB (d*m) hBd σ
  have hpre : I.subschemeι ⁻¹ᵁ sectionOpen X t = sectionOpen I.subscheme s := by
    exact (sectionOpen_pullbackPowerSection L I.subschemeι (d*m) t).symm.trans
      ((congrArg (fun u : GlobalSections I.subscheme
        ((L.pullback I.subschemeι).pow (d*m)).sheaf => sectionOpen I.subscheme u) ht).trans hσ)
  refine ⟨d*m, Nat.mul_pos hd hm, t, ?_, ?_, ?_⟩
  · have hyT : y ∈ I.subschemeι ⁻¹ᵁ sectionOpen X t := by rw [hpre]; exact hys
    change I.subschemeι y ∈ sectionOpen X t at hyT
    rwa [hy] at hyT
  · intro z hz
    obtain ⟨w,hw⟩ := subscheme_surjective_of_fullSupport I hI z
    have hwT : w ∈ I.subschemeι ⁻¹ᵁ sectionOpen X t := by change I.subschemeι w ∈ sectionOpen X t; rwa [hw]
    rw [hpre] at hwT
    have hwV := hsV hwT
    change I.subschemeι w ∈ V at hwV
    rwa [hw] at hwV
  · apply isAffineOpen_of_fullSupport_preimage_q68 I hI
    rw [hpre]
    exact hsa

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReducedComponentAmple
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ReducedComponentAmple
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem isAmple_of_finite_closed_cover {ι : Type*} (s : Finset ι) :
    ∀ {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
      (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
      (L H : LineBundle X), H.IsAmple →
      ∀ I : ι → X.IdealSheafData,
      (∀ x : X, ∃ i ∈ s, x ∈ (I i).support) →
      (∀ i ∈ s, (L.pullback (I i).subschemeι).IsAmple) → L.IsAmple := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro X _ _ p _ L H hH I hcover hample x U hx
    obtain ⟨i,hi,_⟩ := hcover x
    simp at hi
  | @insert i s hi ih =>
    intro X _ _ p _ L H hH I hcover hample
    let Z : Closeds X := s.sup (fun j => (I j).support)
    let J : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
    have hJsupport : J.support = Z := by
      ext x
      simp only [J, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    let : IsLocallyNoetherian J.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
    let : CompactSpace J.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace J.subschemeι
    let : IsNoetherian J.subscheme := {}
    let : IsReduced J.subscheme := NumericalAmpleness.isReduced_vanishingIdeal_subscheme Z
    have hH' : (H.pullback J.subschemeι).IsAmple :=
      LineBundle.IsAmple.pullback_closedImmersion H hH J.subschemeι
    have hcoverJ : ∀ x : J.subscheme, ∃ j ∈ s,
        x ∈ ((I j).comap J.subschemeι).support := by
      intro x
      have hx : J.subschemeι x ∈ Z := by
        rw [← hJsupport]
        exact x.property
      have hx' : ∃ j ∈ s, J.subschemeι x ∈ ((I j).support : Set X) := by
        change J.subschemeι x ∈ ((s.sup (fun j => (I j).support) : Closeds X) : Set X) at hx
        rw [Closeds.coe_finset_sup] at hx
        simpa only [Finset.sup_eq_iSup, Function.comp_apply, Set.iSup_eq_iUnion,
          Set.mem_iUnion, exists_prop] using hx
      obtain ⟨j,hj,hxj⟩ := hx'
      refine ⟨j,hj,?_⟩
      rw [Scheme.IdealSheafData.support_comap]
      change J.subschemeι x ∈ ((I j).support : Set X)
      exact hxj
    have hampleJ : ∀ j ∈ s,
        ((L.pullback J.subschemeι).pullback ((I j).comap J.subschemeι).subschemeι).IsAmple := by
      intro j hj
      exact isAmple_comap_restriction (I j) J.subschemeι L
        (hample j (Finset.mem_insert_of_mem hj))
    have hJ : (L.pullback J.subschemeι).IsAmple :=
      ih (J.subschemeι ≫ p) (L.pullback J.subschemeι) (H.pullback J.subschemeι)
        hH' (fun j => (I j).comap J.subschemeι) hcoverJ hampleJ
    apply PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover_q68
      p L H hH (I i) J ?_ (hample i (Finset.mem_insert_self _ _)) hJ
    apply top_unique
    intro x _
    change x ∈ ((I i).support : Set X) ∪ (J.support : Set X)
    obtain ⟨j,hj,hxj⟩ := hcover x
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl hxj
    · apply Or.inr
      rw [hJsupport]
      exact (Finset.le_sup (f := fun j => (I j).support) hj) hxj

theorem isAmple_of_reduced_components {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (hcomponents : ∀ C : irreducibleComponents X,
      (L.pullback (CurveCycle.reducedComponentι X C)).IsAmple) : L.IsAmple := by
  classical
  let : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let I : irreducibleComponents X → X.IdealSheafData := fun C =>
    Scheme.IdealSheafData.vanishingIdeal
      (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)
  apply isAmple_of_finite_closed_cover Finset.univ p L H hH I
  · intro x
    have hx : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      trivial
    obtain ⟨C,hC,hxC⟩ := hx
    refine ⟨⟨C,hC⟩, Finset.mem_univ _, ?_⟩
    change x ∈ ((I ⟨C,hC⟩).support : Set X)
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change x ∈ C
    exact hxC
  · intro C _
    exact hcomponents C

end PiExponent.ReducedComponentAmple

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_IntegralComponentAmple
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_integral_closed_restrictions_q68_oai [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (hints : ∀ {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsClosedImmersion j],
      (L.pullback j).IsAmple) : L.IsAmple := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)
  have hI : I.support = ⊤ := by
    ext x
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let : IsNoetherian I.subscheme := {}
  let : IsReduced I.subscheme := isReduced_vanishingIdeal_subscheme ⊤
  apply LineBundle.isAmple_of_fullSupport p I hI L
  apply ReducedComponentAmple.isAmple_of_reduced_components (I.subschemeι ≫ p)
    (L.pullback I.subschemeι) (H.pullback I.subschemeι)
    (hH.pullback_closedImmersion H I.subschemeι)
  intro C
  let j := CurveCycle.reducedComponentι I.subscheme C
  have hc : (L.pullback (j ≫ I.subschemeι)).IsAmple := hints (j ≫ I.subschemeι)
  exact AmpleIso.isAmple_of_sheaf_iso _ _
    ((Scheme.Modules.pullbackComp j I.subschemeι).app L.sheaf).symm hc

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions_q68_oai := @OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions_q68_oai
