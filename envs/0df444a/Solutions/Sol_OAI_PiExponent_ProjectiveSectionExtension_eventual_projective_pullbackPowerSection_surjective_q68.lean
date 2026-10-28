-- Prove2me | solution 1 for OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:31:01.827149+00:00
-- url     : https://prove2.me/submissions/7386dd9e-0289-4a3c-8fce-c82bed3f1783

import Mathlib
import Definitions.Def_OAIQ068A044
import Definitions.Def_OAIQ068A045

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedRestrictionTensor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SerreDimensionShift
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerreDimensionShift

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_eq_zero_of_shortExact (A : C) {S : ShortComplex C} (hS : S.ShortExact)
    (q : ℕ) (hmid : ∀ x : Ext.{w} A S.X₂ q, x = 0)
    (hleft : ∀ x : Ext.{w} A S.X₁ (q + 1), x = 0)
    (x : Ext.{w} A S.X₃ q) : x = 0 := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ A hS x rfl (hleft _)
  rw [hmid y, Ext.zero_comp] at hy
  exact hy.symm

theorem eventual_ext_zero_of_presentations {ι : Type t} (A : C) (F : ι → ℕ → C)
    (l : ℕ)
    (hbound : ∀ i n q, l ≤ q → ∀ x : Ext.{w} A (F i n) q, x = 0)
    (presentation : ∀ i, AcyclicPresentation A F i)
    (q : ℕ) (hq : 0 < q) (i : ι) :
    ∃ N, ∀ n, N ≤ n → ∀ x : Ext.{w} A (F i n) q, x = 0 := by
  have hstep : ∀ r q, 0 < q → l ≤ q + r → ∀ i,
      ∃ N, ∀ n, N ≤ n → ∀ x : Ext.{w} A (F i n) q, x = 0 := by
    intro r
    induction r with
    | zero =>
      intro q hq hl i
      exact ⟨0, fun n _ x => hbound i n q (by simpa using hl) x⟩
    | succ r ih =>
      intro q hq hl i
      let P := presentation i
      obtain ⟨N, hN⟩ := ih (q + 1) (by omega) (by omega) P.kernel
      refine ⟨P.shift + N, fun n hn => ?_⟩
      have hnshift : P.shift ≤ n := by omega
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnshift
      apply ext_eq_zero_of_shortExact A (P.shortExact t) q
      · exact P.acyclic t q hq
      · exact hN t (by omega)
  exact hstep l q hq (by omega) i

theorem eventual_all_positive_ext_zero_of_presentations {ι : Type t}
    (A : C) (F : ι → ℕ → C) (l : ℕ)
    (hbound : ∀ i n q, l ≤ q → ∀ x : Ext.{w} A (F i n) q, x = 0)
    (presentation : ∀ i, AcyclicPresentation A F i) (i : ι) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q → ∀ x : Ext.{w} A (F i n) q, x = 0 := by
  classical
  have h : ∀ q : Fin l, ∃ N, ∀ n, N ≤ n →
      ∀ x : Ext.{w} A (F i n) (q.val + 1), x = 0 :=
    fun q => eventual_ext_zero_of_presentations A F l hbound presentation
      (q.val + 1) (by omega) i
  choose N hN using h
  refine ⟨Finset.univ.sup N, fun n hn q hq x => ?_⟩
  cases q with
  | zero => omega
  | succ q =>
    by_cases hl : l ≤ q + 1
    · exact hbound i n (q + 1) hl x
    · exact hN ⟨q, by omega⟩ n
        (le_trans (Finset.le_sup (f := N) (Finset.mem_univ _)) hn) x

end
end PiExponent.GeometrySupport.SerreDimensionShift

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SerreAssembly
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerreAssembly

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
open TwistPresentations

variable {X : Scheme.{0}} [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]

attribute [local instance] OAI.PiExponent.GeometrySupport.SerreAssembly.instHasExtModules_solutions
theorem eventual_twist_ext_zero_of_generation_and_standard_acyclicity
    (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (U : Fin l → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (hgenerate : ∀ M : {M : X.Modules // M.IsFinitePresentation},
      ∃ n0, ∃ s : ((moduleTwistFunctor L n0).obj M.val).GeneratingSections, s.IsFiniteType)
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X) (modulePow X L.sheaf n) q, x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X)
        ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  have hbound : ∀ i n q, l ≤ q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X) (coherentTwistFamily L i n) q,
        x = 0 := by
    intro i n q hq x
    let : i.val.IsFinitePresentation := i.property
    have := PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation L n i.val
    let : ((moduleTwistFunctor L n).obj i.val).IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
        ((moduleTwistFunctor L n).obj i.val)).choose.isQuasicoherent
    exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover l hl U hU hcover
      ((moduleTwistFunctor L n).obj i.val) q hq x
  choose n0 s hs using hgenerate
  let presentation (i : {M : X.Modules // M.IsFinitePresentation}) :
      SerreDimensionShift.AcyclicPresentation.{1} (schemeUnit X)
        (coherentTwistFamily L) i := by
    let : (s i).IsFiniteType := hs i
    exact acyclicPresentationOfGenerators.{1} L i (n0 i) (s i) hpow
  exact SerreDimensionShift.eventual_all_positive_ext_zero_of_presentations
    (schemeUnit X) (coherentTwistFamily L) l hbound presentation
      ⟨M, inferInstance⟩

theorem eventual_twist_ext_zero_of_section_cover
    (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X) (modulePow X L.sheaf n) q, x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X)
        ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  apply eventual_twist_ext_zero_of_generation_and_standard_acyclicity
    L l hl (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) haffine hcover
    _ hpow M
  intro A
  let : A.val.IsFinitePresentation := A.property
  obtain ⟨N, hN⟩ := PiExponent.AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    L A.val s hcover haffine
  obtain ⟨G, hG⟩ := hN N le_rfl
  exact ⟨N, G, hG⟩

end
end PiExponent.GeometrySupport.SerreAssembly

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveMonomialCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialCech

noncomputable section

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [AddCommGroup K]

theorem exists_nonnegative_coordinate [Nonempty ι] {d : ℤ}
    (hd : 0 ≤ d) (a : Monomial ι d) : ∃ i, 0 ≤ a.val i := by
  by_contra h
  have hneg : ∀ i, a.val i < 0 := fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩)
  have htotal : (∑ i, a.val i) < 0 :=
    Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty
  rw [a.property] at htotal
  exact (not_lt_of_ge hd) htotal

end
end PiExponent.ProjectiveMonomialCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveMonomialCechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialCechHigher

noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech

variable {ι A K : Type*} [AddCommGroup A]

variable [Fintype ι] [AddCommGroup K]

theorem contraction_regular {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c) :
    Regular (contraction pivot c) := by
  intro t a ha k hk
  obtain ⟨j, hj⟩ := hc (Fin.cons (pivot a) t) a ha k hk
  cases j using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero] at hj
      rw [← hj] at hk
      exact False.elim ((not_lt_of_ge (hpivot a)) hk)
  | succ j => exact ⟨j, by simpa only [Fin.cons_succ] using hj⟩

theorem exact_of_pivot {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hcocycle : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  refine ⟨contraction pivot c, contraction_regular pivot hpivot c hc, ?_⟩
  have h := contraction_identity pivot c
  rw [hcocycle] at h
  have hz : contraction pivot (0 : Cochain ι (Laurent ι K d) (q + 2)) = 0 := by
    funext t
    ext a
    rfl
  rw [hz, zero_add] at h
  exact h

theorem nonnegative_twist_cech_exact_all_positive {d : ℤ} (hd : 0 ≤ d) {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hcocycle : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      refine ⟨fun t => isEmptyElim (t 0), ?_, ?_⟩
      · intro t
        exact isEmptyElim (t 0)
      · funext t
        exact isEmptyElim (t 0)
  | inr h =>
      let pivot : Monomial ι d → ι :=
        fun a => Classical.choose (exists_nonnegative_coordinate hd a)
      have hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a) :=
        fun a => Classical.choose_spec (exists_nonnegative_coordinate hd a)
      exact exact_of_pivot pivot hpivot c hc hcocycle

end
end PiExponent.ProjectiveMonomialCechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open CechOne
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem map_sub {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c e : Cochain R U M q) :
    map R U M g (c - e) = map R U M g c - map R U M g e := by
  funext t
  exact Preadditive.sub_comp _ _ _

theorem primitives_of_shortExact (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) (q : ℕ)
    (hzero : ∀ (t : Fin (q + 2) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (hkernel : HasPrimitives R U S.X₁ (q + 1))
    (hmiddle : HasPrimitives R U S.X₂ q) : HasPrimitives R U S.X₃ q := by
  intro c hc
  obtain ⟨b, a, hb, ha, hclosed⟩ := connecting_cocycle R U S hS hzero c hc
  obtain ⟨e, he⟩ := hkernel a hclosed
  have hcorrected : differential R U S.X₂ (b - map R U S.X₁ S.f e) = 0 := by
    rw [differential_sub, ← map_differential, he, ha, sub_self]
  obtain ⟨v, hv⟩ := hmiddle _ hcorrected
  refine ⟨map R U S.X₂ S.g v, ?_⟩
  rw [← map_differential, hv, map_sub, hb]
  have hz : map R U S.X₂ S.g (map R U S.X₁ S.f e) = 0 := by
    funext t
    change (e t ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]
  rw [hz, sub_zero]

theorem shortExact_global_lift (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i)
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (hzero : ∀ (t : Fin 1 → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (hprimitive : HasPrimitives R U S.X₁ 0) (f : freeOpen R V ⟶ S.X₃) :
    ∃ g : freeOpen R V ⟶ S.X₂, g ≫ S.g = f := by
  let c := augmentation R U S.X₃ V hUV f
  obtain ⟨b, a, hb, ha, hclosed⟩ := connecting_cocycle R U S hS hzero c
    (augmentation_closed R U S.X₃ V hUV f)
  obtain ⟨e, he⟩ := hprimitive a hclosed
  have hcorrected : differential R U S.X₂ (b - map R U S.X₁ S.f e) = 0 := by
    rw [differential_sub, ← map_differential, he, ha, sub_self]
  obtain ⟨g, hg⟩ := glue_zero_cocycle R U S.X₂ V hUV hcover _ hcorrected
  refine ⟨g, ?_⟩
  apply hom_ext R U V hUV hcover S.X₃
  intro i
  rw [restrictHom_comp, hg i]
  change (restrictHom R _ (b (fun _ => i) - e (fun _ => i) ≫ S.f)) ≫ S.g = _
  erw [restrictHom_sub, Preadditive.sub_comp, ← restrictHom_comp,
    ← restrictHom_comp, Category.assoc, S.zero, comp_zero]
  simp only [restrictHom, comp_zero, sub_zero]
  have hi := congrFun hb (fun _ => i)
  change b (fun _ => i) ≫ S.g = c (fun _ => i) at hi
  rw [hi]
  exact sectionZero_augmentation R U S.X₃ V hUV f i

theorem ext_one_eq_zero (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i)
    (hzero : ∀ (t : Fin 1 → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) M 1), x = 0)
    (hprimitive : HasPrimitives R U M 0)
    (x : Ext.{u+1} (freeOpen R V) M 1) : x = 0 := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (freeOpen R V) hS x
    (Ext.eq_zero_of_injective _) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  obtain ⟨g, rfl⟩ := shortExact_global_lift R U V hUV hcover S hS hzero hprimitive f
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Ext.comp_zero] at hy
  exact hy.symm

theorem ext_succ_eq_zero_of_injective_cech
    (V : Opens X) (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (hinjective : ∀ (I : SheafOfModules.{u} R) [Injective I] (q : ℕ),
      HasPrimitives R U I q)
    (n : ℕ)
    (hlocal : ∀ (q : ℕ) (t : Fin (q + 1) → J) (k : ℕ)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) M (k + 1)), x = 0)
    (hprimitive : HasPrimitives R U M n)
    (x : Ext.{u+1} (freeOpen R V) M (n + 1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
      exact ext_one_eq_zero R U M V hUV hcover (fun t x => hlocal 0 t 0 x) hprimitive x
  | succ n ih =>
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have hlocal' : ∀ (q : ℕ) (t : Fin (q + 1) → J) (k : ℕ)
          (y : Ext.{u+1} (freeOpen R (intersection U t)) S.X₃ (k + 1)), y = 0 := by
        intro q t k y
        obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃
          (freeOpen R (intersection U t)) hS y (n₁ := k + 2) rfl (hlocal q t (k + 1) _)
        rw [Ext.eq_zero_of_injective z, Ext.zero_comp] at hz
        exact hz.symm
      have hprimitive' : HasPrimitives R U S.X₃ n :=
        primitives_of_shortExact R U S hS n
          (fun t y => hlocal (n + 1) t 0 y) hprimitive (hinjective S.X₂ n)
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (freeOpen R V) hS x
        (Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
      rw [ih S.X₃ hlocal' hprimitive' y, Ext.zero_comp] at hy
      exact hy.symm

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem affine_ext_succ_eq_zero_of_injective_cech
    (Y : Scheme.{u}) [IsNoetherian Y] (A : Y.Modules) [A.IsQuasicoherent]
    (W : J → Y.Opens) (V : Y.Opens) (hWV : ∀ i, W i ≤ V)
    (hcover : V ≤ ⨆ i, W i)
    (haffine : ∀ (q : ℕ) (t : Fin (q + 1) → J), IsAffineOpen (intersection W t))
    (hinjective : ∀ (I : Y.Modules) [Injective I] (q : ℕ),
      HasPrimitives Y.ringCatSheaf W I q)
    (n : ℕ) (hprimitive : HasPrimitives Y.ringCatSheaf W A n)
    (x : Ext.{u+1} (C := Y.Modules) (schemeFreeOpen Y V) A (n + 1)) : x = 0 := by
  exact ext_succ_eq_zero_of_injective_cech Y.ringCatSheaf W A V hWV hcover
    hinjective n (fun q t k y =>
      PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
        (intersection W t) (haffine q t) A k y) hprimitive x

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveTwistCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveTwistCech

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open PiExponent.ProjectiveMonomialCech

universe u
variable {X : Scheme.{u}} {ι K : Type u} [Fintype ι] [AddCommGroup K]

namespace LaurentCechPresentation

variable {U : ι → X.Opens} {M : X.Modules} {d : ℤ}
    (P : LaurentCechPresentation (K := K) U M d)

include P in

theorem hasPrimitives (hd : 0 ≤ d) (q : ℕ) :
    GeometrySupport.CechHigher.HasPrimitives X.ringCatSheaf U M q := by
  intro c hc
  have hregular : ProjectiveMonomialCechHigher.Regular (P.toLaurent c) :=
    fun t => P.regular _ t _
  have hclosed : ProjectiveMonomialCechHigher.differential (P.toLaurent c) = 0 := by
    rw [← P.toLaurent_differential, hc]
    funext t
    exact map_zero _
  obtain ⟨B, hB, hCB⟩ :=
    ProjectiveMonomialCechHigher.nonnegative_twist_cech_exact_all_positive hd
      (P.toLaurent c) hregular hclosed
  choose b hb using fun t => P.surjective q t (B t) (hB t)
  refine ⟨b, ?_⟩
  funext t
  apply P.injective (q + 1) t
  have hcochain : P.toLaurent b = B := funext hb
  have h := congrFun (P.toLaurent_differential b) t
  rw [hcochain, hCB] at h
  exact h

end LaurentCechPresentation

end
end PiExponent.ProjectiveTwistCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveTwistAcyclicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveTwistAcyclicity

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport.CechOne
open PiExponent.ProjectiveMonomialCech

universe u
variable {X : Scheme.{u}} {ι K : Type u} [Fintype ι] [AddCommGroup K]

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem ext_succ_eq_zero_of_laurent_cech_charts [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (d : ℤ) (hd : 0 ≤ d)
    (P : ProjectiveTwistCech.LaurentCechPresentation (K := K) U M d)
    (q : ℕ) (x : Ext.{u+1} (C := X.Modules) (schemeUnit (X := X)) M (q + 1)) : x = 0 := by
  let e : schemeFreeOpen (X := X) ⊤ ≅ schemeUnit (X := X) :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen ⊤) M (q + 1), z = 0 := by
    apply GeometrySupport.CechHigher.affine_ext_succ_eq_zero_of_injective_cech
      X M U ⊤ (fun _ => le_top) (by rw [hcover])
    · intro n t
      exact IsAffineOpen.iInf (fun i => hU (t i))
    · intro I hI n
      exact @GeometrySupport.FreeCechSections.injective_hasPrimitives _ _ U X.ringCatSheaf I hI n
    · exact P.hasPrimitives hd q
  have h := congrArg (fun y => (Ext.mk₀ e.inv).comp y (zero_add (q + 1)))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add (q + 1))))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

end
end PiExponent.ProjectiveTwistAcyclicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveCoordinateAcyclicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (structureSheaf X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,PiExponentSeshadri.SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
attribute [local irreducible] coordinatePowerOverlap modulePow

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

include hc in
omit [Fintype σ] in

theorem coordinatePower_isQuasicoherent (n : ℕ) :
    (modulePow X M n).IsQuasicoherent :=
  LineBundleCoherent.modulePow_isQuasicoherent (coordinateLineBundle M s hc) n

include hf in

theorem coordinatePower_ext_succ_eq_zero [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n q : ℕ)
    (x : Ext.{1} (C := X.Modules) (schemeUnit (X := X)) (modulePow X M n) (q + 1)) : x = 0 := by
  let : (modulePow X M n).IsQuasicoherent := coordinatePower_isQuasicoherent M s hc n
  exact ProjectiveTwistAcyclicity.ext_succ_eq_zero_of_laurent_cech_charts
    (coordinateOpen_isAffine M s k hc f hf) hc (modulePow X M n) n (Int.natCast_nonneg n)
    (coordinateLaurentCechPresentation M s k hc f hf n) q x

include hf in
theorem coordinatePower_ext_eq_zero [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n q : ℕ) (hq : 0 < q)
    (x : Ext.{1} (C := X.Modules) (schemeUnit (X := X)) (modulePow X M n) q) : x = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  exact coordinatePower_ext_succ_eq_zero M s k hc f hf n r x

end
end PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSpaceSerre
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

attribute [local irreducible] lineBundle coordinateSection scalars

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

variable (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ]

theorem standardPower_ext_eq_zero (n q : ℕ) (hq : 0 < q)
    (x : Ext.{1} (C := (projectiveSpace R σ).Modules) (schemeUnit (projectiveSpace R σ))
      (modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n) q) :
    x = 0 := by
  exact PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinatePower_ext_eq_zero
    (X := projectiveSpace R σ) (K := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf
    (coordinateSection (R := R) (σ := σ)) (scalars (R := R) (σ := σ))
    (coordinateSection_cover (R := R) (σ := σ)) (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n q hq x

theorem serre_vanishing [Nonempty σ]
    (M : (projectiveSpace R σ).Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := (projectiveSpace R σ).Modules) (schemeUnit (projectiveSpace R σ))
        ((moduleTwistFunctor (lineBundle (R := R) (σ := σ)) n).obj M) q, x = 0 := by
  let e := Fintype.equivFin σ
  let s : Fin (Fintype.card σ) →
      (structureSheaf (projectiveSpace R σ) ⟶ (lineBundle (R := R) (σ := σ)).sheaf) :=
    fun i => coordinateSection (e.symm i)
  have hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤ := by
    change (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen
      (coordinateSection (R := R) (e.symm i))) = ⊤
    exact (Equiv.iSup_comp
      (g := fun j : σ => PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) j))
      e.symm).trans (coordinateSection_cover (R := R) (σ := σ))
  apply PiExponent.GeometrySupport.SerreAssembly.eventual_twist_ext_zero_of_section_cover
    (lineBundle (R := R) (σ := σ)) (Fintype.card σ) Fintype.card_pos s hcover
    (fun i => coordinateSection_isAffineOpen (e.symm i)) _ M
  intro n q hq x
  exact standardPower_ext_eq_zero R σ n q hq x

end
end PiExponent.ProjectiveO1

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SerreSectionLifting
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerreSectionLifting
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem globalSections_surjective_of_h1_zero
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hzero : ∀ x : cohomology S.X₁ 1, x = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  intro s
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS
    (Ext.mk₀ s) (n₁ := 1) rfl (hzero _)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

end
end PiExponent.GeometrySupport.SerreSectionLifting

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionExtension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveSectionExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
open GeometrySupport

variable {X Y : Scheme.{0}}

lemma idealModule_isFinitePresentation [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f] :
    (PiExponentSeshadri.IdealModule.idealModule f).IsFinitePresentation := by
  let : (PiExponentSeshadri.IdealModule.unit X).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (PiExponentSeshadri.IdealModule.unit Y).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward f).obj
      (PiExponentSeshadri.IdealModule.unit X)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj
        (PiExponentSeshadri.IdealModule.unit X))).choose.isQuasicoherent
  exact FiniteGlobalPresentation.kernel_isFinitePresentation
    (PiExponentSeshadri.IdealModule.structureMap f)

theorem quotientPowerRestriction_surjective_of_h1_zero
    (L : LineBundle Y) (f : X ⟶ Y) [IsClosedImmersion f] (n : ℕ)
    (hzero : ∀ x : cohomology
      ((moduleTwistFunctor L n).obj (PiExponentSeshadri.IdealModule.idealModule f)) 1, x = 0) :
    Function.Surjective (quotientPowerRestriction L f n) := by
  let S := ShortComplex.mk (PiExponentSeshadri.IdealModule.inclusion f)
    (PiExponentSeshadri.IdealModule.structureMap f) (kernel.condition _)
  have hS : S.ShortExact := PiExponentSeshadri.IdealModule.closedSequence_exact f
  have hsurj := SerreSectionLifting.globalSections_surjective_of_h1_zero
    (S.map (moduleTwistFunctor L n)) (moduleTwistFunctor_shortExact L n S hS) hzero
  intro s
  obtain ⟨t, ht⟩ := hsurj s
  refine ⟨t ≫ (moduleTwistUnitIso L n).hom, ?_⟩
  change t ≫ (moduleTwistFunctor L n).map
    (PiExponentSeshadri.IdealModule.structureMap f) = s at ht
  change (t ≫ (moduleTwistUnitIso L n).hom) ≫ (moduleTwistUnitIso L n).inv ≫ _ = s
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ht

theorem eventual_projective_quotientPowerRestriction_surjective
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (quotientPowerRestriction (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n) := by
  let := idealModule_isFinitePresentation f
  obtain ⟨N, hN⟩ := ProjectiveO1.serre_vanishing R σ
    (PiExponentSeshadri.IdealModule.idealModule f)
  exact ⟨N, fun n hn => quotientPowerRestriction_surjective_of_h1_zero
    (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n (hN n hn 1 (by decide))⟩

end
end PiExponent.ProjectiveSectionExtension

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionPullback
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveSectionExtension
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X Y : Scheme.{0}}

theorem quotientSectionsEquiv_restriction (L : LineBundle Y) (f : X ⟶ Y)
    (n : ℕ) (s : GlobalSections Y (modulePow Y L.sheaf n)) :
    quotientSectionsEquiv L f n (quotientPowerRestriction L f n s) =
      pullbackPowerSection L f n s := by
  apply (globalPushEquiv f _).injective
  change globalPushEquiv f _ ((globalPushEquiv f _).symm
    (quotientPowerRestriction L f n s ≫ (quotientPowerIso L f n).hom)) = _
  rw [Equiv.apply_symm_apply]
  change (s ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)) ≫
      (ProjectionFormula.twistIso f (structureSheaf X) L n).inv ≫
        (Scheme.Modules.pushforward f).map (moduleTwistUnitIso (L.pullback f) n).hom = _
  change _ = PiExponentSeshadri.IdealModule.structureMap f ≫
    (Scheme.Modules.pushforward f).map (pullbackPowerSection L f n s)
  erw [Category.assoc, Category.assoc]
  simpa only [PiExponentSeshadri.Frames.O, structureSheaf,
    PiExponentSeshadri.IdealModule.unit] using! ClosedRestrictionTensor.section_restriction_eq f L n s

theorem eventual_projective_pullbackPowerSection_surjective_q68_oai
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (pullbackPowerSection (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n) := by
  obtain ⟨N, hN⟩ := eventual_projective_quotientPowerRestriction_surjective f
  refine ⟨N, fun n hn t => ?_⟩
  obtain ⟨s, hs⟩ := hN n hn ((quotientSectionsEquiv _ f n).symm t)
  refine ⟨s, ?_⟩
  rw [← quotientSectionsEquiv_restriction, hs, Equiv.apply_symm_apply]

end PiExponent.ProjectiveSectionExtension
end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective_q68_oai := @OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective_q68_oai
