-- Prove2me | solution 1 for OAI.LittleFinitistic.extreme_left_right_asymmetry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:44:50.864815+00:00
-- url     : https://prove2.me/submissions/a94a686c-a9c7-4def-b139-c1931e68b47b

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Idempotents.Biproducts
import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.CategoryTheory.Localization.Preadditive
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_FinitisticAsymmetry
import Definitions.Def_Q221FA002
import Theorems.Thm_OAI_LittleFinitistic_CummingsConstruction_injectivesGenerate
import Theorems.Thm_OAI_LittleFinitistic_Main_infinite_littleFinitisticDimension

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_LocalizingRetracts
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.DerivedSupport
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasColimitsOfShape (Discrete ℕ) C]
variable {X Y : C} (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X)

include hip

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ degree : ℤ, (shiftFunctor C degree).Additive] [Pretriangulated C]

lemma swindle_distinguished : Triangle.mk (swindleA i p) (swindleB p) 0 ∈ distTriang C := by
  apply isomorphic_distinguished _ (binaryBiproductTriangle_distinguished (∐ fun _ : ℕ => Y) X)
  refine Triangle.isoMk _ _ (Iso.refl _) (swindleIso i p hip) (Iso.refl _) ?_ ?_ ?_
  · simp only [Triangle.mk, Iso.refl_hom, binaryBiproductTriangle, Category.id_comp]
    change swindleA i p ≫ (swindleIso i p hip).hom = biprod.inl
    apply biprod.hom_ext <;> simp [swindleIso, swindleAC i p hip, swindleAB i p hip]
  · simp only [Triangle.mk, Iso.refl_hom, binaryBiproductTriangle, Category.comp_id]
    change swindleB p = (swindleIso i p hip).hom ≫ biprod.snd
    exact (biprod.lift_snd _ _).symm
  · simp
    exact (zero_comp (X := _) (f := (shiftFunctor C 1).map _)).trans (comp_zero (f := 𝟙 _)).symm

lemma localizing_of_retract (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulated] [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] (hY : P Y) : P X := by
  have h : P (∐ fun _ : ℕ => Y) := P.prop_colimit (Discrete.functor (fun _ : ℕ => Y)) (fun _ => hY)
  exact P.ext_of_isTriangulatedClosed₃ _ (swindle_distinguished i p hip) h h

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_ModuleGeneration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u w
variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
  [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]

omit [P.IsTriangulated] [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_single_of_cofan {I : Type u} [P.IsClosedUnderColimitsOfShape (Discrete I)]
    {M : I → ModuleCat R} (s : Cofan M) (hs : IsColimit s)
    (hM : ∀ i, P ((DerivedCategory.singleFunctor _ 0).obj (M i))) :
    P ((DerivedCategory.singleFunctor _ 0).obj s.pt) := by
  let F := HomologicalComplex.single (ModuleCat R) (.up ℤ) 0
  let e := DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0
  have hs' := isColimitCofanMkObjOfIsColimit F M s.inj hs
  apply P.prop_of_iso (e.app s.pt).symm
  exact P.prop_of_isColimit (derivedCofanIsColimit _ hs')
    (fun i => P.prop_of_iso (e.app (M i.as)) (hM i.as))

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Nakayama_Modules
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Nakayama
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

variable {k R}

variable (k R)

lemma field_injective (V : ModuleCat.{u} k) : Injective V where
  factors {X Y} g f hf := by
    obtain ⟨s, hs⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp hf))
    refine ⟨ModuleCat.ofHom (g.hom.comp s), ?_⟩
    apply ModuleCat.hom_ext
    change g.hom.comp (s.comp f.hom) = g.hom
    rw [hs, LinearMap.comp_id]

instance coind_injective (V : ModuleCat.{u} k) : Injective (coind k R V) :=
  (ModuleCat.restrictCoextendScalarsAdj (algebraMap k R)).map_injective _
    (field_injective k V)

lemma eta_natural {M N : ModuleCat.{u} R} (f : M ⟶ N) (p : M) :
    (map f).comp (etaMap k R M p) = etaMap k R N (f p) := by rfl

lemma frame_nonempty (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    Nonempty (Frame R M) := by
  classical
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  refine ⟨⟨n, fun i => f (Pi.single i 1), fun i => (LinearMap.proj i).comp g, ?_⟩⟩
  intro x
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, ← map_smul, ← map_sum]
  have he : ∑ i : Fin n, g x i • Pi.single i (1 : R) = g x := by
    ext j
    simp [Pi.single_apply, smul_eq_mul]
  rw [he]
  exact LinearMap.congr_fun hfg x

variable {k R}
lemma Frame.dual_expand {M : ModuleCat.{u} R} (F : Frame R M) (φ : M →ₗ[R] R) :
    ∑ i, rightMult k R M (φ (F.b i)) (F.c i) = φ := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.sum_apply, rightMult_apply, map_sum, map_smul,
    smul_eq_mul] using congrArg φ (F.expand x)

variable (k R)
lemma eta_injective [FiniteDimensional k R] (M : ModuleCat.{u} R)
    (F : Frame R M) : Function.Injective (etaMap k R M) := by
  intro x y h
  have hxy (i : Fin F.n) : F.c i x = F.c i y := by
    apply (Module.evalEquiv k R).injective
    apply LinearMap.ext
    intro φ
    exact congrArg (fun f : DA k R →ₗ[R] Object k R M =>
      Object.value (f ((daEquiv k R).symm φ)) (F.c i)) h
  rw [← F.expand x, ← F.expand y]
  simp only [hxy]

lemma eta_surjective [FiniteDimensional k R] (M : ModuleCat.{u} R)
    (F : Frame R M) : Function.Surjective (etaMap k R M) := by
  classical
  intro f
  let p : Fin F.n → R := fun i => (Module.evalEquiv k R).symm (
    (LinearMap.applyₗ' k (F.c i)).comp
      ((f.restrictScalars k).comp (daEquiv k R).symm.toLinearMap))
  have hp (i : Fin F.n) (h : DA k R) : h (p i) = Object.value (f h) (F.c i) := by
    change (daEquiv k R h) (p i) = _
    dsimp only [p]
    rw [Module.apply_evalEquiv_symm_apply]
    change Object.value (f ((daEquiv k R).symm (daEquiv k R h))) (F.c i) = _
    rw [LinearEquiv.symm_apply_apply]

  refine ⟨∑ i, p i • F.b i, ?_⟩
  apply LinearMap.ext
  intro h
  apply Object.ext
  intro φ
  change h (φ (∑ i, p i • F.b i)) = Object.value (f h) φ
  calc
    h (φ (∑ i, p i • F.b i)) = ∑ i, h (p i * φ (F.b i)) := by
      change (daEquiv k R h) (φ (∑ i, p i • F.b i)) = _
      simp only [map_sum, map_smul, smul_eq_mul]
      rfl
    _ = ∑ i, Object.value (f h) (rightMult k R M (φ (F.b i)) (F.c i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show h (p i * φ (F.b i)) =
        (φ (F.b i) • h : DA k R) (p i) from rfl, hp]
      rw [map_smul]
      rfl
    _ = Object.value (f h) φ := by rw [← map_sum, F.dual_expand]

lemma coindInclusion_retraction (M : ModuleCat.{u} R) (F : Frame R M) :
    coindInclusion k R M ≫ coindRetraction k R M F = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  apply Object.ext
  intro φ
  change ∑ i, Object.value h (rightMult k R M (φ (F.b i)) (F.c i)) = Object.value h φ
  rw [← map_sum, F.dual_expand]

lemma object_injective (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    Injective ((functor k R).obj M) := by
  obtain ⟨F⟩ := frame_nonempty R M
  exact (show Retract ((functor k R).obj M) (coind k R (ModuleCat.of k (Object k R M))) from
    ⟨coindInclusion k R M, coindRetraction k R M F, coindInclusion_retraction k R M F⟩).injective

end LittleFinitistic.Nakayama

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_InjectiveSums
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u v
variable {R : Type u} [Ring R] {ι : Type v}
variable (Q : ι → Type u) [∀ i, AddCommGroup (Q i)] [∀ i, Module R (Q i)]

lemma finite_support_map (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (g : M →ₗ[R] Π₀ i, Q i) : ∃ s : Finset ι, ∀ x i, i ∉ s → g x i = 0 := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let s := Finset.univ.biUnion (fun j : Fin n => (g (f (Pi.single j 1))).support)
  refine ⟨s, ?_⟩
  intro x i hi
  obtain ⟨v, rfl⟩ := hf x
  have hv : ∑ j : Fin n, v j • Pi.single j (1 : R) = v := by
    ext j
    simp [Pi.single_apply, smul_eq_mul]
  have hz (j : Fin n) : (g (f (Pi.single j 1))) i = 0 := by
    apply DFinsupp.notMem_support_iff.mp
    intro h
    apply hi
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩
  rw [← hv, map_sum, map_sum]
  change (DFinsupp.lapply (R := R) i) (∑ j, g (f (v j • Pi.single j 1))) = 0
  rw [map_sum]
  simp only [map_smul, DFinsupp.lapply_apply, hz, smul_zero, Finset.sum_const_zero]

lemma dfinsupp_injective [IsNoetherianRing R] [∀ i, Module.Injective R (Q i)] :
    Module.Injective R (Π₀ i, Q i) := by
  classical
  apply Module.Baer.injective
  intro I g
  obtain ⟨s, hs⟩ := finite_support_map Q I g
  have he (i : ι) : ∃ f : R →ₗ[R] Q i, ∀ (x : R) (hx : x ∈ I),
      f x = g ⟨x,hx⟩ i :=
    Module.Baer.of_injective (inferInstance : Module.Injective R (Q i)) I
      ((DFinsupp.lapply i).comp g)
  choose f hf using he
  refine ⟨∑ i ∈ s, (DFinsupp.lsingle i).comp (f i), ?_⟩
  intro x hx
  apply DFinsupp.ext
  intro j
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, DFinsupp.lsingle_apply]
  by_cases hj : j ∈ s
  · simpa [DFinsupp.single_apply, hj] using hf j x hx
  · simp [DFinsupp.single_apply, hj, hs _ _ hj]

lemma prod_injective (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Injective R M] [Module.Injective R N] :
    Module.Injective R (M × N) := by
  constructor
  intro X Y _ _ _ _ f hf g
  obtain ⟨a, ha⟩ := Module.Injective.out f hf ((LinearMap.fst R M N).comp g)
  obtain ⟨b, hb⟩ := Module.Injective.out f hf ((LinearMap.snd R M N).comp g)
  exact ⟨a.prod b, fun x => Prod.ext (ha x) (hb x)⟩

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Nakayama_Coinduction
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Module
namespace LittleFinitistic.Nakayama
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

lemma da_finite : Module.Finite R (DA k R) := by
  let : Module.Finite k (DA k R) := Module.Finite.equiv (daEquiv k R).symm
  exact Module.Finite.of_restrictScalars_finite k R _

variable {k R}

omit [FiniteDimensional k R] in
private lemma coind_sum_eval {J : Type*} (s : Finset J) (V : ModuleCat.{u} k)
    (f : J → coind k R V) (r : R) :
    (∑ j ∈ s, f j) r = ∑ j ∈ s, f j r := by
  change (ModuleCat.CoextendScalars.equiv (algebraMap k R) V (∑ j ∈ s, f j)) r = _
  rw [map_sum]
  exact LinearMap.sum_apply _ _ _

variable {ι : Type u}

omit [FiniteDimensional k R] in
lemma coindBasisMap_injective (V : ModuleCat.{u} k) (b : Basis ι k V) :
    Function.Injective (coindBasisMap (R := R) V b) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro φ hφ
  change φ = 0
  apply DFinsupp.ext
  intro i
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro r
  change R at r
  change φ i r = 0
  have h := congrArg (fun g : coind k R V => b.repr (g r) i) hφ
  rw [coind_zero_eval, map_zero, Finsupp.zero_apply] at h
  change coindBasisMap V b φ = 0 at hφ
  have he : coindBasisMap V b φ r = ∑ j ∈ φ.support, φ j r • b j := by
    have hexp : coindBasisMap V b φ = ∑ j ∈ φ.support, coindLine V (b j) (φ j) := by
      simp [coindBasisMap, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum]
    rw [hexp, coind_sum_eval]
    simp only [coindLine_apply]
  rw [he] at h
  simp only [map_sum, map_smul, b.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  by_cases hi : i ∈ φ.support
  · simpa [hi] using h
  · have hh := DFinsupp.notMem_support_iff.mp hi
    rw [hh]
    rfl

lemma coindBasisMap_surjective
    (V : ModuleCat.{u} k) (b : Basis ι k V) :
    Function.Surjective (coindBasisMap (R := R) V b) := by
  classical
  intro φ
  let φ' : R →ₗ[k] V := {
    toFun := φ
    map_add' := φ.map_add
    map_smul' := coind_smul_eval k R V φ }
  let g : R →ₗ[k] Π₀ _ : ι, k := (finsuppLequivDFinsupp k).toLinearMap.comp
    (b.repr.toLinearMap.comp φ')
  obtain ⟨s, hs⟩ := Rickard.finite_support_map (R := k) (fun _ : ι => k) R g
  let c (i : ι) : DA k R := (daEquiv k R).symm ((Finsupp.lapply i).comp
    (b.repr.toLinearMap.comp φ'))
  let x : Π₀ _ : ι, DA k R := ∑ i ∈ s, DFinsupp.single i (c i)
  refine ⟨x, ?_⟩
  apply LinearMap.ext
  intro r
  change R at r
  change coindBasisMap V b x r = φ r
  have he : coindBasisMap V b x r = ∑ i ∈ s, b.repr (φ r) i • b i := by
    have hx : coindBasisMap V b x = ∑ i ∈ s, coindLine V (b i) (c i) := by
      simp only [x, map_sum, coindBasisMap, DFinsupp.lsum_single]
    rw [hx, coind_sum_eval]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  rw [he]
  apply b.repr.injective
  ext i
  by_cases hi : i ∈ s
  · simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hi]
  · have hh := hs r i hi
    change b.repr (φ r) i = 0 at hh
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hi, hh]

variable (k R)
lemma coindBasisMap_bijective (V : ModuleCat.{u} k) (b : Basis ι k V) :
    Function.Bijective (coindBasisMap (R := R) V b) :=
  ⟨coindBasisMap_injective V b, coindBasisMap_surjective V b⟩

omit [FiniteDimensional k R] in
lemma moduleCoindInclusion_mono (M : ModuleCat.{u} R) : Mono (moduleCoindInclusion k R M) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y h
  have hh := congrArg (fun g : coind k R ((ModuleCat.restrictScalars (algebraMap k R)).obj M) => g (1 : R)) h
  change (1 : R) • x = (1 : R) • y at hh
  simpa using hh

end LittleFinitistic.Nakayama

end

end OAI
end

section
-- module Solutions.Q221_FA.Finitistic_Dimension_PDDimension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

lemma cover_subsingleton (M : FiniteModule k A) [Subsingleton M] :
    Subsingleton (cover M).source := by
  have hp : (cover M).π = 0 := Subsingleton.elim _ _
  have hsurj := (cover M).minimal 0 (by simp [hp])
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hsurj x
  obtain ⟨b, hb⟩ := hsurj y
  exact ha.symm.trans hb

lemma cover_injective (M : FiniteModule k A) [Module.Projective A M] :
    Function.Injective (cover M).π := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (cover M).π LinearMap.id
    (cover M).surjective
  have he : (cover M).π.comp (g.comp (cover M).π) = (cover M).π := by
    rw [← LinearMap.comp_assoc, hg, LinearMap.id_comp]
  have hs := (cover M).minimal _ he
  have hgs : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨(cover M).π y, hy⟩
  have hgp : g.comp (cover M).π = LinearMap.id := by
    ext x
    obtain ⟨y, rfl⟩ := hgs x
    exact congrArg g (DFunLike.congr_fun hg y)
  exact LinearMap.injective_of_comp_eq_id _ _ hgp

lemma next_subsingleton_of_projective (M : FiniteModule k A) [Module.Projective A M] :
    Subsingleton (next M) := by
  have he := LinearMap.ker_eq_bot.mpr (cover_injective M)
  change Subsingleton (LinearMap.ker (cover M).π)
  rw [he]
  infer_instance

/-- Vanishing of a term of the constructed resolution gives the standard
categorical projective-dimension bound. -/
theorem pdLT_of_term_zero (M : FiniteModule k A) (n i : ℕ)
    (hz : Subsingleton (term M (i+n))) :
    HasProjectiveDimensionLT (syzygy M i).cat n := by
  induction n generalizing i with
  | zero =>
    have : Subsingleton (term M i) := by simpa using hz
    have : Subsingleton (syzygy M i) :=
      Function.Surjective.subsingleton (cover _).surjective
    exact (hasProjectiveDimensionLT_zero_iff_isZero _).mpr
      (ModuleCat.isZero_iff_subsingleton.mpr (show Subsingleton (syzygy M i) from inferInstance))
  | succ n ih =>
    have hnext : HasProjectiveDimensionLT (syzygy M (i+1)).cat n :=
      ih (i+1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz)
    have hs := LinearMap.shortExact_shortComplexKer (cover (syzygy M i)).surjective
    exact hs.hasProjectiveDimensionLT_X₃ n hnext inferInstance

lemma syzygy_projective (M : FiniteModule k A) (n i : ℕ)
    (h : HasProjectiveDimensionLT (syzygy M i).cat (n+1)) :
    Projective (syzygy M (i+n)).cat := by
  induction n generalizing i with
  | zero =>
    simpa using projective_iff_hasProjectiveDimensionLT_one.mpr h
  | succ n ih =>
    have hs := LinearMap.shortExact_shortComplexKer (cover (syzygy M i)).surjective
    have hn : HasProjectiveDimensionLT (syzygy M (i+1)).cat (n+1) :=
      (hs.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i+1) hn

/-- Finite projective dimension forces the minimal resolution to terminate. -/
theorem term_zero_of_pdLE (M : FiniteModule k A) (n : ℕ)
    (h : HasProjectiveDimensionLE M.cat n) : Subsingleton (term M (n+1)) := by
  have hp := syzygy_projective M n 0 h
  rw [Nat.zero_add] at hp
  have : Module.Projective A (syzygy M n) :=
    (IsProjective.iff_projective _).mpr (by simpa only [Nat.zero_add, FiniteModule.cat] using hp)
  have : Subsingleton (syzygy M (n+1)) := next_subsingleton_of_projective (syzygy M n)
  exact cover_subsingleton _

/-- The actual minimal-resolution term criterion, proved from covers and
short-exact-sequence dimension shifting. -/
theorem pdLE_iff_term_zero (M : FiniteModule k A) (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔ Subsingleton (term M (n+1)) :=
  ⟨term_zero_of_pdLE M n, fun h => pdLT_of_term_zero M (n+1) 0 (by simpa using h)⟩
end LittleFinitistic.PDMinimal

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_FiniteFamilies
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

lemma exists_finite_module_high_pd (h : littleFinitisticDimension R = ⊤) (i : ℕ) :
    ∃ M : PDMinimal.FiniteModule k R,
      (i : WithBot ℕ∞) < projectiveDimension M.cat ∧ projectiveDimension M.cat < ⊤ := by
  have hi : (i : WithBot ℕ∞) < littleFinitisticDimension R := by
    rw [h]
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top i)
  simp only [littleFinitisticDimension, lt_iSup_iff] at hi
  obtain ⟨M, hfg, hpd, hgt⟩ := hi
  let := hfg
  let : Module k M := Module.compHom M (algebraMap k R)
  let : IsScalarTower k R M := IsScalarTower.of_compHom k R M
  let : FiniteDimensional k M := Module.Finite.trans R M
  exact ⟨PDMinimal.FiniteModule.of (k := k) (A := R) M, hgt, hpd⟩

lemma exists_minimal_family (h : littleFinitisticDimension R = ⊤) :
    ∃ (M : ℕ → PDMinimal.FiniteModule k R) (d : ℕ → ℕ),
      (∀ i, i < d i) ∧
      (∀ i, HasProjectiveDimensionLE (M i).cat (d i)) ∧
      (∀ i, ¬ Subsingleton (PDMinimal.term (M i) (d i))) := by
  classical
  choose M hgt hfin using exists_finite_module_high_pd (k := k) h
  have hb (i : ℕ) : ∃ d, HasProjectiveDimensionLE (M i).cat d :=
    (projectiveDimension_ne_top_iff _).mp (hfin i).ne
  let d := fun i => Nat.find (hb i)
  have hd (i : ℕ) : HasProjectiveDimensionLE (M i).cat (d i) := Nat.find_spec (hb i)
  have hdi (i : ℕ) : i < d i := by
    have hp := (projectiveDimension_le_iff _ _).mpr (hd i)
    have hlt := (hgt i).trans_le hp
    exact_mod_cast hlt
  refine ⟨M, d, hdi, hd, ?_⟩
  intro i hz
  have hpos := hdi i
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d i ≠ 0)
  have hh : HasProjectiveDimensionLE (M i).cat n :=
    (PDMinimal.pdLE_iff_term_zero (M i) n).mpr (by simpa [hn] using hz)
  have hm := Nat.find_min' (hb i) hh
  change d i ≤ n at hm
  omega

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_Orthogonal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.Rickard
universe u v t
variable {C : Type u} [Category.{v} C]

lemma leftOrthogonal_closed [HasZeroMorphisms C] (P : ObjectProperty C) (J : Type t) [Category J] :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩ Y f hY
  apply colimit.hom_ext
  intro j
  simpa using hF j (colimit.ι F j ≫ f) hY

section
variable [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

instance perpendicular_closed (X : C) (J : Type t) [Category J] :
    (perpendicular X).IsClosedUnderColimitsOfShape J := leftOrthogonal_closed _ J

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma perpendicular_iff (X Y : C) : perpendicular X Y ↔
    ∀ (n : ℤ) (f : Y ⟶ X⟦n⟧), f = 0 := by
  constructor
  · intro h n f
    exact h f ⟨X,n,Iso.refl _, by simp⟩
  · intro h Z f hZ
    obtain ⟨X', n, e, he⟩ := hZ
    have he' : X = X' := by simpa using he
    subst X'
    apply (cancel_mono e.hom).mp
    simpa using h n (f ≫ e.hom)

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma isZero_of_perpendicular_self (X : C) (hX : perpendicular X X) : IsZero X := by
  apply (IsZero.iff_id_eq_zero _).mpr
  exact hX (𝟙 X) ((ObjectProperty.singleton X).le_shiftClosure X (by simp))
end

variable {R : Type u} [Ring R]

local instance orthogonalHasDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

lemma not_generate_of_orthogonal
    (X : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _))
    (hX : ¬ IsZero X)
    (hI : ∀ (M : ModuleCat.{u} R), Injective M →
      ∀ (n : ℤ) (f : (DerivedCategory.singleFunctor _ 0).obj M ⟶ X⟦n⟧), f = 0) :
    ¬ InjectivesGenerate R := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  intro h
  apply hX
  apply isZero_of_perpendicular_self
  apply h (perpendicular X) inferInstance inferInstance (fun I => inferInstance)
  intro M hM
  exact (perpendicular_iff X _).mpr (hI M hM)

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_OrthogonalStalks
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
namespace LittleFinitistic.Rickard
universe u
variable {R : Type u} [Ring R]

lemma class_eq_zero_of_hom_exact (D : ModuleCat.{u} R)
    (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hex : ∀ j, ∀ f : D ⟶ L.X j, f ≫ L.d j (j+1) = 0 →
      ∃ g : D ⟶ L.X (j-1), g ≫ L.d (j-1) j = f)
    (n : ℤ) (x : CohomologyClass ((singleFunctor _ 0).obj D) L n) : x=0 := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (by simp) (n+1) rfl
  rw [CohomologyClass.mk_eq_zero_iff,
    Cocycle.fromSingleMk_mem_coboundaries_iff f (by simp) (n+1) rfl hf (n-1) (by omega)]
  exact hex n f hf

attribute [local instance] OAI.LittleFinitistic.Rickard.orthogonalStalksHasDerivedCategory
lemma orthogonal_single_of_hom_exact (D : ModuleCat.{u} R)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) [L.IsKInjective]
    (hex : ∀ j, ∀ f : D ⟶ L.X j, f ≫ L.d j (j+1) = 0 →
      ∃ g : D ⟶ L.X (j-1), g ≫ L.d (j-1) j = f)
    (n : ℤ) (f : (DerivedCategory.singleFunctor _ 0).obj D ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :
    f=0 := by
  let S := (singleFunctor (ModuleCat R) 0).obj D
  have hz (g : (HomotopyCategory.quotient _ _).obj S ⟶
      (HomotopyCategory.quotient _ _).obj (L⟦n⟧)) : g=0 := by
    obtain ⟨x, rfl⟩ := (CohomologyClass.toHom_bijective S L n).surjective g
    rw [class_eq_zero_of_hom_exact D L hex n x, map_zero]
  have hz' (g : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj S) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (L⟦n⟧))) : g=0 := by
    obtain ⟨g, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient _ _).obj S) (L⟦n⟧)).surjective g
    rw [hz g, Functor.map_zero]
  let es := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0).app D
  let eqs := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app S
  let eql := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app (L⟦n⟧)
  let en := (DerivedCategory.Q.commShiftIso n).app L
  apply (cancel_epi es.inv).mp
  apply (cancel_epi eqs.hom).mp
  apply (cancel_mono en.inv).mp
  apply (cancel_mono eql.inv).mp
  simpa only [Category.assoc, comp_zero, zero_comp] using
    hz' (eqs.hom ≫ es.inv ≫ f ≫ en.inv ≫ eql.inv)

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_ReducedProducts
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u
variable {R : Type u} [Ring R]
variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

lemma reducedComplex_injective [IsNoetherianRing R]
    (hK : ∀ i j, Injective ((K i).X j)) (j : ℤ) :
    Injective ((reducedComplex K).X j) := by
  let (i : ℕ) : Module.Injective R ((K i).X j) :=
    (Module.injective_iff_injective_object R _).mpr (hK i j)
  let (i : ℕ) : Module.Injective R ((K i).X (j+1)) :=
    (Module.injective_iff_injective_object R _).mpr (hK i (j+1))
  let := dfinsupp_injective (R := R) (fun i => (K i).X (j+1))
  let := prod_injective (R := R) (productTerm K j) (sumTerm K (j+1))
  apply Module.injective_object_of_injective_module

lemma reduced_hom_exact (D : ModuleCat.{u} R) [Module.Finite R D]
    (j : ℤ) (hex : ∃ s : Finset ℕ, ∀ i ∉ s, ∀ f : D ⟶ (K i).X (j+1),
      f ≫ (K i).d (j+1) (j+1+1) = 0 → ∃ g : D ⟶ (K i).X j,
      g ≫ (K i).d j (j+1) = f)
    (f : D ⟶ (reducedComplex K).X (j+1))
    (hf : f ≫ (reducedComplex K).d (j+1) (j+1+1) = 0) :
    ∃ g : D ⟶ (reducedComplex K).X j,
      g ≫ (reducedComplex K).d j (j+1) = f := by
  classical
  let a : ∀ i, D →ₗ[R] (K i).X (j+1) := fun i =>
    (LinearMap.proj i).comp ((LinearMap.fst R _ _).comp f.hom)
  let b : D →ₗ[R] sumTerm K (j+1+1) := (LinearMap.snd R _ _).comp f.hom
  obtain ⟨s, hs⟩ := finite_support_map (R := R) _ D b
  obtain ⟨t, ht⟩ := hex
  have hcycle (i : ℕ) (x : D) :
      (K i).d (j+1) (j+1+1) (a i x) + b x i = 0 := by
    have h := congrArg (fun z : reducedTerm K (j+1+1) => z.1 i)
      (ConcreteCategory.congr_hom hf x)
    rw [reducedComplex_d] at h
    change (reducedD K (j+1) (f x)).1 i = 0 at h
    exact h
  have he (i : ℕ) : ∃ c : D →ₗ[R] (K i).X j,
      i ∉ s ∪ t → ((K i).d j (j+1)).hom.comp c = a i := by
    by_cases hi : i ∈ s ∪ t
    · exact ⟨0, fun h => (h hi).elim⟩
    · have his : i ∉ s := fun h => hi (Finset.mem_union_left _ h)
      have hit : i ∉ t := fun h => hi (Finset.mem_union_right _ h)
      obtain ⟨c, hc⟩ := ht i hit (ModuleCat.ofHom (a i)) (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
          ModuleCat.hom_zero, LinearMap.zero_apply, hs x i his, add_zero] using hcycle i x)
      exact ⟨c.hom, fun _ => congrArg ModuleCat.Hom.hom hc⟩
  choose c hc using he
  let q : D →ₗ[R] productTerm K j := LinearMap.pi c
  let v : ∀ i, D →ₗ[R] (K i).X (j+1) := fun i => a i - ((K i).d j (j+1)).hom.comp (c i)
  let w : D →ₗ[R] sumTerm K (j+1) := ∑ i ∈ s ∪ t, (DFinsupp.lsingle i).comp (v i)
  have hw (x : D) (i : ℕ) : w x i = a i x - (K i).d j (j+1) (c i x) := by
    by_cases hi : i ∈ s ∪ t
    · simp [w, LinearMap.sum_apply, DFinsupp.single_apply, hi, v]
    · have hci : (K i).d j (j+1) (c i x) = a i x := LinearMap.congr_fun (hc i hi) x
      simp [w, LinearMap.sum_apply, DFinsupp.single_apply, hi, hci, v]
  let g : D →ₗ[R] reducedTerm K j := q.prod w
  refine ⟨ModuleCat.ofHom g, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · ext i
    rw [reducedComplex_d]
    change (reducedD K j (g x)).1 i = a i x
    rw [reducedD_fst]
    change (K i).d j (j+1) (c i x) + w x i = a i x
    rw [hw]
    abel
  · apply DFinsupp.ext
    intro i
    rw [reducedComplex_d]
    change (reducedD K j (g x)).2 i = b x i
    rw [reducedD_snd]
    change -(K i).d (j+1) (j+1+1) (w x i) = b x i
    rw [hw, map_sub, d_d_apply, sub_zero]
    exact neg_eq_of_add_eq_zero_right (hcycle i x)

lemma reduced_isStrictlyGE
    (hK : ∀ i j, j < 0 → IsZero ((K i).X j)) :
    (reducedComplex K).IsStrictlyGE (-1) := by
  apply (CochainComplex.isStrictlyGE_iff _ _).mpr
  intro j hj
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let (i : ℕ) : Subsingleton ((K i).X j) :=
    ModuleCat.isZero_iff_subsingleton.mp (hK i j (by omega))
  let (i : ℕ) : Subsingleton ((K i).X (j+1)) :=
    ModuleCat.isZero_iff_subsingleton.mp (hK i (j+1) (by omega))
  change Subsingleton (reducedTerm K j)
  infer_instance

lemma reduced_not_exact_zero
    (hK : ∀ i j, j < 0 → IsZero ((K i).X j))
    (hnon : ∀ i, ∃ x : (K i).X 0, x ≠ 0 ∧ (K i).d 0 1 x = 0) :
    ¬ (reducedComplex K).ExactAt 0 := by
  classical
  choose x hxne hxd using hnon
  let p : reducedTerm K 0 := (x, 0)
  have hp : (reducedComplex K).d 0 1 p = 0 := by
    rw [show (1 : ℤ)=0+1 from rfl, reducedComplex_d]
    apply Prod.ext
    · ext i
      change (K i).d 0 1 (x i) + 0 = 0
      simpa only [add_zero] using hxd i
    · apply DFinsupp.ext
      intro i
      change -(K i).d 1 2 0 = 0
      rw [map_zero, neg_zero]
  intro hex
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff ((reducedComplex K).sc' (-1) 0 1)).mp
    ((HomologicalComplex.exactAt_iff' _ _ _ _ (by simp) (by simp)).mp hex) p hp
  change (reducedComplex K).d (-1) 0 y = p at hy
  have hd : (reducedComplex K).d (-1) 0 = ModuleCat.ofHom (reducedD K (-1)) :=
    reducedComplex_d K (-1)
  rw [hd] at hy
  change reducedTerm K (-1) at y
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset y.2.support
  have hy0 : y.2 i = 0 := DFinsupp.notMem_support_iff.mp hi
  have hy1 : y.1 i = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp (hK i (-1) (by omega))).elim _ _
  have h := congrArg (fun z : reducedTerm K 0 => z.1 i) hy
  change (reducedD K (-1) y).1 i = x i at h
  rw [reducedD_fst, hy0, hy1, map_zero, zero_add] at h
  exact hxne i h.symm

attribute [local instance] OAI.LittleFinitistic.Rickard.reducedProductsHasDerivedCategory
lemma not_isZero_Q_of_not_exact_zero (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : ¬ L.ExactAt 0) : ¬ IsZero (DerivedCategory.Q.obj L) := by
  intro hz
  apply h
  apply (HomologicalComplex.exactAt_iff_isZero_homology L 0).mpr
  exact ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map_isZero hz).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app L).symm

end LittleFinitistic.Rickard

end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Nakayama_Minimality
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDMinimal.augment_epi _root_.OAI.LittleFinitistic.PDMinimal.term_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Nakayama
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

lemma split_of_dual_surjective {P Q : ModuleCat.{u} R} (F : Frame R P)
    (d : P ⟶ Q) (h : Function.Surjective (LinearMap.lcomp k R d.hom)) :
    ∃ s : Q ⟶ P, d ≫ s = 𝟙 P := by
  classical
  choose c hc using fun i => h (F.c i)
  let s : Q →ₗ[R] P := ∑ i, (c i).smulRight (F.b i)
  refine ⟨ModuleCat.ofHom s, ?_⟩
  apply ModuleCat.hom_ext
  ext x
  change s (d x) = x
  simp only [s, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hh (i : Fin F.n) : c i (d x) = F.c i x := LinearMap.congr_fun (hc i) x
  simp only [hh]
  exact F.expand x

lemma nakayama_map_not_injective {P Q : ModuleCat.{u} R}
    [Module.Finite R P] [Module.Projective R P] [Nontrivial P]
    (d : P ⟶ Q) (h : ¬ ∃ s : Q ⟶ P, d ≫ s = 𝟙 P) :
    ¬ Function.Injective (map (k := k) d) := by
  intro hd
  apply h
  obtain ⟨F⟩ := frame_nonempty R P
  apply split_of_dual_surjective (k := k) F d
  apply LinearMap.dualMap_injective_iff.mp
  exact hd

variable [FiniteDimensional k R]

lemma minimal_differential_not_split (M : PDMinimal.FiniteModule k R) (n : ℕ)
    [Nontrivial (PDMinimal.term M (n+1))] :
    ¬ ∃ s : (PDMinimal.term M n).cat ⟶ (PDMinimal.term M (n+1)).cat,
      ModuleCat.ofHom (PDMinimal.differential M n) ≫ s = 𝟙 _ := by
  rintro ⟨s, hs⟩
  let d := PDMinimal.differential M n
  let e : PDMinimal.term M n →ₗ[R] PDMinimal.term M n := LinearMap.id - d.comp s.hom
  have he : (PDMinimal.augment M n).comp e = PDMinimal.augment M n := by
    ext x
    change PDMinimal.augment M n (x - d (s x)) = PDMinimal.augment M n x
    rw [map_sub]
    have hh := LinearMap.congr_fun (PDMinimal.augment_differential M n) (s x)
    change PDMinimal.augment M n (d (s x)) = 0 at hh
    rw [hh, sub_zero]
  have hes : Function.Surjective e := (PDMinimal.cover _).minimal e he
  have hei : Function.Injective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := e.restrictScalars k) rfl).mpr hes
  have hd (x : PDMinimal.term M (n+1)) : d x = 0 := by
    have hh : s (d x) = x := ConcreteCategory.congr_hom hs x
    apply hei
    change d x - d (s (d x)) = 0 - d (s 0)
    erw [hh, sub_self, map_zero, map_zero, sub_self]
  have hz (x : PDMinimal.term M (n+1)) : x=0 := by
    have hh : s (d x) = x := ConcreteCategory.congr_hom hs x
    erw [hd, map_zero] at hh
    exact hh.symm
  obtain ⟨x,y,hxy⟩ := exists_pair_ne (PDMinimal.term M (n+1))
  exact hxy ((hz x).trans (hz y).symm)

lemma minimal_nakayama_differential_noninjective (M : PDMinimal.FiniteModule k R) (n : ℕ)
    [Nontrivial (PDMinimal.term M (n+1))] :
    ¬ Function.Injective (map (k := k) (ModuleCat.ofHom (PDMinimal.differential M n))) := by
  apply nakayama_map_not_injective
  exact minimal_differential_not_split M n

end LittleFinitistic.Nakayama

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_ResolutionFamily
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.Nakayama.coindLine_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
private theorem mono_map_of_conjugate {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X₀ X₁ Y₀ Y₁ : C} (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁)
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (h : f = e₀.hom ≫ g ≫ e₁.inv)
    (hf : Mono (F.map f)) : Mono (F.map g) := by
  let := hf
  have hg : F.map g = F.map e₀.inv ≫ F.map f ≫ F.map e₁.hom := by
    rw [h, F.map_comp, F.map_comp]
    simp
  rw [hg]
  infer_instance

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
open PDMinimal

lemma translatedResolution_finite (M : FiniteModule k R) (d : ℕ) (j : ℤ) :
    Module.Finite R ((translatedResolution M d).X j) := by
  by_cases h : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE d).f n = j
  · obtain ⟨n, hn⟩ := h
    let : Module.Finite R ((complex M).X n) := (inferInstance : Module.Finite R (term M n))
    exact Module.Finite.equiv ((complex M).extendXIso _ hn).symm.toLinearEquiv
  · have hz := (complex M).isZero_extend_X (ComplexShape.embeddingUpIntLE d) j (by simpa using h)
    let : Subsingleton ((translatedResolution M d).X j) := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

lemma translatedResolution_projective (M : FiniteModule k R) (d : ℕ) (j : ℤ) :
    Module.Projective R ((translatedResolution M d).X j) := by
  by_cases h : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE d).f n = j
  · obtain ⟨n, hn⟩ := h
    let : Module.Projective R ((complex M).X n) :=
      (inferInstance : Module.Projective R (term M n))
    exact Module.Projective.of_equiv ((complex M).extendXIso _ hn).symm.toLinearEquiv
  · have hz := (complex M).isZero_extend_X (ComplexShape.embeddingUpIntLE d) j (by simpa using h)
    let : Subsingleton ((translatedResolution M d).X j) := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

lemma term_zero_above (M : FiniteModule k R) (d n : ℕ)
    (hd : HasProjectiveDimensionLE M.cat d) (hn : d < n) : Subsingleton (term M n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply term_zero_of_pdLE M m
  rw [← projectiveDimension_le_iff] at hd ⊢
  exact hd.trans (by exact_mod_cast (by omega : d ≤ m))

lemma translatedResolution_zero_negative (M : FiniteModule k R) (d : ℕ)
    (hd : HasProjectiveDimensionLE M.cat d) (j : ℤ) (hj : j < 0) :
    IsZero ((translatedResolution M d).X j) := by
  let n := (d - j).toNat
  have hn : (ComplexShape.embeddingUpIntLE d).f n = j := by
    rw [ComplexShape.embeddingUpIntLE_f]
    dsimp [n]
    omega
  have := term_zero_above M d n hd (by dsimp [n]; omega)
  exact ((complex M).extendXIso _ hn).isZero_iff.mpr
    (ModuleCat.isZero_iff_subsingleton.mpr (show Subsingleton (term M n) from inferInstance))

lemma translatedResolution_exact (M : FiniteModule k R) (d : ℕ) (j : ℤ) (hj : j ≠ d) :
    (translatedResolution M d).ExactAt j := by
  by_cases h : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE d).f n = j
  · obtain ⟨n, hn⟩ := h
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      simp only [ComplexShape.embeddingUpIntLE_f, Nat.cast_zero, sub_zero] at hn
      exact hj hn.symm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact ((complex M).extend_exactAt_iff _ hn).mpr (complex_exactAt M m)
  · exact (complex M).extend_exactAt _ j (by simpa using h)

variable (k)

lemma nakayamaComplex_hom_exact (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfin : ∀ j, Module.Finite R (P.X j)) (hproj : ∀ j, Module.Projective R (P.X j))
    (j : ℤ) (hex : P.ExactAt (j+1)) (f : Nakayama.DA k R ⟶ (nakayamaComplex k P).X (j+1))
    (hf : f ≫ (nakayamaComplex k P).d (j+1) (j+1+1) = 0) :
    ∃ g : Nakayama.DA k R ⟶ (nakayamaComplex k P).X j,
      g ≫ (nakayamaComplex k P).d j (j+1) = f := by
  let (i : ℤ) := hfin i
  let (i : ℤ) := hproj i
  obtain ⟨F⟩ := Nakayama.frame_nonempty R (P.X (j+1))
  obtain ⟨G⟩ := Nakayama.frame_nonempty R (P.X (j+1+1))
  obtain ⟨p, hp⟩ := Nakayama.eta_surjective k R _ F f.hom
  have hz : P.d (j+1) (j+1+1) p = 0 := by
    apply Nakayama.eta_injective k R _ G
    rw [← Nakayama.eta_natural, hp]
    have hf' := congrArg ModuleCat.Hom.hom hf
    change (Nakayama.map (P.d (j+1) (j+1+1))).comp f.hom = 0 at hf'
    rw [hf']
    ext h φ
    simp [Nakayama.etaMap]
    rfl
  have hx := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    ((HomologicalComplex.exactAt_iff' P j (j+1) (j+1+1) (by simp) (by simp)).mp hex)
  change LinearMap.range (P.d j (j+1)).hom = LinearMap.ker (P.d (j+1) (j+1+1)).hom at hx
  have hpker : p ∈ LinearMap.ker (P.d (j+1) (j+1+1)).hom := hz
  rw [← hx] at hpker
  obtain ⟨q, hq⟩ := hpker
  refine ⟨ModuleCat.ofHom (Nakayama.etaMap k R _ q), ?_⟩
  apply ModuleCat.hom_ext
  change (Nakayama.map (P.d j (j+1))).comp (Nakayama.etaMap k R _ q) = f.hom
  rw [Nakayama.eta_natural, hq, hp]

omit [FiniteDimensional k R] in
lemma nakayamaComplex_injective (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfin : ∀ j, Module.Finite R (P.X j)) (hproj : ∀ j, Module.Projective R (P.X j))
    (j : ℤ) : Injective ((nakayamaComplex k P).X j) := by
  let := hfin j
  let := hproj j
  exact Nakayama.object_injective k R (P.X j)

omit [FiniteDimensional k R] in
lemma nakayamaComplex_zero (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (j : ℤ) (h : IsZero (P.X j)) : IsZero ((nakayamaComplex k P).X j) := by
  exact (Nakayama.functor k R).map_isZero h

lemma translated_nakayama_zero_cycle (M : FiniteModule k R) (d : ℕ)
    (hd : 0 < d) (hterm : ¬ Subsingleton (term M d)) :
    ∃ x : (nakayamaComplex k (translatedResolution M d)).X 0,
      x ≠ 0 ∧ (nakayamaComplex k (translatedResolution M d)).d 0 1 x = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let : Nontrivial (term M (n+1)) := not_subsingleton_iff_nontrivial.mp hterm
  let e := ComplexShape.embeddingUpIntLE ((n+1 : ℕ) : ℤ)
  have h₀ : e.f (n+1) = 0 := by simp [e]
  have h₁ : e.f n = 1 := by simp [e]
  let P := translatedResolution M (n+1)
  let F := Nakayama.functor k R
  have he : P.d 0 1 = ((complex M).extendXIso e h₀).hom ≫
      ModuleCat.ofHom (differential M n) ≫ ((complex M).extendXIso e h₁).inv := by
    simpa only [P, translatedResolution, e, complex_d] using! (complex M).extend_d_eq e h₀ h₁
  have hn : ¬ Function.Injective ((nakayamaComplex k P).d 0 1).hom := by
    intro hi
    have hmono : Mono (F.map (P.d 0 1)) := (ModuleCat.mono_iff_injective _).mpr hi
    have hh : Mono (F.map (ModuleCat.ofHom (differential M n))) :=
      mono_map_of_conjugate F ((complex M).extendXIso e h₀) ((complex M).extendXIso e h₁)
        (P.d 0 1) (ModuleCat.ofHom (differential M n)) he hmono
    exact Nakayama.minimal_nakayama_differential_noninjective M n
      ((ModuleCat.mono_iff_injective _).mp hh)
  rw [Function.Injective] at hn
  push Not at hn
  obtain ⟨x, y, hxy, hne⟩ := hn
  refine ⟨x-y, sub_ne_zero.mpr hne, ?_⟩
  change ((nakayamaComplex k P).d 0 1).hom (x-y) = 0
  rw [map_sub, hxy, sub_self]

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_NonGeneration
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

attribute [local instance] OAI.LittleFinitistic.Rickard.nonGenerationHasDerivedCategory
lemma prop_injective_of_da
    (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (hcop : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I))
    (hD : P ((DerivedCategory.singleFunctor _ 0).obj (Nakayama.DA k R)))
    (M : ModuleCat.{u} R) [Injective M] :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  classical
  let V := (ModuleCat.restrictScalars (algebraMap k R)).obj M
  let b := Module.Free.chooseBasis k V
  let S := ModuleCat.of R (Π₀ _ : Module.Free.ChooseBasisIndex k V, Nakayama.DA k R)
  let cs : Cofan (fun _ : Module.Free.ChooseBasisIndex k V => Nakayama.DA k R) :=
    Cofan.mk S (fun i => ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun _ : Module.Free.ChooseBasisIndex k V => Nakayama.DA k R) i))
  have hc : IsColimit cs := by
    refine Cofan.IsColimit.mk _
      (fun t => ModuleCat.ofHom (DFinsupp.lsum ℤ (fun i => (t.inj i).hom))) ?_ ?_
    · intro t i
      ext x
      change (DFinsupp.lsum ℤ (fun i => (t.inj i).hom)) (DFinsupp.single i x) = (t.inj i).hom x
      simp only [DFinsupp.lsum_single]
    · intro t f hf
      apply ModuleCat.hom_ext
      apply DFinsupp.lhom_ext'
      intro i
      apply LinearMap.ext
      intro x
      have hh := ConcreteCategory.congr_hom (hf i) x
      change f.hom (DFinsupp.single i x) =
        (DFinsupp.lsum ℤ (fun i => (t.inj i).hom)) (DFinsupp.single i x)
      rw [DFinsupp.lsum_single]
      exact hh
  let := hcop (ULift.{u} ℕ)
  let : P.IsClosedUnderColimitsOfShape (Discrete ℕ) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{u} ℕ ≃ ℕ))
  let := hcop (Module.Free.ChooseBasisIndex k V)
  have hS : P ((DerivedCategory.singleFunctor _ 0).obj S) :=
    DerivedSupport.prop_single_of_cofan P cs hc (fun _ => hD)
  let e : S ≅ Nakayama.coind k R V :=
    (LinearEquiv.ofBijective (Nakayama.coindBasisMap V b)
      (Nakayama.coindBasisMap_bijective k R V b)).toModuleIso
  have hC : P ((DerivedCategory.singleFunctor _ 0).obj (Nakayama.coind k R V)) :=
    P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e) hS
  let j := Nakayama.moduleCoindInclusion k R M
  let : Mono j := Nakayama.moduleCoindInclusion_mono k R M
  let p := Injective.factorThru (𝟙 M) j
  have hjp : j ≫ p = 𝟙 M := Injective.comp_factorThru (𝟙 M) j
  let F := DerivedCategory.singleFunctor (ModuleCat R) 0
  exact DerivedSupport.localizing_of_retract (F.map j) (F.map p)
    (by rw [← F.map_comp, hjp, F.map_id]) P hC

lemma not_generate_of_minimal_family (M : ℕ → PDMinimal.FiniteModule k R)
    (d : ℕ → ℕ) (hd : ∀ i, i < d i)
    (hpd : ∀ i, HasProjectiveDimensionLE (M i).cat (d i))
    (hlast : ∀ i, ¬ Subsingleton (PDMinimal.term (M i) (d i))) :
    ¬ InjectivesGenerate R := by
  classical
  let K := fun i => nakayamaComplex k (translatedResolution (M i) (d i))
  let L := reducedComplex K
  have hkzero : ∀ i j, j < 0 → IsZero ((K i).X j) := fun i j hj =>
    nakayamaComplex_zero k _ j (translatedResolution_zero_negative (M i) (d i) (hpd i) j hj)
  have hknon : ∀ i, ∃ x : (K i).X 0, x ≠ 0 ∧ (K i).d 0 1 x = 0 := fun i =>
    translated_nakayama_zero_cycle k (M i) (d i) (by have := hd i; omega) (hlast i)
  have hkinj : ∀ i j, Injective ((K i).X j) := fun i j =>
    nakayamaComplex_injective k _ (translatedResolution_finite (M i) (d i))
      (translatedResolution_projective (M i) (d i)) j
  let : IsNoetherianRing R := IsNoetherianRing.of_finite k R
  let (j : ℤ) : Injective (L.X j) := reducedComplex_injective K hkinj j
  let : L.IsStrictlyGE (-1) := reduced_isStrictlyGE K hkzero
  let : L.IsKInjective := CochainComplex.isKInjective_of_injective L (-1)
  have hnon : ¬ IsZero (DerivedCategory.Q.obj L) :=
    not_isZero_Q_of_not_exact_zero L (reduced_not_exact_zero K hkzero hknon)
  let : Module.Finite R (Nakayama.DA k R) := Nakayama.da_finite k R
  have hex (j : ℤ) (f : Nakayama.DA k R ⟶ L.X j) (hf : f ≫ L.d j (j+1) = 0) :
      ∃ g : Nakayama.DA k R ⟶ L.X (j-1), g ≫ L.d (j-1) j = f := by
    have he : ∃ s : Finset ℕ, ∀ i ∉ s, ∀ f : Nakayama.DA k R ⟶ (K i).X (j-1+1),
        f ≫ (K i).d (j-1+1) (j-1+1+1) = 0 →
        ∃ g : Nakayama.DA k R ⟶ (K i).X (j-1), g ≫ (K i).d (j-1) (j-1+1) = f := by
      refine ⟨Finset.range (j.toNat+1), ?_⟩
      intro i hi f hf
      apply nakayamaComplex_hom_exact k _ (translatedResolution_finite (M i) (d i))
        (translatedResolution_projective (M i) (d i)) (j-1) _ f hf
      apply translatedResolution_exact
      have hdi := hd i
      simp only [Finset.mem_range, not_lt] at hi
      omega
    have hh := reduced_hom_exact K (Nakayama.DA k R) (j-1) he
    rw [sub_add_cancel] at hh
    exact hh f hf
  apply not_generate_of_orthogonal (DerivedCategory.Q.obj L) hnon
  intro N hN
  let := hN
  apply (perpendicular_iff (DerivedCategory.Q.obj L) _).mp
  apply prop_injective_of_da (k := k) (perpendicular (DerivedCategory.Q.obj L))
    (fun I => inferInstance) _ N
  apply (perpendicular_iff _ _).mpr
  exact orthogonal_single_of_hom_exact _ L hex

lemma not_injectivesGenerate_of_little_eq_top (k : Type u) [Field k] [Algebra k R]
    [FiniteDimensional k R]
    (h : littleFinitisticDimension R = ⊤) : ¬ InjectivesGenerate R := by
  obtain ⟨M, d, hd, hpd, hterm⟩ := exists_minimal_family (k := k) h
  exact not_generate_of_minimal_family M d hd hpd hterm

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Transport_DerivedEquivalence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
section DerivedTransport
universe w₁ w₂ v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
open CategoryTheory.Limits CategoryTheory.Functor

lemma mapDerivedCategory_isEquivalence (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] :
    e.functor.mapDerivedCategory.IsEquivalence := by
  let f := e.functor.mapHomologicalComplex (ComplexShape.up ℤ)
  let g := e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)
  let qC := DerivedCategory.Q (C := C)
  let qD := DerivedCategory.Q (C := D)
  let α : (f ⋙ qD) ⋙ e.inverse.mapDerivedCategory ≅ qC :=
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft f e.inverse.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (e.mapHomologicalComplex (ComplexShape.up ℤ)).unitIso.symm qC ≪≫
    Functor.leftUnitor qC
  let β : (g ⋙ qC) ⋙ e.functor.mapDerivedCategory ≅ qD :=
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft g e.functor.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (e.mapHomologicalComplex (ComplexShape.up ℤ)).counitIso qD ≪≫
    Functor.leftUnitor qD
  exact Localization.isEquivalence qC (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    qD (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    (f ⋙ qD) e.functor.mapDerivedCategory
    (g ⋙ qC) e.inverse.mapDerivedCategory α β

end DerivedTransport

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Transport_InjectiveGeneration
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.Nakayama.coind_injective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
section InjectiveGenerationTransport
universe v
variable {R S : Type v} [Ring R] [Ring S]
open CategoryTheory.Limits

lemma injectivesGenerate_of_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) (hR : InjectivesGenerate R) :
    InjectivesGenerate S := by
  let := HasDerivedCategory.standard (ModuleCat.{v} R)
  let := HasDerivedCategory.standard (ModuleCat.{v} S)
  let : e.functor.Additive := e.functor.additive_of_preserves_binary_products
  let : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  let F := e.functor.mapDerivedCategory
  let : F.IsEquivalence := mapDerivedCategory_isEquivalence e
  intro P hP hT hCol hI X
  let := hP
  let := hT
  let (index : Type v) := hCol index
  have h : ∀ Y, (P.inverseImage F) Y := by
    apply hR (P.inverseImage F) inferInstance inferInstance (fun I => inferInstance)
    intro M hM
    let := hM
    exact P.prop_of_iso ((e.functor.mapDerivedCategorySingleFunctor 0).app M).symm
      (hI (e.functor.obj M) inferInstance)
  exact P.prop_of_iso (F.asEquivalence.counitIso.app X) (h (F.asEquivalence.inverse.obj X))

lemma injectivesGenerate_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    InjectivesGenerate R ↔ InjectivesGenerate S :=
  ⟨injectivesGenerate_of_equivalence e, injectivesGenerate_of_equivalence e.symm⟩

end InjectiveGenerationTransport

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Transport_ProjectiveDimension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory

namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

section ProjectiveTransport
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [EnoughProjectives D]
open CategoryTheory.Limits

omit [EnoughProjectives D] in
lemma hasProjectiveDimensionLT_of_fullyFaithful
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] [F.PreservesProjectiveObjects]
    (X : C) (n : ℕ) [HasProjectiveDimensionLT (F.obj X) n] :
    HasProjectiveDimensionLT X n := by
  let := HasExt.standard C
  let := HasExt.standard D
  apply HasProjectiveDimensionLT.mk
  intro i hi Y e
  apply (F.mapExt_bijective_of_preservesProjectiveObjects X Y i).injective
  rw [map_zero]
  exact (F.mapExtAddHom X Y i e).eq_zero_of_hasProjectiveDimensionLT n hi

omit [EnoughProjectives D] in
lemma hasProjectiveDimensionLT_map
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesProjectiveObjects] (X : C) (n : ℕ) [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT (F.obj X) n := by
  induction n generalizing X with
  | zero =>
    exact (F.map_isZero (isZero_of_hasProjectiveDimensionLT_zero X)).hasProjectiveDimensionLT_zero
  | succ n ih =>
    cases n with
    | zero =>
      let : Projective X := projective_iff_hasProjectiveDimensionLT_one.mpr (by assumption)
      exact inferInstance
    | succ n =>
      let S := ShortComplex.mk (kernel.ι (Projective.π X)) (Projective.π X)
        (kernel.condition (Projective.π X))
      have hs : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π X) }
      have hk : HasProjectiveDimensionLT S.X₁ (n + 1) :=
        (hs.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
      let := hk
      exact (hs.map_of_exact F).hasProjectiveDimensionLT_X₃ (n + 1)
        (ih S.X₁) (by
          change HasProjectiveDimensionLT (F.obj (Projective.over X)) (n + 1 + 1)
          exact hasProjectiveDimensionLT_of_ge _ 1 _ (by omega))

omit [EnoughProjectives D] in
lemma projectiveDimension_fullyFaithful
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesProjectiveObjects] [F.Full] [F.Faithful] (X : C) :
    projectiveDimension (F.obj X) = projectiveDimension X := by
  have h (n : ℕ) : HasProjectiveDimensionLT (F.obj X) n ↔ HasProjectiveDimensionLT X n :=
    ⟨fun h => @hasProjectiveDimensionLT_of_fullyFaithful _ _ _ _ _ _ _ F _ _ _ _ _ _ X n h,
      fun h => @hasProjectiveDimensionLT_map _ _ _ _ _ _ _ F _ _ _ _ X n h⟩
  simp only [projectiveDimension, h]

lemma hasProjectiveDimensionLT_equivalence_iff (e : C ≌ D) (X : C) (n : ℕ) :
    HasProjectiveDimensionLT (e.functor.obj X) n ↔ HasProjectiveDimensionLT X n := by
  let : e.functor.Additive := e.functor.additive_of_preserves_binary_products
  let : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  constructor
  · intro h
    let : HasProjectiveDimensionLT (e.functor.obj X) n := h
    exact hasProjectiveDimensionLT_of_fullyFaithful e.functor X n
  · intro h
    let : HasProjectiveDimensionLT X n := h
    let : HasProjectiveDimensionLT (e.inverse.obj (e.functor.obj X)) n :=
      hasProjectiveDimensionLT_of_iso (show X ≅ e.inverse.obj (e.functor.obj X) from
        e.unitIso.app X) n
    exact hasProjectiveDimensionLT_of_fullyFaithful e.inverse (e.functor.obj X) n

lemma projectiveDimension_equivalence (e : C ≌ D) (X : C) :
    projectiveDimension (e.functor.obj X) = projectiveDimension X := by
  simp only [projectiveDimension, hasProjectiveDimensionLT_equivalence_iff e X]

end ProjectiveTransport

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Transport_ScalarRestriction
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

section RestrictionAlongSurjection
universe v
variable {R S : Type v} [Ring R] [Ring S]

open CategoryTheory.Limits

lemma restrictScalars_full (f : R →+* S) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{v} f).Full where
  map_surjective {M N} g := by
    refine ⟨ModuleCat.ofHom { g.hom with map_smul' := ?_ }, ?_⟩
    · intro s m
      obtain ⟨r, rfl⟩ := hf s
      exact g.hom.map_smul r m
    · rfl

lemma restrictScalars_preservesProjectives (f : R →+* S)
    [Module.Projective R ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))] :
    (ModuleCat.restrictScalars.{v} f).PreservesProjectiveObjects where
  projective_obj {P} hP := by
    classical
    let := hP
    let F := ModuleCat.restrictScalars.{v} f
    let Q := F.obj (ModuleCat.of S S)
    obtain ⟨i, hi⟩ := Module.projective_def'.mp (inferInstance : Module.Projective S P)
    let : Module.Projective R (F.obj (ModuleCat.of S (P →₀ S))) := by
      change Module.Projective R (P →₀ Q)
      exact Module.Projective.of_equiv (finsuppLequivDFinsupp R).symm
    let : Module.Projective R (F.obj P) := Module.Projective.of_split
      (F.map (ModuleCat.ofHom i)).hom
      (F.map (ModuleCat.ofHom (Finsupp.linearCombination S id))).hom (by
        ext x
        exact DFunLike.congr_fun hi x)
    exact inferInstance

lemma finite_restrictScalars (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{v} S) [Module.Finite S M] :
    Module.Finite R ((ModuleCat.restrictScalars f).obj M) := by
  let N := (ModuleCat.restrictScalars f).obj M
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := M)
  refine ⟨s, ?_⟩
  apply top_unique
  intro x hx
  have hx' : (x : M) ∈ Submodule.span S (s : Set M) := by rw [hs]; trivial
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    obtain ⟨r, rfl⟩ := hf a
    exact Submodule.smul_mem (Submodule.span R (show Set N from (s : Set M))) r ih

lemma littleFinitisticDimension_le_restrictScalars (f : R →+* S)
    (hf : Function.Surjective f)
    [Module.Projective R ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))] :
    littleFinitisticDimension S ≤ littleFinitisticDimension R := by
  let := restrictScalars_full f hf
  let := restrictScalars_preservesProjectives f
  refine iSup_le fun M => iSup_le fun hfg => iSup_le fun hpd => ?_
  let := hfg
  have heq := projectiveDimension_fullyFaithful (ModuleCat.restrictScalars f) M
  rw [← heq]
  exact le_iSup_of_le ((ModuleCat.restrictScalars f).obj M)
    (le_iSup_of_le (finite_restrictScalars f hf M)
      (le_iSup_of_le (by rwa [heq]) le_rfl))

end RestrictionAlongSurjection

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Algebra
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instModuleT _root_.OAI.LittleFinitistic.CummingsConstruction.instAlgebraT _root_.OAI.LittleFinitistic.CummingsConstruction.newRegularπ_epi _root_.OAI.LittleFinitistic.CummingsConstruction.periodicAug_quasiIso _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace TriangularConstruction
universe v
variable (C E U : Type v)

variable [Ring C] [Ring E] [AddCommGroup U] [Module E U] [Module Cᵐᵒᵖ U]
  [SMulCommClass E Cᵐᵒᵖ U]

omit [SMulCommClass E Cᵐᵒᵖ U] in
lemma toC_surjective : Function.Surjective (toC C E U) :=
  fun c => ⟨((c, 0), 0), rfl⟩

lemma rightCorner_projective :
    Module.Projective (Algebra C E U)ᵐᵒᵖ
      ((ModuleCat.restrictScalars (toC C E U).op).obj (ModuleCat.of Cᵐᵒᵖ Cᵐᵒᵖ)) := by
  apply Module.Projective.of_split (rightCornerSection C E U)
    (Module.compHom.toLinearMap (toC C E U).op)
  ext x
  rfl

lemma right_little_lower_bound :
    littleFinitisticDimension Cᵐᵒᵖ ≤ littleFinitisticDimension (Algebra C E U)ᵐᵒᵖ := by
  let := rightCorner_projective C E U
  apply littleFinitisticDimension_le_restrictScalars (toC C E U).op
  intro c
  obtain ⟨t, ht⟩ := toC_surjective C E U c.unop
  exact ⟨MulOpposite.op t, congrArg MulOpposite.op ht⟩

variable (k : Type v) [Field k] [_root_.Algebra k C] [_root_.Algebra k E] [Module k U]
  [IsScalarTower k E U] [IsScalarTower k Cᵐᵒᵖ U]
  [FiniteDimensional k C] [FiniteDimensional k E] [FiniteDimensional k U]

omit [Module E U] [Module Cᵐᵒᵖ U] [SMulCommClass E Cᵐᵒᵖ U]
  [IsScalarTower k E U] [IsScalarTower k Cᵐᵒᵖ U] in
lemma finiteDimensional : FiniteDimensional k (Algebra C E U) :=
  inferInstanceAs (FiniteDimensional k ((C × E) × OffDiagonal C E U))

end TriangularConstruction

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Socle
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instModuleT _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instSMulT _root_.OAI.LittleFinitistic.CummingsConstruction.newRegularπ_epi _root_.OAI.LittleFinitistic.CummingsConstruction.periodicAug_quasiIso _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CummingsConstruction.cval_mul _root_.OAI.LittleFinitistic.CummingsConstruction.ehead_mul _root_.OAI.LittleFinitistic.CummingsConstruction.epsDifferential_sq _root_.OAI.LittleFinitistic.CummingsConstruction.etail_mul _root_.OAI.LittleFinitistic.CummingsConstruction.newDifferential_sq _root_.OAI.LittleFinitistic.CummingsConstruction.oval_mul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace CummingsConstruction
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]

variable (χ : C →ₐ[k] (ι → k))
instance instFiniteDimensionalTOfFinite [Finite ι] [FiniteDimensional k C] : FiniteDimensional k (T χ) :=
  TriangularConstruction.finiteDimensional C (NewCorner k ι) (SimpleSum χ) k

lemma augmentation_surjective (hχ : Function.Surjective χ) : Function.Surjective (augmentation χ) := by
  intro v
  obtain ⟨c, hc⟩ := hχ (v ∘ Sum.inl)
  refine ⟨((c, fun i => TrivSqZeroExt.inl (v (.inr i))), 0), ?_⟩
  ext i
  cases i with
  | inl i => exact congrFun hc i
  | inr i => rfl

variable [DecidableEq ι]

lemma socle_ne_zero (i : Sum ι ι) : socle χ i ≠ 0 := by
  intro h
  cases i with
  | inl i =>
    have := congrArg (fun x : T χ => (TriangularConstruction.offValue x.snd : ι → k) i) h
    change (Pi.single i (1 : k) : ι → k) i = 0 at this
    simp at this
  | inr i =>
    have := congrArg (fun x : T χ => (x.fst.2 i).snd) h
    simp [socle] at this

end CummingsConstruction
end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Kasch_Radical
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace Kasch

universe v w
variable {R : Type u} [Ring R]

lemma map_radical_le (J : Ideal R) {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) : (radicalPart J P).map f ≤ radicalPart J Q := by
  rw [radicalPart, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

lemma isNilpotent_of_range_le_radical {P : Type v} [AddCommGroup P] [Module R P]
    (J : Ideal R) [J.IsTwoSided] (hJ : ∃ n : ℕ, J ^ n = ⊥)
    (f : P →ₗ[R] P) (hf : LinearMap.range f ≤ radicalPart J P) : IsNilpotent f := by
  have hn (n : ℕ) : LinearMap.range (f ^ n) ≤ J ^ n • (⊤ : Submodule R P) := by
    induction n with
    | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
    | succ n ih =>
      rw [pow_succ, Module.End.mul_eq_comp, LinearMap.range_comp]
      apply le_trans (Submodule.map_mono hf)
      rw [radicalPart, Submodule.map_smul'', Submodule.map_top]
      apply le_trans (Submodule.smul_mono le_rfl ih)
      rw [← Submodule.mul_smul, Ideal.IsTwoSided.pow_succ]
  obtain ⟨n, hnil⟩ := hJ
  refine ⟨n, ?_⟩
  apply LinearMap.range_eq_bot.mp
  apply le_bot_iff.mp
  simpa [hnil] using hn n

lemma top_semisimple {S : Type v} [Ring S] [IsSemisimpleRing S]
    (χ : R →+* S) (hχ : Function.Surjective χ)
    (M : Type w) [AddCommGroup M] [Module R M] :
    IsSemisimpleModule R (M ⧸ radicalPart (RingHom.ker χ) M) := by
  let : IsSemisimpleRing (R ⧸ (RingHom.ker χ)) :=
    (χ.quotientKerEquivOfSurjective hχ).symm.isSemisimpleRing
  exact (Module.isTorsionBySet_quotient_ideal_smul M (RingHom.ker χ)).isSemisimpleModule_iff.mp
    inferInstance

end Kasch
end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Kasch_ProjectiveSplitting
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace Kasch
universe v w
variable {R : Type u} [Ring R]
section SplitBasic
variable {k : Type u} [Field k] [Algebra k R]
variable {ι : Type u} (χ : R →ₐ[k] (ι → k))
variable (a : ι → R) (ha : ∀ i, a i ≠ 0)
  (hmul : ∀ i r, a i * r = χ r i • a i)

include hmul in
lemma annihilates_radical {P : Type v} [AddCommGroup P] [Module R P]
    {x : P} (hx : x ∈ radicalPart (RingHom.ker χ.toRingHom) P) (i : ι) : a i • x = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    rw [← mul_smul, hmul]
    have h : χ r = 0 := hr
    simp [h]
  · intro x y hx hy
    simp only [smul_add, hx, hy, add_zero]

include ha hmul in
lemma finsupp_mem_radical_of_annihilated {σ : Type v} (x : σ →₀ R)
    (hx : ∀ i, a i • x = 0) : x ∈ radicalPart (RingHom.ker χ.toRingHom) (σ →₀ R) := by
  classical
  have hcoef (s : σ) : χ (x s) = 0 := by
    ext i
    have hi : a i * x s = 0 := congrArg (fun y : σ →₀ R => y s) (hx i)
    rw [hmul] at hi
    exact (smul_eq_zero.mp hi).resolve_right (ha i)
  rw [← Finsupp.sum_single x]
  apply Submodule.sum_mem
  intro s hs
  have heq : Finsupp.single s (x s) = x s • Finsupp.single s (1 : R) := by simp
  rw [heq]
  exact Submodule.smul_mem_smul (hcoef s) (Submodule.mem_top)

include ha hmul in
lemma projective_mem_radical_iff {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (x : P) :
    x ∈ radicalPart (RingHom.ker χ.toRingHom) P ↔ ∀ i, a i • x = 0 := by
  constructor
  · exact fun hx i => annihilates_radical χ a hmul hx i
  · intro hx
    obtain ⟨s, hs⟩ := (Module.projective_def' (R := R) (P := P)).mp inferInstance
    have hx' : s x ∈ radicalPart (RingHom.ker χ.toRingHom) (P →₀ R) :=
      finsupp_mem_radical_of_annihilated χ a ha hmul (s x) (fun i => by
        rw [← s.map_smul, hx i, map_zero])
    have he : (Finsupp.linearCombination R id) (s x) = x := DFunLike.congr_fun hs x
    rw [← he]
    exact map_radical_le (RingHom.ker χ.toRingHom) (Finsupp.linearCombination R id)
      (Submodule.mem_map_of_mem hx')

include ha hmul in
lemma projective_mono_reflects_radical {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) (hf : Function.Injective f) {x : P}
    (hx : f x ∈ radicalPart (RingHom.ker χ.toRingHom) Q) :
    x ∈ radicalPart (RingHom.ker χ.toRingHom) P := by
  rw [projective_mem_radical_iff χ a ha hmul]
  intro i
  apply hf
  rw [map_smul, map_zero]
  exact annihilates_radical χ a hmul hx i

include ha hmul in
lemma projective_mono_splits [Finite ι]
    (hχ : Function.Surjective χ) (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    {P : Type v} {Q : Type w} [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (f : P →ₗ[R] Q) (hf : Function.Injective f) :
    ∃ g : Q →ₗ[R] P, g.comp f = LinearMap.id := by
  let J := RingHom.ker χ.toRingHom
  let p := radicalPart J P
  let q := radicalPart J Q
  let fbar : P ⧸ p →ₗ[R] Q ⧸ q := p.mapQ q f
    (Submodule.map_le_iff_le_comap.mp (map_radical_le J f))
  have hfbar : Function.Injective fbar := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨x, rfl⟩ := p.mkQ_surjective x
    have hx' : f x ∈ q := (Submodule.Quotient.mk_eq_zero q).mp hx
    exact (Submodule.Quotient.mk_eq_zero p).mpr
      (projective_mono_reflects_radical χ a ha hmul f hf hx')
  let : IsSemisimpleModule R (Q ⧸ q) := top_semisimple χ.toRingHom hχ Q
  obtain ⟨gbar, hgbar⟩ := IsSemisimpleModule.extension_property fbar hfbar
    (LinearMap.id : P ⧸ p →ₗ[R] P ⧸ p)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property p.mkQ (gbar.comp q.mkQ)
    p.mkQ_surjective
  have hnil : IsNilpotent (1 - g.comp f : Module.End R P) := by
    apply isNilpotent_of_range_le_radical J hJ
    rintro _ ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero p).mp
    change p.mkQ (x - g (f x)) = 0
    rw [map_sub]
    have hg' := DFunLike.congr_fun hg (f x)
    have hgbar' := DFunLike.congr_fun hgbar (p.mkQ x)
    change p.mkQ (g (f x)) = gbar (q.mkQ (f x)) at hg'
    change gbar (q.mkQ (f x)) = p.mkQ x at hgbar'
    rw [hg', hgbar', sub_self]
  have hu : IsUnit (g.comp f) := by simpa using hnil.isUnit_one_sub
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  refine ⟨u.comp g, ?_⟩
  simpa only [Module.End.mul_eq_comp, Module.End.one_eq_id, LinearMap.comp_assoc] using hu

end SplitBasic
end Kasch
end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Kasch_FiniteDimension
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace Kasch
universe v w
variable {R : Type u} [Ring R]
section SplitBasic
variable {k : Type u} [Field k] [Algebra k R]
variable {ι : Type u} (χ : R →ₐ[k] (ι → k))
variable (a : ι → R) (ha : ∀ i, a i ≠ 0)
  (hmul : ∀ i r, a i * r = χ r i • a i)
include ha hmul in
lemma projective_of_hasFiniteBound [Finite ι]
    (hχ : Function.Surjective χ) (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    (M : ModuleCat.{u} R) (n : ℕ) [HasProjectiveDimensionLT M n] : Projective M := by
  induction n generalizing M with
  | zero =>
    exact (CategoryTheory.isZero_of_hasProjectiveDimensionLT_zero M).projective
  | succ n ih =>
    cases n with
    | zero => exact projective_iff_hasProjectiveDimensionLT_one.mpr inferInstance
    | succ n =>
      let S := ShortComplex.mk (Limits.kernel.ι (Projective.π M)) (Projective.π M)
        (Limits.kernel.condition (Projective.π M))
      have hs : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π M) }
      let : HasProjectiveDimensionLT S.X₁ (n + 1) :=
        (hs.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
      let : Projective S.X₁ := ih S.X₁
      obtain ⟨r, hr⟩ := projective_mono_splits χ a ha hmul hχ hJ S.f.hom
        ((ModuleCat.mono_iff_injective S.f).mp hs.mono_f)
      let spl := ShortComplex.Splitting.ofExactOfRetraction S hs.exact
        (ModuleCat.ofHom r) (ModuleCat.hom_ext hr) hs.epi_g
      exact (show Retract M S.X₂ from
        { i := spl.s, r := S.g, retract := spl.s_g }).projective

include ha hmul in
lemma projective_of_finiteDimension [Finite ι]
    (hχ : Function.Surjective χ) (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    (M : ModuleCat.{u} R) (hM : projectiveDimension M < ⊤) : Projective M := by
  obtain ⟨n, hn⟩ := (projectiveDimension_ne_top_iff M).mp hM.ne
  let := hn
  exact projective_of_hasFiniteBound χ a ha hmul hχ hJ M (n + 1)

end SplitBasic
end Kasch

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Transport_FiniteModules
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
section FiniteTransport
universe v
variable {R S : Type v} [Ring R] [Ring S]

lemma compactElement_orderIso {α β : Type*} [CompleteLattice α] [CompleteLattice β]
    (e : α ≃o β) {a : α} (h : IsCompactElement a) : IsCompactElement (e a) := by
  rw [CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup]
  intro ι f hf
  have hf' : a ≤ ⨆ i, e.symm (f i) := by
    rw [← e.symm.map_iSup]
    exact (e.le_symm_apply).mpr hf
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ h (fun i => e.symm (f i)) hf'
  refine ⟨s, ?_⟩
  simpa only [e.map_iSup, e.apply_symm_apply, Finset.sup_eq_iSup] using e.monotone hs

lemma moduleFinite_equivalence_iff (e : ModuleCat.{v} R ≌ ModuleCat.{v} S)
    (M : ModuleCat.{v} R) : Module.Finite S (e.functor.obj M) ↔ Module.Finite R M := by
  let o : Submodule R M ≃o Submodule S (e.functor.obj M) :=
    (ModuleCat.subobjectModule M).symm.trans
      ((Subobject.lowerEquivalence (MonoOver.congr M e)).toOrderIso.trans
        (ModuleCat.subobjectModule (e.functor.obj M)))
  rw [Module.finite_def, Module.finite_def, Submodule.fg_iff_compact,
    Submodule.fg_iff_compact]
  constructor
  · intro h
    simpa using compactElement_orderIso o.symm h
  · intro h
    simpa using compactElement_orderIso o h

lemma littleFinitisticDimension_le_big (R : Type v) [Ring R] :
    littleFinitisticDimension R ≤ bigFinitisticDimension R := by
  refine iSup_le fun M => iSup_le fun _ => iSup_le fun h => ?_
  exact le_iSup_of_le M (le_iSup_of_le h le_rfl)

lemma littleFinitisticDimension_le_of_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    littleFinitisticDimension R ≤ littleFinitisticDimension S := by
  refine iSup_le fun M => iSup_le fun hM => iSup_le fun hpd => ?_
  have hf : Module.Finite S (e.functor.obj M) :=
    (moduleFinite_equivalence_iff e M).mpr hM
  have hd : projectiveDimension (e.functor.obj M) < ⊤ := by
    rwa [projectiveDimension_equivalence e M]
  exact le_iSup_of_le (e.functor.obj M) (le_iSup_of_le hf
    (le_iSup_of_le hd (le_of_eq (projectiveDimension_equivalence e M).symm)))

lemma littleFinitisticDimension_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    littleFinitisticDimension R = littleFinitisticDimension S :=
  le_antisymm (littleFinitisticDimension_le_of_equivalence e)
    (littleFinitisticDimension_le_of_equivalence e.symm)

lemma bigFinitisticDimension_le_of_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    bigFinitisticDimension R ≤ bigFinitisticDimension S := by
  refine iSup_le fun M => iSup_le fun hpd => ?_
  have hd : projectiveDimension (e.functor.obj M) < ⊤ := by
    rwa [projectiveDimension_equivalence e M]
  exact le_iSup_of_le (e.functor.obj M)
    (le_iSup_of_le hd (le_of_eq (projectiveDimension_equivalence e M).symm))

lemma bigFinitisticDimension_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    bigFinitisticDimension R = bigFinitisticDimension S :=
  le_antisymm (bigFinitisticDimension_le_of_equivalence e)
    (bigFinitisticDimension_le_of_equivalence e.symm)

end FiniteTransport

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_ZeroDimensions
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
section ZeroDimensions
variable {R k : Type u} [Ring R] [Nontrivial R] [Field k] [Algebra k R]

lemma littleFinitisticDimension_nonneg : 0 ≤ littleFinitisticDimension R := by
  have hpd : projectiveDimension (ModuleCat.of R R) = 0 :=
    (projectiveDimension_eq_zero_iff _).mpr ⟨inferInstance, fun h => by
      let := ModuleCat.isZero_iff_subsingleton.mp h
      exact (one_ne_zero : (1 : R) ≠ 0) (Subsingleton.elim _ _)⟩
  exact le_iSup_of_le (ModuleCat.of R R) (le_iSup_of_le (inferInstance : Module.Finite R R)
    (le_iSup_of_le (by rw [hpd]; norm_cast) hpd.ge))

lemma dimensions_zero_of_splitBasic_rightSocle {ι : Type u} [Finite ι]
    (χ : R →ₐ[k] (ι → k)) (hχ : Function.Surjective χ)
    (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    (a : ι → R) (ha : ∀ i, a i ≠ 0)
    (hmul : ∀ i r, a i * r = χ r i • a i) :
    littleFinitisticDimension R = 0 ∧ bigFinitisticDimension R = 0 := by
  have hb : bigFinitisticDimension R ≤ 0 := by
    refine iSup_le fun M => iSup_le fun hpd => ?_
    let : Projective M := Kasch.projective_of_finiteDimension χ a ha hmul hχ hJ M hpd
    exact (projectiveDimension_le_iff M 0).mpr inferInstance
  have hl : 0 ≤ littleFinitisticDimension R := littleFinitisticDimension_nonneg
  have hlb := littleFinitisticDimension_le_big R
  exact ⟨le_antisymm (hlb.trans hb) hl, le_antisymm hb (hl.trans hlb)⟩

end ZeroDimensions

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Augmentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instModuleT _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instSMulT _root_.OAI.LittleFinitistic.CummingsConstruction.newRegularπ_epi _root_.OAI.LittleFinitistic.CummingsConstruction.periodicAug_quasiIso _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CummingsConstruction.cval_mul _root_.OAI.LittleFinitistic.CummingsConstruction.ehead_mul _root_.OAI.LittleFinitistic.CummingsConstruction.epsDifferential_sq _root_.OAI.LittleFinitistic.CummingsConstruction.etail_mul _root_.OAI.LittleFinitistic.CummingsConstruction.newDifferential_sq _root_.OAI.LittleFinitistic.CummingsConstruction.oval_mul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace CummingsConstruction
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k))
lemma mem_ker_augmentation (x : T χ) :
    x ∈ RingHom.ker (augmentation χ).toRingHom ↔ χ x.fst.1 = 0 ∧ newAugmentation x.fst.2 = 0 := by
  change (Sum.elim (χ x.fst.1) (newAugmentation x.fst.2) : Sum ι ι → k) = 0 ↔ _
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (.inl i), funext fun i => congrFun h (.inr i)⟩
  · rintro ⟨h₁, h₂⟩
    ext i
    cases i <;> simp [h₁, h₂]

lemma ker_square_pureOldRadical :
    (RingHom.ker (augmentation χ).toRingHom) ^ 2 ≤ pureOldRadical χ := by
  rw [Submodule.pow_succ, Submodule.pow_one]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨hxc, hxe⟩ := (mem_ker_augmentation χ x).mp hx
  obtain ⟨hyc, hye⟩ := (mem_ker_augmentation χ y).mp hy
  change x.fst.2 * y.fst.2 = 0 ∧
    newAugmentation x.fst.2 * SimpleSum.value (TriangularConstruction.offValue y.snd) +
      χ y.fst.1 * SimpleSum.value (TriangularConstruction.offValue x.snd) = 0 ∧ χ (x.fst.1 * y.fst.1) = 0
  refine ⟨?_, by simp [hxe, hyc], by simp [map_mul, hxc]⟩
  ext i : 1
  have hx0 : (x.fst.2 i).fst = 0 := congrFun hxe i
  have hy0 : (y.fst.2 i).fst = 0 := congrFun hye i
  apply TrivSqZeroExt.ext <;> simp [hx0, hy0]

lemma pow_le_comap_pow_noncomm {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I ≤ J.comap f) (n : ℕ) : I ^ n ≤ (J ^ n).comap f := by
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ, Submodule.pow_succ]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change f (x * y) ∈ J ^ n * J
    rw [map_mul]
    exact Ideal.mul_mem_mul (ih hx) (h hy)

lemma augmentation_ker_nilpotent (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥) :
    ∃ n : ℕ, (RingHom.ker (augmentation χ).toRingHom) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  let K := RingHom.ker (augmentation χ).toRingHom
  let J := RingHom.ker χ.toRingHom
  have hcomap : K ≤ J.comap (TriangularConstruction.toC C (NewCorner k ι) (SimpleSum χ)) := by
    intro x hx
    exact ((mem_ker_augmentation χ x).mp hx).1
  have hpow := pow_le_comap_pow_noncomm _ K J hcomap (n + 2)
  have hjn : J ^ (n + 2) = ⊥ := by
    apply le_bot_iff.mp
    exact (Ideal.pow_le_pow_right (I := J) (Nat.le_add_right n 2)).trans hn.le
  rw [hjn] at hpow
  refine ⟨n + 2, le_bot_iff.mp ?_⟩
  intro x hx
  have hc : x.fst.1 = 0 := hpow hx
  have hp := ker_square_pureOldRadical χ ((Ideal.pow_le_pow_right (I := K) (by omega : 2 ≤ n + 2)) hx)
  change x = 0
  apply TrivSqZeroExt.ext
  · exact Prod.ext hc hp.1
  · exact hp.2.1

variable [DecidableEq ι]

lemma left_dimensions_zero [Finite ι] [Nontrivial C]
    (hχ : Function.Surjective χ) (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥) :
    littleFinitisticDimension (T χ) = 0 ∧ bigFinitisticDimension (T χ) = 0 := by
  let : Nontrivial (T χ) := inferInstanceAs (Nontrivial ((C × NewCorner k ι) ×
    TriangularConstruction.OffDiagonal C (NewCorner k ι) (SimpleSum χ)))
  exact dimensions_zero_of_splitBasic_rightSocle (augmentation χ)
    (augmentation_surjective χ hχ) (augmentation_ker_nilpotent χ hJ)
    (socle χ) (socle_ne_zero χ) (socle_mul χ)

end CummingsConstruction
end LittleFinitistic

end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Asymmetry
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst _root_.OAI.LittleFinitistic.cyclicRing_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open CategoryTheory
namespace LittleFinitistic.AsymmetryConstruction
universe u
variable {k A ι : Type u} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [Nontrivial A] [Fintype ι]
variable (χ : Aᵐᵒᵖ →ₐ[k] (ι → k))

lemma all_clauses
    (hχ : Function.Surjective χ)
    (hnil : ∃ n : ℕ, (RingHom.ker χ.toRingHom)^n = ⊥)
    (hA : littleFinitisticDimension A = ⊤) :
    FiniteDimensional k (Lambda χ) ∧
      littleFinitisticDimension (Lambda χ) = ⊤ ∧
      bigFinitisticDimension (Lambda χ) = ⊤ ∧
      littleFinitisticDimension (Lambda χ)ᵐᵒᵖ = 0 ∧
      bigFinitisticDimension (Lambda χ)ᵐᵒᵖ = 0 ∧
      ¬ InjectivesGenerate (Lambda χ) ∧ InjectivesGenerate (Lambda χ)ᵐᵒᵖ := by
  classical
  let eA := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)
  have hinf : littleFinitisticDimension (Lambda χ) = ⊤ := by
    apply top_unique
    rw [← hA, ← littleFinitisticDimension_equivalence eA]
    exact TriangularConstruction.right_little_lower_bound _ _ _
  have hbig : bigFinitisticDimension (Lambda χ) = ⊤ :=
    top_unique (hinf ▸ littleFinitisticDimension_le_big (Lambda χ))
  let eT := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (RingEquiv.opOp (CummingsConstruction.T χ))
  obtain ⟨hlz, hbz⟩ := CummingsConstruction.left_dimensions_zero χ hχ hnil
  have hlz' : littleFinitisticDimension (Lambda χ)ᵐᵒᵖ = 0 :=
    (littleFinitisticDimension_equivalence eT).trans hlz
  have hbz' : bigFinitisticDimension (Lambda χ)ᵐᵒᵖ = 0 :=
    (bigFinitisticDimension_equivalence eT).trans hbz
  refine ⟨inferInstance, hinf, hbig, hlz', hbz', ?_, ?_⟩
  · exact Rickard.not_injectivesGenerate_of_little_eq_top k hinf
  · exact (injectivesGenerate_equivalence eT).mpr
      (CummingsConstruction.injectivesGenerate χ hχ hnil)
end LittleFinitistic.AsymmetryConstruction

end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Augmentation_Directed
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.VertexDecomposition.equiv_apply _root_.OAI.LittleFinitistic.VertexDecomposition.equiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.DirectedBound
universe u

namespace DirectedSystem
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedSystem k A n)

lemma coefficient_vertex (i j : D.Vertices) :
    D.coefficient (D.e i) j = if j = i then 1 else 0 := by
  classical
  apply (D.coefficient_eq_iff _ _ _).mpr
  split_ifs with h
  · subst j; simp [D.idem]
  · rw [D.orthogonal j i (fun hji => h (Subtype.ext hji))]
    simp

lemma augmentation_surjective : Function.Surjective D.augmentation := by
  classical
  intro s
  refine ⟨∑ i : D.Vertices, s i • D.e i, ?_⟩
  ext j
  simp [map_sum, map_smul, augmentation, coefficient_vertex]

lemma mem_augmentation_ker_iff (a : A) :
    a ∈ RingHom.ker D.augmentation.toRingHom ↔ ∀ i : Fin n, D.e i * a * D.e i = 0 := by
  constructor
  · intro ha i
    by_cases hi : D.e i = 0
    · simp [hi]
    · rw [D.coefficient_spec a ⟨i, hi⟩]
      have := congrFun ha ⟨i, hi⟩
      change D.coefficient a ⟨i, hi⟩ = 0 at this
      rw [this, zero_smul]
  · intro ha
    change D.augmentation a = 0
    ext i
    apply (D.coefficient_eq_iff _ _ _).mpr
    simpa using ha i

lemma ker_corner_vanish {a : A} (ha : a ∈ RingHom.ker D.augmentation.toRingHom)
    (i j : Fin n) (hij : i.val < j.val + 1) : D.e i * a * D.e j = 0 := by
  by_cases h : i = j
  · subst j; exact (D.mem_augmentation_ker_iff a).mp ha i
  · exact D.directed j i (by have hne : i.val ≠ j.val := fun hval => h (Fin.ext hval); omega) a

lemma pow_ker_corner_vanish (m : ℕ) {a : A}
    (ha : a ∈ (RingHom.ker D.augmentation.toRingHom) ^ m)
    (i j : Fin n) (hij : i.val < j.val + m) : D.e i * a * D.e j = 0 := by
  induction m generalizing a i j with
  | zero => exact D.directed j i (by simpa using hij) a
  | succ m ih =>
    rw [Submodule.pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [D.corner_mul]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : i.val < l.val + m
      · rw [ih hx i l hil, zero_mul]
      · rw [D.ker_corner_vanish hy l j (by omega), mul_zero]
    · intro x y hx hy
      simp [mul_add, add_mul, hx, hy]

lemma augmentation_ker_nilpotent :
    ∃ m : ℕ, (RingHom.ker D.augmentation.toRingHom) ^ m = ⊥ := by
  refine ⟨n, le_bot_iff.mp ?_⟩
  intro a ha
  change a = 0
  have he : (∑ i, D.e i) * a * (∑ j, D.e j) = 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro i _
    exact D.pow_ker_corner_vanish n ha i j (by omega)
  simpa [D.complete] using he
end DirectedSystem
end LittleFinitistic.DirectedBound

end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Augmentation_SplitBasic
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.CummingsConstruction.instAlgebraT _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.SplitBasic
universe v
variable {k : Type v} [Field k]
lemma pow_le_comap_pow {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I ≤ J.comap f) (n : ℕ) : I ^ n ≤ (J ^ n).comap f := by
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ, Submodule.pow_succ]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change f (x * y) ∈ J ^ n * J
    rw [map_mul]
    exact Ideal.mul_mem_mul (ih hx) (h hy)

section SquareZero
variable {R M : Type v} [Ring R] [Algebra k R] [AddCommGroup M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [Module k M] [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
variable {ι : Type v} (χ : R →ₐ[k] (ι → k))
lemma squareZero_surjective (hχ : Function.Surjective χ) :
    Function.Surjective (squareZeroAugmentation (M := M) χ) := by
  intro s
  obtain ⟨r, hr⟩ := hχ s
  exact ⟨TrivSqZeroExt.inl r, hr⟩
lemma squareZero_ker_nilpotent (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥) :
    ∃ n : ℕ, (RingHom.ker (squareZeroAugmentation (M := M) χ).toRingHom) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  let f := (TrivSqZeroExt.fstHom k R M).toRingHom
  let K := RingHom.ker (squareZeroAugmentation (M := M) χ).toRingHom
  let J := RingHom.ker χ.toRingHom
  let L := RingHom.ker f
  have h : K ^ n ≤ L := by
    have hp := pow_le_comap_pow f K J (by intro x hx; exact hx) n
    rw [hn] at hp
    exact hp
  have hL : L * L = ⊥ := by
    apply le_bot_iff.mp
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    change x * y = 0
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hx, hy]
  refine ⟨n + n, le_bot_iff.mp ?_⟩
  rw [Ideal.IsTwoSided.pow_add]
  exact (Ideal.mul_mono h h).trans hL.le
end SquareZero

section Product
variable {R S ι κ : Type v} [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (χ : R →ₐ[k] (ι → k)) (ψ : S →ₐ[k] (κ → k))
lemma product_surjective (hχ : Function.Surjective χ) (hψ : Function.Surjective ψ) :
    Function.Surjective (productAugmentation χ ψ) := by
  intro s
  obtain ⟨r, hr⟩ := hχ (s ∘ Sum.inl)
  obtain ⟨t, ht⟩ := hψ (s ∘ Sum.inr)
  refine ⟨(r,t), ?_⟩
  ext i
  cases i <;> simp [productAugmentation, hr, ht]
lemma product_ker_nilpotent
    (hχ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    (hψ : ∃ n : ℕ, (RingHom.ker ψ.toRingHom) ^ n = ⊥) :
    ∃ n : ℕ, (RingHom.ker (productAugmentation χ ψ).toRingHom) ^ n = ⊥ := by
  obtain ⟨m, hm⟩ := hχ
  obtain ⟨n, hn⟩ := hψ
  let K := RingHom.ker (productAugmentation χ ψ).toRingHom
  have h₁ := pow_le_comap_pow (RingHom.fst R S) K (RingHom.ker χ.toRingHom)
    (by intro x hx; exact funext (fun i => congrFun hx (Sum.inl i))) m
  have h₂ := pow_le_comap_pow (RingHom.snd R S) K (RingHom.ker ψ.toRingHom)
    (by intro x hx; exact funext (fun i => congrFun hx (Sum.inr i))) n
  rw [hm] at h₁
  rw [hn] at h₂
  refine ⟨m + n, le_bot_iff.mp ?_⟩
  intro x hx
  exact Prod.ext (h₁ (Ideal.pow_le_pow_right (by omega) hx))
    (h₂ (Ideal.pow_le_pow_right (by omega) hx))
end Product

section Opposite
variable {R ι : Type v} [Ring R] [Algebra k R] (χ : R →ₐ[k] (ι → k))
lemma opposite_surjective (hχ : Function.Surjective χ) :
    Function.Surjective (oppositeAugmentation χ) := by
  intro s
  obtain ⟨r, hr⟩ := hχ s
  exact ⟨MulOpposite.op r, hr⟩
lemma unop_mem_pow_ker (n : ℕ) {x : Rᵐᵒᵖ}
    (hx : x ∈ (RingHom.ker (oppositeAugmentation χ).toRingHom) ^ n) :
    x.unop ∈ (RingHom.ker χ.toRingHom) ^ n := by
  induction n generalizing x with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ] at hx
    rw [Ideal.IsTwoSided.pow_succ]
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      exact Ideal.mul_mem_mul hz (ih hy)
    · intro y z hy hz
      exact add_mem hy hz
lemma opposite_ker_nilpotent (hχ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥) :
    ∃ n : ℕ, (RingHom.ker (oppositeAugmentation χ).toRingHom) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := hχ
  refine ⟨n, le_bot_iff.mp ?_⟩
  intro x hx
  have h := unop_mem_pow_ker χ n hx
  rw [hn] at h
  exact MulOpposite.unop_injective h
end Opposite
end LittleFinitistic.SplitBasic

end
end

end OAI
end

section
-- module Solutions.Q221_FA.Finitistic_Ordinary_OrdinaryBlockBimodule
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instAddCommGroup _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instIsScalarTowerEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModule _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModuleEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k L R O T : Type u} [Field k] [Ring L] [Ring R]
  [AddCommGroup O] [AddCommGroup T]

open CategoryTheory
open scoped TensorProduct
variable {B : Type u} [Ring B] [Algebra k B]

theorem ordinary_finite (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ)
    (a : ℤ) (l : ℕ) [FiniteDimensional k B]
    [∀ n, FiniteDimensional k ((underlyingComplex (k := k) P).X n)] :
    FiniteDimensional k (BimoduleX P a l) := inferInstance
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.Q221_FA.Finitistic_Selected_SelectedOrdinaryAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FiniteSelectionFamily.instFiniteDimensionalComplexCarrierVector _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedOrdinaryAlgebra
open SelectedFixedDiagram QuadraticEncoding
open OrdinarySimulation

instance X_finite : FiniteDimensional ℂ X := ordinary_finite _ _ _

instance A_finite : FiniteDimensional ℂ A :=
  inferInstanceAs (FiniteDimensional ℂ (D × X))
end LittleFinitistic.SelectedOrdinaryAlgebra

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.SelectedBasic
open SelectedOrdinaryAlgebra SelectedFixedDiagram QuadraticEncoding
open OrdinarySimulation SplitBasic

lemma diagonal_surjective : Function.Surjective diagonalAugmentation :=
  product_surjective _ _ baseSystem.augmentation_surjective tensorSystem.augmentation_surjective
lemma diagonal_ker_nilpotent :
    ∃ n : ℕ, (RingHom.ker diagonalAugmentation.toRingHom)^n = ⊥ :=
  product_ker_nilpotent _ _ baseSystem.augmentation_ker_nilpotent tensorSystem.augmentation_ker_nilpotent

lemma augmentationA_surjective : Function.Surjective augmentationA :=
  squareZero_surjective _ diagonal_surjective
lemma augmentationA_ker_nilpotent :
    ∃ n : ℕ, (RingHom.ker augmentationA.toRingHom)^n = ⊥ :=
  squareZero_ker_nilpotent _ diagonal_ker_nilpotent

lemma augmentationC_surjective : Function.Surjective augmentationC :=
  opposite_surjective _ augmentationA_surjective
lemma augmentationC_ker_nilpotent :
    ∃ n : ℕ, (RingHom.ker augmentationC.toRingHom)^n = ⊥ :=
  opposite_ker_nilpotent _ augmentationA_ker_nilpotent
end LittleFinitistic.SelectedBasic

namespace LittleFinitistic

theorem extreme_left_right_asymmetry_oai :
    ∃ (Λ : Type) (_ : Ring Λ) (_ : Algebra ℂ Λ),
      FiniteDimensional ℂ Λ ∧
      littleFinitisticDimension Λ = ⊤ ∧ bigFinitisticDimension Λ = ⊤ ∧
      littleFinitisticDimension Λᵐᵒᵖ = 0 ∧ bigFinitisticDimension Λᵐᵒᵖ = 0 ∧
      ¬ InjectivesGenerate Λ ∧ InjectivesGenerate Λᵐᵒᵖ := by
  classical
  let Λ := AsymmetryConstruction.Lambda SelectedBasic.augmentationC
  refine ⟨Λ, inferInstance, inferInstance, ?_⟩
  exact AsymmetryConstruction.all_clauses SelectedBasic.augmentationC
    SelectedBasic.augmentationC_surjective SelectedBasic.augmentationC_ker_nilpotent
    Main.infinite_littleFinitisticDimension
end LittleFinitistic

end
end

end OAI
end

theorem solution : type_of% @OAI.LittleFinitistic.extreme_left_right_asymmetry_oai := @OAI.LittleFinitistic.extreme_left_right_asymmetry_oai
