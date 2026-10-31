-- Prove2me | solution 1 for HuangN13.N13GaussianGlobalZeroCarrierDlog.factorizationUnit_dlog_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T07:42:51.831329+00:00
-- url     : https://prove2.me/submissions/683df662-2994-4c8c-a7a7-0a389e4ee30f

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GaussianCubicField_integralClosure_eq_adjoin
import Theorems.Thm_MazurProof_N13GaussianCubicField_minpoly_alpha
import Theorems.Thm_MazurProof_N13GaussianGlobalReductionTwo_shiftedTheta_root_h
import Theorems.Thm_MazurProof_N13GaussianNamedUnitTransport_orderToGaussian_apply
import Theorems.Thm_MazurProof_N13LocalDlogRegimes_gaussianIDual_sq
import Theorems.Thm_MazurProof_N13LocalDlogRegimes_gaussian_cubic_jet_relation

import Definitions.Def_HuangN13_GaussianUnitLogCore

set_option autoImplicit false

section
section
set_option autoImplicit false
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL MazurProof.N13GlobalKummerPID.fieldL
private def integralClosureToClassNumberOrder (x : O) :
    N13GaussianClassNumberOne.O :=
  ⟨x.val, isIntegralElem_int_of x.property⟩
end
end MazurProof.N13GlobalKummerPID
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
private theorem subtypeConstructor_val {A : Type*} {p : A → Prop}
    (a : A) (ha : p a) :
    (⟨a, ha⟩ : Subtype p).val = a := rfl
end
end MazurProof.N13GlobalKummerPID
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL MazurProof.N13GlobalKummerPID.fieldL MazurProof.N13GlobalKummerPID.intAlgebraL
private theorem integralClosureToClassNumberOrder_val (x : O) :
    (integralClosureToClassNumberOrder x).val = x.val :=
  subtypeConstructor_val x.val
    (isIntegralElem_int_of (g := algebraMap ℤ L) x.property)
end
end MazurProof.N13GlobalKummerPID
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GlobalKummerPID
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianClassNumberOne.fieldL
/-- The normalization order and the class-number order have literally the
same underlying element of the ambient number field.  Exporting this small
carrier theorem prevents downstream proofs from unfolding the full ring
equivalence. -/
@[simp] theorem coe_integralClosureEquivClassNumberOrder
    (x : O) :
    (integralClosureEquivClassNumberOrder.toEquiv.toFun x).val =
      x.val :=
  integralClosureToClassNumberOrder_val x
end
end MazurProof.N13GlobalKummerPID
end
end

section
section
set_option autoImplicit false
namespace MazurProof.RamifiedDlog
open TrivSqZeroExt
noncomputable section
variable {k : Type*} [Field k]
@[simp] theorem unitOf_val (a b : k) (ha : a ≠ 0) :
    (unitOf a b ha : DualNumber k) = (a, b) :=
  by
    unfold unitOf
    exact IsUnit.unit_spec _
end
end MazurProof.RamifiedDlog
end
end

section
section
set_option autoImplicit false
namespace MazurProof.RamifiedDlog
open TrivSqZeroExt
noncomputable section
variable {k : Type*} [Field k]
@[simp] theorem dlog_unitOf (a b : k) (ha : a ≠ 0) :
    dlog (unitOf a b ha) = b / a := by
  simp [dlog]
end
end MazurProof.RamifiedDlog
end
end

section
section
set_option autoImplicit false
namespace MazurProof.RamifiedDlog
open TrivSqZeroExt
noncomputable section
variable {k : Type*} [Field k]
/-- In characteristic two every square has zero first ramified logarithm. -/
theorem dlog_sq [CharP k 2] (z : (DualNumber k)ˣ) :
    dlog (z ^ 2) = 0 := by
  rw [pow_two, dlog_mul]
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  linear_combination htwo * dlog z
end
end MazurProof.RamifiedDlog
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped CharTwo
namespace MazurProof.N13GaussianOrderTwo
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
open Module
@[simp] theorem reduction_theta :
    reduction theta = thetaDual := by
  exact AdjoinRoot.lift_root _
end
end MazurProof.N13GaussianOrderTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped CharTwo
namespace MazurProof.N13GaussianOrderTwo
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
open Module
@[simp] theorem reduction_scalar (z : Z2) :
    reduction (algebraMap Z2 Order z) = padicScalarDualHom z := by
  simp [reduction, gaussianReduction, AdjoinRoot.algebraMap_eq']
end
end MazurProof.N13GaussianOrderTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianGlobalReductionTwo.giAlgebraOrder
@[simp] theorem relativeToOrder_gen :
    relativeToOrder
        N13GaussianCubicField.relativeIntegralPowerBasis.gen =
      N13GaussianOrderTwo.theta - 9 := by
  exact PowerBasis.lift_gen
    N13GaussianCubicField.relativeIntegralPowerBasis
    (N13GaussianOrderTwo.theta - 9)
    _
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianGlobalReductionTwo.fieldL
@[simp] theorem relativeToOrder_theta :
    relativeToOrder relativeTheta =
      N13GaussianOrderTwo.theta := by
  rw [relativeTheta, map_add, relativeToOrder_gen]
  have h9 :
      relativeToOrder (9 : RelativeO) =
        (9 : Order) := by
    exact map_natCast relativeToOrder 9
  rw [h9]
  ring
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianNumberField.intAlgebraAbsoluteIntegers MazurProof.N13GaussianNumberField.intAlgebraL MazurProof.N13GaussianNumberField.intAlgebraRelativeIntegers MazurProof.N13GaussianGlobalReductionTwo.fieldL
@[simp] theorem ringOfIntegersToOrder_relative
    (x : RelativeO) :
    ringOfIntegersToOrder (relativeToRingOfIntegers x) =
      relativeToOrder x := by
  simp [ringOfIntegersToOrder, relativeToRingOfIntegers]
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
theorem map_relativeTheta :
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianGlobalReductionTwo.relativeTheta =
      N13GaussianFieldEquiv.gaussianTheta := by
  change
    ((N13GaussianCubicField.relativeIntegralPowerBasis.gen :
        N13GaussianGlobalReductionTwo.RelativeO) : Lg) + 9 =
      N13GaussianCubicField.alpha + 9
  rw [N13GaussianCubicField.coe_relativeIntegralPowerBasis_gen]
end
end MazurProof.N13GaussianNamedUnitTransport
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianLowDegree
noncomputable section
open N13GaussianOrderTwo
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
/-- Polynomial evaluation commutes with the exact first-jet reduction.
The resulting jet has no infinitesimal component. -/
theorem reduction_thetaEval (U : Z2[X]) :
    reduction (thetaEval U) = inl (residueEval U) := by
  let residueDualHom : ZMod 2 →+* DualNumber F8 :=
    (algebraMap F8 (DualNumber F8)).comp
      (algebraMap (ZMod 2) F8)
  have hscalar :
      reduction.comp (algebraMap Z2 Order) =
        padicScalarDualHom := by
    apply RingHom.ext
    intro z
    exact reduction_scalar z
  have hcomp :
      residueDualHom.comp PadicInt.toZMod =
        padicScalarDualHom := by
    apply RingHom.ext
    intro z
    rfl
  calc
    reduction (thetaEval U) =
        U.eval₂ padicScalarDualHom thetaDual := by
      rw [thetaEval, Polynomial.hom_eval₂, hscalar,
        reduction_theta]
    _ = (residuePolynomial U).eval₂
          residueDualHom thetaDual := by
      rw [residuePolynomial, Polynomial.eval₂_map, hcomp]
    _ = inl
          ((residuePolynomial U).eval₂
            (algebraMap (ZMod 2) F8) alpha) := by
      simpa [residueDualHom, thetaDual,
        TrivSqZeroExt.algebraMap_eq_inl'] using
        (Polynomial.hom_eval₂
          (residuePolynomial U)
          (algebraMap (ZMod 2) F8)
          (algebraMap F8 (DualNumber F8))
          alpha).symm
    _ = inl (residueEval U) := by
      change inl
          ((residuePolynomial U).eval₂
            (AdjoinRoot.of residueCubic)
            (AdjoinRoot.root residueCubic)) =
        inl (AdjoinRoot.mk residueCubic (residuePolynomial U))
      exact congrArg
        (fun z : AdjoinRoot residueCubic =>
          (inl z : DualNumber F8))
        (by
          simpa only [aeval_def, AdjoinRoot.algebraMap_eq] using
            (AdjoinRoot.aeval_eq (f := residueCubic)
              (residuePolynomial U)))
end
end MazurProof.N13GaussianLowDegree
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianLowDegree
noncomputable section
open N13GaussianOrderTwo
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
@[simp] theorem lowDegreeJet_val
    (U : Z2[X])
    (hne : residuePolynomial U ≠ 0)
    (hdeg : (residuePolynomial U).natDegree ≤ 2) :
    (lowDegreeJet U hne hdeg : DualNumber F8) =
      reduction (thetaEval U) := by
  rw [reduction_thetaEval]
  ext <;> simp [lowDegreeJet]
end
end MazurProof.N13GaussianLowDegree
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianLowDegree
noncomputable section
open N13GaussianOrderTwo
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
/-- Every primitive low-degree integral polynomial has zero first
ramified logarithm at `θ`. -/
theorem dlog_lowDegreeJet
    (U : Z2[X])
    (hne : residuePolynomial U ≠ 0)
    (hdeg : (residuePolynomial U).natDegree ≤ 2) :
    RamifiedDlog.dlog (lowDegreeJet U hne hdeg) = 0 := by
  simp [lowDegreeJet]
end
end MazurProof.N13GaussianLowDegree
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
theorem dlog_globalPrimitiveJet (D : LowRep) :
    RamifiedDlog.dlog (globalPrimitiveJet D) = 0 :=
  dlog_lowDegreeJet _ _ _
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13GaussianGlobalZeroCarrierDlog.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianGlobalZeroCarrierDlog.fieldLg
/-- The two maximal-order presentations send an integral polynomial
evaluation to the same carrier in the Gaussian cubic field. -/
theorem normalizationOrderEquiv_integralEval
    (U : ℤ[X]) :
    N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
        (N13GlobalKummerNormalization.integralEval U) =
      relativeToRingOfIntegers
        (eval₂
          (algebraMap ℤ
            N13GaussianGlobalReductionTwo.RelativeO)
          relativeTheta U) := by
  apply NumberField.RingOfIntegers.ext
  have hfun :
      N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
          (N13GlobalKummerNormalization.integralEval U) =
        N13GlobalKummerPID.integralClosureEquivClassNumberOrder.toFun
          (N13GlobalKummerNormalization.integralEval U) := rfl
  rw [hfun, N13GlobalKummerPID.coe_integralClosureEquivClassNumberOrder,
    N13GlobalKummerNormalization.coe_integralEval]
  have hrelative
      (z : N13GaussianGlobalReductionTwo.RelativeO) :
      (((relativeToRingOfIntegers z : On)) :
          N13GaussianCubicField.L) =
        algebraMap
          N13GaussianGlobalReductionTwo.RelativeO
          N13GaussianCubicField.L z := by
    calc
      (((relativeToRingOfIntegers z : On)) :
          N13GaussianCubicField.L) =
          N13GaussianNamedUnitTransport.orderToGaussian
            (relativeToRingOfIntegers z) :=
        (N13GaussianNamedUnitTransport.orderToGaussian_apply _).symm
      _ =
          algebraMap
            N13GaussianGlobalReductionTwo.RelativeO
            N13GaussianCubicField.L z := by
        simp [N13GaussianNamedUnitTransport.orderToGaussian,
          relativeToRingOfIntegers]
  rw [hrelative]
  have hInt :
      (algebraMap
          N13GaussianGlobalReductionTwo.RelativeO
          N13GaussianCubicField.L).comp
          (algebraMap ℤ
            N13GaussianGlobalReductionTwo.RelativeO) =
        algebraMap ℤ N13GaussianCubicField.L :=
    RingHom.ext_int _ _
  symm
  calc
    algebraMap
          N13GaussianGlobalReductionTwo.RelativeO
          N13GaussianCubicField.L
          (eval₂
            (algebraMap ℤ
              N13GaussianGlobalReductionTwo.RelativeO)
            relativeTheta U) =
        eval₂
          ((algebraMap
              N13GaussianGlobalReductionTwo.RelativeO
              N13GaussianCubicField.L).comp
            (algebraMap ℤ
              N13GaussianGlobalReductionTwo.RelativeO))
          (algebraMap
            N13GaussianGlobalReductionTwo.RelativeO
            N13GaussianCubicField.L relativeTheta) U := by
      exact Polynomial.hom_eval₂ _ _ _ _
    _ =
        eval₂ (algebraMap ℤ N13GaussianCubicField.L)
          N13GaussianFieldEquiv.gaussianTheta U := by
      rw [hInt, N13GaussianNamedUnitTransport.map_relativeTheta]
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13GaussianGlobalZeroCarrierDlog.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianGlobalZeroCarrierDlog.fieldLg
/-- Hence the normalized global Kummer integer is literally the displayed
low-degree polynomial evaluation in the fixed integral order at two. -/
theorem ringOfIntegersToOrder_normalizedKummerInteger
    (D : LowRep) :
    ringOfIntegersToOrder
        (N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
          (N13GlobalKummerNormalization.normalizedKummerInteger D)) =
      thetaEval (globalPrimitiveZ2 D) := by
  rw [N13GlobalKummerNormalization.normalizedKummerInteger,
    normalizationOrderEquiv_integralEval,
    ringOfIntegersToOrder_relative]
  have hInt :
      relativeToOrder.comp
          (algebraMap ℤ
            N13GaussianGlobalReductionTwo.RelativeO) =
        (algebraMap Z2 Order).comp
          (algebraMap ℤ Z2) :=
    RingHom.ext_int _ _
  calc
    relativeToOrder
          (eval₂
            (algebraMap ℤ
              N13GaussianGlobalReductionTwo.RelativeO)
            relativeTheta
            (N13GlobalKummerNormalization.primitiveNormalization
              D.toSemi.u)) =
        eval₂
          (relativeToOrder.comp
            (algebraMap ℤ
              N13GaussianGlobalReductionTwo.RelativeO))
          (relativeToOrder relativeTheta)
          (N13GlobalKummerNormalization.primitiveNormalization
            D.toSemi.u) := by
      exact Polynomial.hom_eval₂ _ _ _ _
    _ =
        eval₂
          ((algebraMap Z2 Order).comp (algebraMap ℤ Z2))
          N13GaussianOrderTwo.theta
          (N13GlobalKummerNormalization.primitiveNormalization
            D.toSemi.u) := by
      rw [hInt, relativeToOrder_theta]
    _ =
        eval₂ (algebraMap Z2 Order) N13GaussianOrderTwo.theta
          ((N13GlobalKummerNormalization.primitiveNormalization
            D.toSemi.u).map (algebraMap ℤ Z2)) := by
      rw [Polynomial.eval₂_map]
    _ = thetaEval (globalPrimitiveZ2 D) := rfl
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
theorem globalReduction_normalizedKummerInteger
    (D : LowRep) :
    globalReduction
        (N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
          (N13GlobalKummerNormalization.normalizedKummerInteger D)) =
      (globalPrimitiveJet D : DualNumber F8) := by
  change
    reduction
        (ringOfIntegersToOrder
          (N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
            (N13GlobalKummerNormalization.normalizedKummerInteger D))) =
      (globalPrimitiveJet D : DualNumber F8)
  rw [ringOfIntegersToOrder_normalizedKummerInteger]
  exact
    (lowDegreeJet_val
      (globalPrimitiveZ2 D)
      (residuePolynomial_globalPrimitiveZ2_ne_zero D)
      (Polynomial.natDegree_map_le.trans
        (globalPrimitiveZ2_natDegree_le D))).symm
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
/-- The unit in the factorization `x = ε y²` has zero first ramified
logarithm.  The proof is an identity of group homomorphisms: the primitive
left side has constant first jet and the square on the right contributes
twice its logarithm. -/
theorem factorizationUnit_dlog_eq_zero
    (D : LowRep)
    (ε : Oiˣ) (y : Oi)
    (hxy :
      N13GlobalKummerNormalization.normalizedKummerInteger D =
        (ε : Oi) * y ^ 2) :
    N13GaussianNamedUnitSquareclasses.globalDlogAdd
        (Additive.ofMul
          (Units.map
            N13GaussianNormalizationOrderTransport.normalizationOrderEquiv.toMonoidHom
            ε)) = 0 := by
  let e :=
    N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
  let εn : Onˣ := Units.map e.toMonoidHom ε
  let yn : On := e y
  have hxyOn :
      e (N13GlobalKummerNormalization.normalizedKummerInteger D) =
        (εn : On) * yn ^ 2 := by
    dsimp only [εn, yn]
    change
      e (N13GlobalKummerNormalization.normalizedKummerInteger D) =
        e (ε : Oi) * e y ^ 2
    simpa only [map_mul, map_pow] using congrArg e hxy
  have hxUnit :
      IsUnit
        (globalReduction
          (e
            (N13GlobalKummerNormalization.normalizedKummerInteger D))) := by
    rw [globalReduction_normalizedKummerInteger]
    exact (globalPrimitiveJet D).isUnit
  have hprod :
      IsUnit
        (globalReduction (εn : On) *
          globalReduction yn ^ 2) := by
    rw [← map_pow, ← map_mul, ← hxyOn]
    exact hxUnit
  have hynSq : IsUnit (globalReduction yn ^ 2) :=
    ((Commute.all
      (globalReduction (εn : On))
      (globalReduction yn ^ 2)).isUnit_mul_iff.mp hprod).2
  have hyn : IsUnit (globalReduction yn) :=
    (isUnit_pow_iff (by norm_num : 2 ≠ 0)).mp hynSq
  let yJet : JetUnit := hyn.unit
  let εJet : JetUnit := Units.map globalReduction.toMonoidHom εn
  have hyJet :
      (yJet : DualNumber F8) = globalReduction yn :=
    IsUnit.unit_spec _
  have hJet :
      globalPrimitiveJet D = εJet * yJet ^ 2 := by
    apply Units.ext
    change
      (globalPrimitiveJet D : DualNumber F8) =
        globalReduction (εn : On) *
          (yJet : DualNumber F8) ^ 2
    rw [hyJet, ← map_pow, ← map_mul, ← hxyOn,
      globalReduction_normalizedKummerInteger]
  have hdlog :=
    congrArg RamifiedDlog.dlog hJet
  have hεJet :
      RamifiedDlog.dlog εJet = 0 := by
    simpa only [dlog_globalPrimitiveJet,
      RamifiedDlog.dlog_mul, RamifiedDlog.dlog_sq,
      add_zero] using hdlog.symm
  exact hεJet
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg
theorem solution
    (D : MazurProof.N13GaussianGlobalZeroCarrierDlog.LowRep)
    (ε : MazurProof.N13GaussianGlobalZeroCarrierDlog.Oiˣ) (y : MazurProof.N13GaussianGlobalZeroCarrierDlog.Oi)
    (hxy :
      MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D =
        (ε : MazurProof.N13GaussianGlobalZeroCarrierDlog.Oi) * y ^ 2) :
    MazurProof.N13GaussianNamedUnitSquareclasses.globalDlogAdd
        (Additive.ofMul
          (Units.map
            MazurProof.N13GaussianNormalizationOrderTransport.normalizationOrderEquiv.toMonoidHom
            ε)) = 0 := by
  exact MazurProof.N13GaussianGlobalZeroCarrierDlog.factorizationUnit_dlog_eq_zero D ε y hxy
