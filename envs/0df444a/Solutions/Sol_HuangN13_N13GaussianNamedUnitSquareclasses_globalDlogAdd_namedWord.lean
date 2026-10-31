-- Prove2me | solution 1 for HuangN13.N13GaussianNamedUnitSquareclasses.globalDlogAdd_namedWord
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T07:42:49.76372+00:00
-- url     : https://prove2.me/submissions/9fa8e323-0011-4ae9-8364-0196698a53aa

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GaussianCubicField_integralClosure_eq_adjoin
import Theorems.Thm_MazurProof_N13GaussianCubicField_minpoly_alpha
import Theorems.Thm_MazurProof_N13GaussianGlobalReductionTwo_shiftedTheta_root_h
import Theorems.Thm_MazurProof_N13GaussianNamedUnitSquareclasses_relativeZeta_sq
import Theorems.Thm_MazurProof_N13GaussianOrderTwo_i_sq
import Theorems.Thm_MazurProof_N13LocalDlogRegimes_gaussian_cubic_jet_relation

import Definitions.Def_HuangN13_GaussianUnitLogCore

set_option autoImplicit false

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
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
@[simp] theorem alpha_cubed :
    alpha ^ 3 = alpha + 1 := by
  have h : alpha ^ 3 + (alpha + 1) = 0 := by
    simpa only [add_assoc] using alpha_relation
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
end
end MazurProof.N13LocalDlogTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
@[simp] theorem alpha_pow_four :
    alpha ^ 4 = alpha ^ 2 + alpha := by
  calc
    alpha ^ 4 = alpha * alpha ^ 3 := by ring
    _ = alpha * (alpha + 1) := by rw [alpha_cubed]
    _ = alpha ^ 2 + alpha := by ring
end
end MazurProof.N13LocalDlogTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
theorem dlog_zeta :
    RamifiedDlog.dlog zetaJet = 1 := by
  simp [zetaJet]
end
end MazurProof.N13LocalDlogTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
theorem dlog_e1 :
    RamifiedDlog.dlog e1Jet = alpha ^ 2 := by
  rw [e1Jet, RamifiedDlog.dlog_unitOf,
    div_eq_iff alpha_sq_add_one_ne_zero]
  calc
    alpha = (alpha ^ 2 + alpha) + alpha ^ 2 := by
      rw [add_comm (alpha ^ 2) alpha]
      exact (CharTwo.add_cancel_right alpha (alpha ^ 2)).symm
    _ = alpha ^ 4 + alpha ^ 2 := by rw [alpha_pow_four]
    _ = alpha ^ 2 * (alpha ^ 2 + 1) := by ring
end
end MazurProof.N13LocalDlogTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
theorem dlog_e2 :
    RamifiedDlog.dlog e2Jet = alpha + alpha ^ 2 := by
  rw [e2Jet, RamifiedDlog.dlog_unitOf,
    div_eq_iff alpha_sq_add_alpha_add_one_ne_zero]
  calc
    alpha ^ 2 = (alpha ^ 2 + alpha) + alpha := by
      exact (CharTwo.add_cancel_right (alpha ^ 2) alpha).symm
    _ = alpha ^ 4 + alpha := by rw [alpha_pow_four]
    _ = alpha ^ 4 + 2 * alpha ^ 3 + 2 * alpha ^ 2 + alpha := by
      rw [charTwo]
      ring
    _ = (alpha + alpha ^ 2) * (alpha ^ 2 + alpha + 1) := by
      ring
end
end MazurProof.N13LocalDlogTwo
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
@[simp] theorem reduction_i :
    reduction i = gaussianIDual := by
  simp [reduction, i]
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
private theorem dual_two_eq_zero :
    (2 : DualNumber F8) = 0 := by
  ext
  · exact charTwo
  · exact TrivSqZeroExt.snd_natCast (R := F8) (M := F8) 2
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
@[simp] theorem reduction_e1Order :
    reduction e1Order = (e1Jet : DualNumber F8) := by
  simp only [e1Order, map_add, map_sub, map_mul, map_pow, map_one,
    reduction_i, reduction_theta, e1Jet,
    RamifiedDlog.unitOf_val]
  ext <;> simp [gaussianIDual, thetaDual] <;> ring
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
@[simp] theorem reduction_e2Order :
    reduction e2Order = (e2Jet : DualNumber F8) := by
  simp only [e2Order, map_add, map_mul, map_pow, map_ofNat, map_one,
    reduction_i, reduction_theta, e2Jet,
    RamifiedDlog.unitOf_val]
  rw [dual_two_eq_zero]
  ext <;> simp [gaussianIDual, thetaDual] <;> ring
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
@[simp] theorem giToOrder_i :
    giToOrder N13GaussianGlobalArithmetic.i =
      N13GaussianOrderTwo.i := by
  simp [giToOrder, N13GaussianGlobalArithmetic.i]
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
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.giAlgebraOrder
@[simp] theorem algebraMap_gi_i :
    algebraMap GI Order N13GaussianGlobalArithmetic.i =
      N13GaussianOrderTwo.i :=
  giToOrder_i
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
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.giAlgebraOrder
@[simp] theorem relativeToOrder_i :
    relativeToOrder relativeI =
      N13GaussianOrderTwo.i := by
  exact (relativeToOrderAlgHom.commutes
    N13GaussianGlobalArithmetic.i).trans
      algebraMap_gi_i
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
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL
@[simp] theorem globalReduction_relative
    (x : RelativeO) :
    globalReduction (relativeToRingOfIntegers x) =
      N13GaussianOrderTwo.reduction (relativeToOrder x) := by
  simp [globalReduction]
end
end MazurProof.N13GaussianGlobalReductionTwo
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL
@[simp] theorem globalReduction_zetaUnit :
    Units.map globalReduction.toMonoidHom zetaUnit =
      zetaJet := by
  apply Units.ext
  change
    globalReduction
        (relativeToRingOfIntegers relativeZeta) =
      (zetaJet : DualNumber F8)
  rw [globalReduction_relative]
  simp only [relativeZeta, relativeToOrder_i,
    reduction_i]
  ext <;>
    simp [N13LocalDlogRegimes.gaussianIDual,
      zetaJet, RamifiedDlog.unitOf_val]
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
@[simp] theorem globalReduction_e1Unit :
    Units.map globalReduction.toMonoidHom e1Unit =
      e1Jet := by
  apply Units.ext
  change
    globalReduction
        (relativeToRingOfIntegers relativeE1) =
      (e1Jet : DualNumber F8)
  rw [globalReduction_relative]
  have hmap :
      relativeToOrder relativeE1 =
        N13GaussianOrderTwo.e1Order := by
    simp [relativeE1, relativeZeta,
      N13GaussianOrderTwo.e1Order]
  rw [hmap, N13GaussianOrderTwo.reduction_e1Order]
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
@[simp] theorem globalReduction_e2Unit :
    Units.map globalReduction.toMonoidHom e2Unit =
      e2Jet := by
  apply Units.ext
  change
    globalReduction
        (relativeToRingOfIntegers relativeE2) =
      (e2Jet : DualNumber F8)
  rw [globalReduction_relative]
  have hmap :
      relativeToOrder relativeE2 =
        N13GaussianOrderTwo.e2Order := by
    have h2 :
        relativeToOrder (2 : RelativeO) =
          (2 : N13GaussianOrderTwo.Order) :=
      map_natCast relativeToOrder 2
    simp [relativeE2, relativeZeta,
      N13GaussianOrderTwo.e2Order, h2]
  rw [hmap, N13GaussianOrderTwo.reduction_e2Order]
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
@[simp] theorem globalDlogAdd_zeta :
    globalDlogAdd (Additive.ofMul zetaUnit) = 1 := by
  change
    RamifiedDlog.dlog
        (Units.map globalReduction.toMonoidHom zetaUnit) =
      1
  rw [globalReduction_zetaUnit]
  exact dlog_zeta
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
@[simp] theorem globalDlogAdd_e1 :
    globalDlogAdd (Additive.ofMul e1Unit) =
      N13LocalDlogTwo.alpha ^ 2 := by
  change
    RamifiedDlog.dlog
        (Units.map globalReduction.toMonoidHom e1Unit) =
      N13LocalDlogTwo.alpha ^ 2
  rw [globalReduction_e1Unit]
  exact dlog_e1
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
@[simp] theorem globalDlogAdd_e2 :
    globalDlogAdd (Additive.ofMul e2Unit) =
      N13LocalDlogTwo.alpha +
        N13LocalDlogTwo.alpha ^ 2 := by
  change
    RamifiedDlog.dlog
        (Units.map globalReduction.toMonoidHom e2Unit) =
      N13LocalDlogTwo.alpha +
        N13LocalDlogTwo.alpha ^ 2
  rw [globalReduction_e2Unit]
  exact dlog_e2
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

section
section
set_option autoImplicit false
open Finset Module
section
set_option autoImplicit false
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
/-- The logarithm of a named word, expanded in the structural power basis
`1, α, α²` of the residue field. -/
theorem globalDlogAdd_namedWord (c : Exp3) :
    globalDlogAdd (Additive.ofMul (namedWord c)) =
      (c.1 : F8) +
        (c.2.2 : F8) * N13LocalDlogTwo.alpha +
        (c.2.1 + c.2.2 : F2) *
          N13LocalDlogTwo.alpha ^ 2 := by
  simp [namedWord, ← Nat.cast_smul_eq_nsmul (R := F2),
    Algebra.smul_def]
  ring
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end
end
end

attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
theorem solution (c : MazurProof.N13GaussianNamedUnitSquareclasses.Exp3) :
    MazurProof.N13GaussianNamedUnitSquareclasses.globalDlogAdd (Additive.ofMul (MazurProof.N13GaussianNamedUnitSquareclasses.namedWord c)) =
      (c.1 : MazurProof.N13GaussianNamedUnitSquareclasses.F8) +
        (c.2.2 : MazurProof.N13GaussianNamedUnitSquareclasses.F8) * MazurProof.N13LocalDlogTwo.alpha +
        (c.2.1 + c.2.2 : MazurProof.N13GaussianNamedUnitSquareclasses.F2) *
          MazurProof.N13LocalDlogTwo.alpha ^ 2 := by
  exact MazurProof.N13GaussianNamedUnitSquareclasses.globalDlogAdd_namedWord c
