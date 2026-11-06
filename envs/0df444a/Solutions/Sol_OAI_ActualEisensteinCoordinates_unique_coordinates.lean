-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.unique_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:33:37.696227+00:00
-- url     : https://prove2.me/submissions/db6fc18d-41ea-418c-be2c-c31b4b921b30

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
namespace ShortDraftCusp
variable {R : Type*} [CommRing R]
end ShortDraftCusp
namespace ShortDraftConcretePhase
open ShortDraftTrace
end ShortDraftConcretePhase
namespace ShortDraftGauss
open Complex
open scoped ComplexConjugate
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftGauss
namespace EisensteinRayPhase
end EisensteinRayPhase
namespace ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]
end ShortDraftSextic
namespace ShortDraftGaussJacobi
open Finset
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftGaussJacobi
namespace ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftQuadraticGauss
namespace ShortDraftQuotientPhase
variable {A B : Type*} [CommGroup A] [CommGroup B]
end ShortDraftQuotientPhase
namespace EisensteinEPrimaryPhase
end EisensteinEPrimaryPhase
namespace ShortDraftGaussianPhaseTable
end ShortDraftGaussianPhaseTable
namespace ActualEisensteinCoordinates
private theorem eval_basis (a b : ℤ) :
    eval a b = a • pb.basis i0 + b • pb.basis i1 := by
  simp [eval, PowerBasis.basis_eq_pow, i0, i1, pb_gen, mul_comm]
end ActualEisensteinCoordinates
end
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinCoordinates
namespace OAI.ActualEisensteinCoordinates
theorem _root_.solution {a b c d : ℤ}
    (h : eval a b = eval c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun x : O => (pb.basis.repr x) i0) h
  have h1 := congrArg (fun x : O => (pb.basis.repr x) i1) h
  have hne : i0 ≠ i1 := by decide
  rw [eval_basis, eval_basis] at h0 h1
  constructor
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, if_pos, if_neg hne.symm,
      smul_eq_mul, mul_one, mul_zero, add_zero] using h0
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, if_pos, if_neg hne,
      smul_eq_mul, mul_one, mul_zero, zero_add] using h1
end OAI.ActualEisensteinCoordinates
