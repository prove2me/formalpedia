-- Prove2me | solution 1 for OAI.ContinuumCoulomb.QuantumHistorySourceProgram.routed_realization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:38:04.694841+00:00
-- url     : https://prove2.me/submissions/8ca37659-c421-4214-b30b-58abb2b630c0

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.UpperLower.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Order.Compact
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010
import Theorems.Thm_OAI_ContinuumCoulomb_QuantumPlanarTapeGeometry_final_realization

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFixedPauli
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_imaginary _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity Pauli traces evaluated entirely in rational registers.
The interpretation is the actual complex Pauli coefficient, not an
assumed list of Hamiltonian coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar Matrix
open scoped BigOperators Classical

theorem value_finiteProduct {α : Type} [Fintype α] (f : α → Scalar) :
    value (finiteProduct f) = ∏ a, value (f a) := by
  simp only [finiteProduct,value_product,enumerate,List.map_ofFn,List.prod_ofFn]
  exact (Fintype.equivFin α).symm.prod_comp (fun a => value (f a))

theorem value_pauli (μ : Fin 4) (a b : Fin 2) :
    value (pauli μ a b) = qmaPauli μ a b := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,qmaPauli,pauliX,pauliY,pauliZ]

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicHistory
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual ordered history cores have exact four-rational entries.  The
propagation Gram is formed on its at-most-five-site core; the construction
does not sum over spectator configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem value_identity {α : Type} [DecidableEq α] (s t : α) :
    value (identity s t) = (1 : Matrix α α ℂ) s t := by
  by_cases h : s = t <;> simp [identity,Matrix.one_apply,h]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedArmProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation and enumeration of the three buffered endpoint arms.
The lane color is unary, as required by the polynomial geometric size bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedArmProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

 theorem length_eq (colors : Fin 3 → ℕ) (a : Fin 3) :
    qmaBufferedArmLength colors (fun _ => false) a = length a (colors a) := by
  simp only [qmaBufferedArmLength,qmaBufferedPort,qmaBufferedOffset,Bool.false_eq_true,
    ite_false, if_false,length,qmaBufferedDoglegLength]
  split_ifs <;> omega

end ContinuumCoulomb.QuantumBufferedArmProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedSupport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.coarseRoute_last _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.coarseRoute_zero _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.exchangeGraph_energy _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_energy _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_qubit_index _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The routed paths visit original graph vertices only at their own endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem endpointArmSupport_vertex (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v w : Fin M.n) (e : M.Incident v)
    (hz : M.endpointArmSupport hd v e (M.placedVertex w)) : v = w := by
  obtain ⟨p,hp,hs⟩ := hz
  have hb := qmaBufferedFanout_bounded (M.endpointColors hd v)
    ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
    ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
    ((M.endpointPorts hd v).slot 2).isLt (fun _ => false) _ hs
  apply M.routeVertex_injective
  have hh := congrArg (fun z : ℕ × ℕ =>
    (z.1/(8*(9*B+3+6)),z.2/(8*(9*B+3+6)))) hp
  dsimp only [placedVertex] at hh
  rw [qmaBufferedCellPoint_cell (9*B+3) _ p hb.2.1 hb.2.2.2,
    qmaBufferedCellPoint_cell (9*B+3) _ (17,17) (by omega) (by omega)] at hh
  exact hh

theorem spacedSupport_not_vertex (e : M.Term) (v : Fin M.n) :
    ¬M.spacedSupport e (M.placedVertex v) := by
  intro h
  rcases h with ⟨h,_⟩ | ⟨h,_⟩
  all_goals
    have hm := congrArg (fun x : ℕ => x % 8) h
    simp [placedVertex,qmaBufferedCellPoint,qmaLanePoint,spacedColor,qmaSpacedLaneColor,
      Nat.add_mod,Nat.mul_mod] at hm

theorem bufferedPath_vertex (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (v : Fin M.n) (hz : M.placedVertex v ∈ (M.bufferedPath hd e).val.support) :
    v = M.left e ∨ v = M.right e := by
  rcases M.bufferedPath_support hd e hz with h | h | h
  · exact Or.inl (M.endpointArmSupport_vertex hd _ _ _ h).symm
  · exact (M.spacedSupport_not_vertex e v h).elim
  · exact Or.inr (M.endpointArmSupport_vertex hd _ _ _ h).symm

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedExtent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit rectangular bounds for every vertex and every buffered route. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaCellCoordinate_lt {W x X z : ℕ} (hx : x < X) (hz : z < W) :
    W*x+z < W*X := by
  calc
    W*x+z < W*x+W := Nat.add_lt_add_left hz _
    _ = W*(x+1) := by ring
    _ ≤ W*X := Nat.mul_le_mul_left W (by omega)

theorem qmaManhattanSupport_rectangle {p q z : ℕ × ℕ} {X Y : ℕ}
    (hp : p.1 < X ∧ p.2 < Y) (hq : q.1 < X ∧ q.2 < Y)
    (hz : qmaManhattanSupport p q z) : z.1 < X ∧ z.2 < Y := by
  rcases hz with ⟨hy,hx⟩ | ⟨hx,hy⟩ <;> unfold qmaBetween at * <;> omega

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem routeVertex_bounds (v : Fin M.n) :
    (M.routeVertex v).1 < (M.rows+1)*A ∧ (M.routeVertex v).2 < M.width+1 :=
  ⟨(M.qubitSlots.site v).1.isLt,(M.qubitSlots.site v).2.isLt⟩

theorem placedVertex_bounds (v : Fin M.n) :
    (M.placedVertex v).1 < M.bufferedWidth ∧ (M.placedVertex v).2 < M.bufferedHeight := by
  have hb := M.routeVertex_bounds v
  exact ⟨qmaCellCoordinate_lt hb.1 (by omega),qmaCellCoordinate_lt hb.2 (by omega)⟩

theorem endpointArmSupport_bounds (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {z : ℕ × ℕ} (hz : M.endpointArmSupport hd v e z) :
    z.1 < M.bufferedWidth ∧ z.2 < M.bufferedHeight := by
  obtain ⟨p,hp,hs⟩ := hz
  have hb := M.routeVertex_bounds v
  have hs' := qmaBufferedFanout_bounded (M.endpointColors hd v)
    ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
    ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
    ((M.endpointPorts hd v).slot 2).isLt (fun _ => false) _ hs
  rw [← hp]
  exact ⟨qmaCellCoordinate_lt hb.1 hs'.2.1,qmaCellCoordinate_lt hb.2 hs'.2.2.2⟩

theorem spacedSupport_bounds (e : M.Term) {z : ℕ × ℕ} (hz : M.spacedSupport e z) :
    z.1 < M.bufferedWidth ∧ z.2 < M.bufferedHeight := by
  have bound (v : Fin M.n) :
      (qmaLanePoint (M.spacedColor e) (M.routeVertex v)).1 < M.bufferedWidth ∧
        (qmaLanePoint (M.spacedColor e) (M.routeVertex v)).2 < M.bufferedHeight := by
    have hb := M.routeVertex_bounds v
    exact ⟨qmaCellCoordinate_lt hb.1 (M.spacedColor e).isLt,
      qmaCellCoordinate_lt hb.2 (M.spacedColor e).isLt⟩
  exact qmaManhattanSupport_rectangle (bound (M.left e)) (bound (M.right e)) hz

theorem bufferedPath_bounds (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) {z : ℕ × ℕ} (hz : z ∈ (M.bufferedPath hd e).val.support) :
    z.1 < M.bufferedWidth ∧ z.2 < M.bufferedHeight := by
  rcases M.bufferedPath_support hd e hz with h | h | h
  · exact M.endpointArmSupport_bounds hd _ _ h
  · exact M.spacedSupport_bounds e h
  · exact M.endpointArmSupport_bounds hd _ _ h

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkErasure
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coarse route's library loop erasure is the explicit right-to-left
finite-list algorithm. This identifies the actual path data needed by the
literal spatial compiler. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb
namespace QuantumWalkErasure
open ExactQuantumFactoring.BitStackProgram

variable {α : Type} [DecidableEq α]

variable {G : SimpleGraph α} {a b c : α}

private theorem support_dropUntil (p : G.Walk a b) (h : c ∈ p.support) :
    (p.dropUntil c h).support = p.support.drop (p.support.idxOf c) := by
  have hi := List.idxOf_lt_length_of_mem h
  have hs := p.length_support
  have hib : p.support.idxOf c ≤ p.length := by omega
  rw [SimpleGraph.Walk.dropUntil_eq_drop,SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,Nat.min_eq_left hib]

theorem support_bypass (p : G.Walk a b) : erase p.support = p.bypass.support := by
  induction p with
  | nil => simp [erase,step,SimpleGraph.Walk.bypass]
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.support_cons,erase_cons,ih]
    simp only [step,SimpleGraph.Walk.bypass]
    split_ifs with h
    · exact (support_dropUntil p.bypass h).symm
    · rfl

end QuantumWalkErasure

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem bufferedPath_support_explicit
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    (M.bufferedPath hd e).val.support =
      QuantumWalkErasure.erase (M.bufferedWalk hd e).support :=
  (QuantumWalkErasure.support_bypass (M.bufferedWalk hd e)).symm

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkSupport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_energy _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_qubit_index _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual buffered walk is a finite list of explicit arm and Manhattan
points. Loop erasure therefore computes the path used by the port geometry. -/

noncomputable section
namespace ContinuumCoulomb

 theorem qmaGridWalk_support_list (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) :
    (qmaGridWalk p L hstep).support = (List.range (L+1)).map p := by
  induction L generalizing p with
  | zero => simp [qmaGridWalk]
  | succ L ih =>
    simp only [qmaGridWalk,SimpleGraph.Walk.support_cons,ih,List.range_succ_eq_map,
      List.map_cons,List.map_map,Function.comp_def]

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

@[simp] theorem endpointArmWalk_support_eq (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    (M.endpointArmWalk hd v e).support = M.endpointArmList hd v e := by
  simp only [endpointArmWalk,SimpleGraph.Walk.support_copy,qmaGridWalk_support_list,
    endpointArmList]

@[simp] theorem spacedWalk_support_eq (e : M.Term) :
    (M.spacedWalk e).support = M.spacedList e := by
  simp only [spacedWalk,SimpleGraph.Walk.support_copy,qmaGridWalk_support_list,spacedList]

 theorem bufferedWalk_support_eq (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) : (M.bufferedWalk hd e).support = M.bufferedList hd e := by
  simp only [bufferedWalk,SimpleGraph.Walk.support_append,SimpleGraph.Walk.support_reverse,
    endpointArmWalk_support_eq,spacedWalk_support_eq,bufferedList]

 theorem bufferedPath_support_list (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) :
    (M.bufferedPath hd e).val.support = QuantumWalkErasure.erase (M.bufferedList hd e) := by
  rw [M.bufferedPath_support_explicit,M.bufferedWalk_support_eq]

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEndpointListProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint arm list is computed from its ordinal port, lane color and
coarse vertex. All three quantities are supplied by the explicit slot and
incident-rank programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEndpointListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem armList_fin (a : Fin 3) (color : ℕ) :
    armList (a.val,color) = (List.range (QuantumBufferedArmProgram.length a color+1)).map
      (QuantumBufferedArmProgram.point a color) := by
  fin_cases a <;> simp [armList]

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) (e : M.Incident v) :
    value B (M.routeVertex v,((M.endpointPorts hd v).assign e).val,(M.laneColor e.val).val) =
      M.endpointArmList hd v e := by
  unfold value
  rw [armList_fin,List.map_map]
  rw [← M.endpointColors_assigned hd v e]
  simp only [QMASpatialExchangeModel.endpointArmList,QMASpatialExchangeModel.endpointArmLength,
    QuantumBufferedArmProgram.length_eq,translate,Function.comp_def]
  rfl

end ContinuumCoulomb.QuantumEndpointListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumManhattanListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate the Manhattan segment with an explicit fixed route budget.
The cap makes enumeration polynomial on every input, and disappears for
the spatial routes satisfying the proved length bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumManhattanListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem value_exact (K : ℕ) (x : Ends) (h : qmaManhattanLength x.1 x.2 ≤ K) :
    value K x = (List.range (qmaManhattanLength x.1 x.2+1)).map (qmaManhattanPoint x.1 x.2) := by
  simp only [value,Nat.min_eq_right h]

end ContinuumCoulomb.QuantumManhattanListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpacedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate the bounded Manhattan portion of each actual buffered route.
The horizontal and vertical translations are literal binary arithmetic. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpacedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem point_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) (e : M.Term) (p : Pair) :
    point B (M.laneColor e).val p = qmaLanePoint (M.spacedColor e) p := rfl

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) (e : M.Term) :
    value A B ((M.laneColor e).val,M.routeVertex (M.left e),M.routeVertex (M.right e)) =
      M.spacedList e := by
  unfold value
  rw [point_actual,point_actual,QuantumManhattanListProgram.value_exact]
  · rfl
  · exact M.spaced_length e

end ContinuumCoulomb.QuantumSpacedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal construction and loop erasure of the complete buffered route.
The input consists of two computed fine-grid endpoints, one lane color and
the two computed incident port ranks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    value A B (actualInput M hd e) = M.bufferedList hd e := by
  unfold value actualInput
  rw [QuantumEndpointListProgram.value_actual,QuantumSpacedListProgram.value_actual,
    QuantumEndpointListProgram.value_actual]
  rfl

theorem path_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    path A B (actualInput M hd e) = (M.bufferedPath hd e).val.support := by
  rw [path,value_actual,M.bufferedPath_support_list]

end ContinuumCoulomb.QuantumBufferedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedSourceCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original spin cells contain no internal route passage. Their local connections
are precisely the vertex fanout rays, separated from crossing cells. -/

noncomputable section
namespace ContinuumCoulomb
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem coarseRoute_avoids (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (i : ℕ) (v : Fin M.n) (hi0 : 0 < i) (hi : i < M.coarseLength hd e) :
    M.coarseRoute hd e i ≠ M.placedVertex v := by
  intro h
  have hm := (M.bufferedPath hd e).val.getVert_mem_support i
  change M.coarseRoute hd e i ∈ _ at hm
  rw [h] at hm
  rcases M.bufferedPath_vertex hd e v hm with hv | hv
  · rw [hv] at h
    have he := M.coarseRoute_simple hd e i 0 hi.le (Nat.zero_le _)
      (h.trans (M.coarseRoute_zero hd e).symm)
    omega
  · rw [hv] at h
    have he := M.coarseRoute_simple hd e i (M.coarseLength hd e) hi.le le_rfl
      (h.trans (M.coarseRoute_last hd e).symm)
    omega

theorem sourceCell_no_passage (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (i : (M.portRouteData hA hd).Interior) (v : Fin M.n) :
    (M.portRouteData hA hd).cell i ≠ M.placedVertex v := by
  apply M.coarseRoute_avoids hd i.1 (i.2.val+1) v (by omega)
  exact (M.portRouteData hA hd).cell_index_lt i

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectionUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint physical terminal sets make crossing-edge assignment unique.
Consequently the finite endpoint test computes the canonical selection. -/

noncomputable section
namespace ContinuumCoulomb.QMARationalExchangeGraph
open scoped Classical

private theorem crossingMatch_left_parity (G : QMARationalExchangeGraph) {r : ℕ}
    (site : Fin r → Fin 4 → Fin G.n) (e : G.Edge) (p : Fin r × Fin 2)
    (h : G.CrossingMatch site e p) :
    ∃ k : Fin 4, site p.1 k=G.left e ∧ k.val%2=p.2.val := by
  rcases p with ⟨i,a⟩
  fin_cases a
  · rcases h with ⟨hl,_⟩ | ⟨hl,_⟩
    · exact ⟨0,hl.symm,rfl⟩
    · exact ⟨2,hl.symm,rfl⟩
  · rcases h with ⟨hl,_⟩ | ⟨hl,_⟩
    · exact ⟨1,hl.symm,rfl⟩
    · exact ⟨3,hl.symm,rfl⟩

theorem crossingMatch_unique (G : QMARationalExchangeGraph) {r : ℕ}
    (site : Fin r → Fin 4 → Fin G.n)
    (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
    {e : G.Edge} {p q : Fin r × Fin 2}
    (hp : G.CrossingMatch site e p) (hq : G.CrossingMatch site e q) : p=q := by
  obtain ⟨a,ha,hpa⟩ := crossingMatch_left_parity G site e p hp
  obtain ⟨b,hb,hqb⟩ := crossingMatch_left_parity G site e q hq
  have hi : (p.1,a)=(q.1,b) := hinj (ha.trans hb.symm)
  have hab : a=b := congrArg Prod.snd hi
  have hindex : p.1=q.1 := congrArg (fun z : Fin r × Fin 4 => z.1) hi
  refine Prod.ext hindex (Fin.ext ?_)
  rw [← hpa,← hqb,hab]

theorem crossingTag_some_iff (G : QMARationalExchangeGraph) {r : ℕ}
    (site : Fin r → Fin 4 → Fin G.n)
    (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
    (e : G.Edge) (p : Fin r × Fin 2) :
    G.crossingTag site e=some p ↔ G.CrossingMatch site e p := by
  constructor
  · exact G.crossingTag_some site
  · intro hp
    cases ht : G.crossingTag site e with
    | none => exact ((G.crossingTag_none site).mp ht p hp).elim
    | some q =>
      have hq := G.crossingTag_some site ht
      have hqp := G.crossingMatch_unique site hinj hq hp
      exact congrArg some hqp

end ContinuumCoulomb.QMARationalExchangeGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectionRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A relabeling of the old graph and the crossing cells preserves exactly
which edges are retained by the physical crossing selection. -/

noncomputable section
namespace ContinuumCoulomb.QMARationalExchangeGraph
open scoped Classical

variable {G H : QMARationalExchangeGraph} {r t : ℕ}
    (vertex : Fin G.n ≃ Fin H.n) (edge : G.Edge ≃ H.Edge)
    (left : ∀ e, vertex (G.left e)=H.left (edge e))
    (right : ∀ e, vertex (G.right e)=H.right (edge e))
    (s : Fin r → Fin 4 → Fin G.n) (u : Fin t → Fin 4 → Fin H.n)
    (cell : Fin r ≃ Fin t) (site : ∀ i a, vertex (s i a)=u (cell i) a)

include left right site in
theorem crossingMatch_relabel (e : G.Edge) (i : Fin r) (a : Fin 2) :
    G.CrossingMatch s e (i,a) ↔ H.CrossingMatch u (edge e) (cell i,a) := by
  have hl (b : Fin 4) : G.left e=s i b ↔ H.left (edge e)=u (cell i) b := by
    rw [← left e,← site i b]
    exact vertex.injective.eq_iff.symm
  have hr (b : Fin 4) : G.right e=s i b ↔ H.right (edge e)=u (cell i) b := by
    rw [← right e,← site i b]
    exact vertex.injective.eq_iff.symm
  simp only [CrossingMatch,hl,hr]

include left right site in
theorem crossingTag_none_relabel (e : G.Edge) :
    G.crossingTag s e=none ↔ H.crossingTag u (edge e)=none := by
  rw [G.crossingTag_none,H.crossingTag_none]
  constructor
  · intro h ⟨i,a⟩ hp
    apply h (cell.symm i,a)
    apply (crossingMatch_relabel vertex edge left right s u cell site e _ a).mpr
    simpa only [Equiv.apply_symm_apply] using hp
  · intro h ⟨i,a⟩ hp
    exact h (cell i,a) ((crossingMatch_relabel vertex edge left right s u cell site e i a).mp hp)

variable (hs : ∀ i, Function.Injective (s i)) (hu : ∀ i, Function.Injective (u i))

include left right site in
theorem retained_source (e : (G.crossingSelection s hs).retained.Edge) :
    ∃ f : (H.crossingSelection u hu).retained.Edge,
      vertex (G.left e.val)=H.left f.val ∧ vertex (G.right e.val)=H.right f.val := by
  refine ⟨⟨edge e.val,(crossingTag_none_relabel vertex edge left right s u cell site e.val).mp
    e.property⟩,left e.val,right e.val⟩

include left right site in
theorem retained_target (f : (H.crossingSelection u hu).retained.Edge) :
    ∃ e : (G.crossingSelection s hs).retained.Edge,
      vertex (G.left e.val)=H.left f.val ∧ vertex (G.right e.val)=H.right f.val := by
  have ht : G.crossingTag s (edge.symm f.val)=none :=
    (crossingTag_none_relabel vertex edge left right s u cell site (edge.symm f.val)).mpr
      (by rw [Equiv.apply_symm_apply]; exact f.property)
  refine ⟨⟨edge.symm f.val,ht⟩,?_,?_⟩
  · simpa only [Equiv.apply_symm_apply] using left (edge.symm f.val)
  · simpa only [Equiv.apply_symm_apply] using right (edge.symm f.val)

end ContinuumCoulomb.QMARationalExchangeGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSupportRelabel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathSchedule.mem_active _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A crossing layer preserves unordered edge support under relabeling of
the old vertices and crossing cells. Couplings do not enter this statement. -/

noncomputable section
namespace ContinuumCoulomb.QMARationalCrossingLayer
open MediatorGraph
open scoped Classical

variable {r s : ℕ} (C : QMARationalCrossingLayer r) (E : QMARationalCrossingLayer s)
    (vertex : Fin C.base.n ≃ Fin E.base.n) (cell : Fin r ≃ Fin s)

theorem vertexRelabel_old (v : Fin C.base.n) :
    C.vertexRelabel E vertex cell (old C.base.n r v) = old E.base.n s (vertex v) := by
  simp [vertexRelabel,old]

theorem vertexRelabel_fresh (i : Fin r) (a : Fin 2) :
    C.vertexRelabel E vertex cell (fresh C.base.n r i a) =
      fresh E.base.n s (cell i) a := by
  simp [vertexRelabel,fresh]

variable
    (site : ∀ i a, vertex (C.site i a) = E.site (cell i) a)
    (forward : ∀ e : C.base.Edge, ∃ f : E.base.Edge,
      s(vertex (C.base.left e),vertex (C.base.right e)) = s(E.base.left f,E.base.right f))
    (backward : ∀ f : E.base.Edge, ∃ e : C.base.Edge,
      s(vertex (C.base.left e),vertex (C.base.right e)) = s(E.base.left f,E.base.right f))

include site forward in
theorem output_edge_source (N M : ℚ) (e : (C.output N).Edge) :
    ∃ f : (E.output M).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f) := by
  rcases e with (e | ⟨i,a⟩) | (i | ⟨i,a⟩)
  · obtain ⟨f,hf⟩ := forward e
    refine ⟨.inl (.inl f),?_⟩
    simpa only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,Sum.elim_inl,vertexRelabel_old,
      Sym2.map_mk] using congrArg (Sym2.map (old E.base.n s)) hf
  · refine ⟨.inl (.inr (cell i,a)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,Sum.elim_inr,vertexRelabel_old,site]
  · refine ⟨.inr (.inl (cell i)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,vertexRelabel_fresh]
  · refine ⟨.inr (.inr (cell i,a)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      vertexRelabel_old,vertexRelabel_fresh,site]

include site backward in
theorem output_edge_target (N M : ℚ) (f : (E.output M).Edge) :
    ∃ e : (C.output N).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f) := by
  rcases f with (f | ⟨j,a⟩) | (j | ⟨j,a⟩)
  · obtain ⟨e,he⟩ := backward f
    refine ⟨.inl (.inl e),?_⟩
    simpa only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,Sum.elim_inl,vertexRelabel_old,
      Sym2.map_mk] using congrArg (Sym2.map (old E.base.n s)) he
  · refine ⟨.inl (.inr (cell.symm j,a)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,Sum.elim_inr,vertexRelabel_old,site,
      Equiv.apply_symm_apply]
  · refine ⟨.inr (.inl (cell.symm j)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,vertexRelabel_fresh,
      Equiv.apply_symm_apply]
  · refine ⟨.inr (.inr (cell.symm j,a)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      vertexRelabel_old,vertexRelabel_fresh,site,Equiv.apply_symm_apply]

include site forward backward in
theorem output_support (N M : ℚ) :
    (∀ e : (C.output N).Edge, ∃ f : (E.output M).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f)) ∧
    (∀ f : (E.output M).Edge, ∃ e : (C.output N).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f)) :=
  ⟨C.output_edge_source E vertex cell site forward N M,
    C.output_edge_target E vertex cell site backward N M⟩

end ContinuumCoulomb.QMARationalCrossingLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingScaleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational scale for a simultaneous crossing layer, computed from
its retained coefficients and the two crossing coefficients at each cell. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingScaleProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

theorem value_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : value (actualInput C N labels)=C.scale N := by
  simp only [value,base,active,correction,actualInput,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,linearCost,squareCost,QMARationalCrossingLayer.scale]
  rw [labels.symm.sum_comp (fun e => |C.base.weight e|)]

end ContinuumCoulomb.QuantumCrossingScaleProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal crossing packet has exactly the sites, scale and scalar
shift of the rational crossing layer used by the spectral comparison. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock
open scoped BigOperators Classical

theorem scaleInput_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    scaleInput (actualInput C N labels)=QuantumCrossingScaleProgram.actualInput C N labels := by
  simp only [scaleInput,actualInput,QuantumListGraph.packed,List.map_ofFn]
  rfl

theorem parameters_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    parameters (actualInput C N labels)=(C.base.n,C.scale N) := by
  unfold parameters
  rw [scaleInput_actual,QuantumCrossingScaleProgram.value_actual]
  rfl

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathSchedule.mem_active _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-space matrix semantics for the computed crossing packet.
The nine serialized bonds are the nine physical edges of each crossing. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock MediatorGraph
open scoped BigOperators Classical

private theorem fresh_value (n r : ℕ) (i : Fin r) (a : Fin 2) :
    (fresh n r i a).val=n+2*i.val+a.val := by
  change n+(a.val+2*i.val)=_
  omega

private theorem old_value (n r : ℕ) (i : Fin n) : (old n r i).val=i.val := rfl

theorem bond_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    (i : Fin r) (k : Fin 9) :
    bond ((C.base.n,C.scale N),i.val,actualCrossing C i) k =
      (((C.output N).left (edgeTag C N i k)).val,
        ((C.output N).right (edgeTag C N i k)).val,
        (C.output N).weight (edgeTag C N i k)) := by
  fin_cases k <;>
    simp [bond,left,right,coefficient,base,actualCrossing,site,edgeTag,
      QMARationalCrossingLayer.output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,qmaCrossingLeft,qmaCrossingRight,
      qmaCrossingMember,fresh_value,old_value]

private theorem indexed_ofFn {r : ℕ} (p : Parameters) (f : Fin r → Crossing)
    (i : Fin r) : indexed (i.val,(p,List.ofFn f))=(p,i.val,f i) := by
  unfold indexed
  rw [List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn,Option.getD_some]

theorem family_ofFn {r : ℕ} (p : Parameters) (f : Fin r → Crossing) :
    family (p,List.ofFn f)=(List.ofFn fun i => block (p,i.val,f i)).flatten := by
  have hr (g : ℕ → List MediatorListProgram.Bond) :
      (List.range r).map g=List.ofFn (fun i : Fin r => g i.val) := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem_eq_map (List.range r) g).symm
  unfold family
  rw [List.length_ofFn,hr]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin r → List MediatorListProgram.Bond => List.ofFn g)
  funext i
  rw [indexed_ofFn]

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite endpoint scans recover the actual selected rational couplings.
No matrix or energy comparison is assumed by this source-data bridge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped BigOperators Classical

theorem terminalPair_encoded {n r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (i : Fin r) (a : Fin 2) :
    terminalPair a (encodedSites site i)=
      ((site i (if a=0 then 0 else 1)).val,(site i (if a=0 then 2 else 3)).val) := by
  fin_cases a <;> rfl

theorem hits_selected {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    (e : G.Edge) (i : Fin r) (a : Fin 2) :
    hits (((G.left e).val,(G.right e).val,G.weight e),terminalPair a (encodedSites S.site i)) =
      decide (S.tag e=some (i,a)) := by
  apply Bool.eq_iff_iff.mpr
  rw [hits_iff,decide_eq_true_eq,htag,terminalPair_encoded]
  simp only [QMARationalExchangeGraph.CrossingMatch,Prod.mk.injEq,Fin.ext_iff]
  tauto

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingRetention
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathSchedule.mem_active _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact retained-edge semantics of the finite crossing scan. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped BigOperators Classical

theorem pairs_ofFn_mem {r : ℕ} (ss : Fin r → Sites) (p : QuantumRouteCode.Pair) :
    p ∈ pairs (List.ofFn ss) ↔ ∃ i a, terminalPair a (ss i)=p := by
  rw [pairs,List.map_ofFn]
  constructor
  · intro h
    obtain ⟨xs,hxs,hp⟩ := List.mem_flatten.mp h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hxs
    rcases List.mem_cons.mp hp with hp | hp
    · exact ⟨i,0,hp.symm⟩
    · exact ⟨i,1,(List.mem_singleton.mp hp).symm⟩
  · rintro ⟨i,a,rfl⟩
    apply List.mem_flatten.mpr
    refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    fin_cases a <;> simp

theorem keep_selected {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    (e : G.Edge) :
    keep (pairs (List.ofFn (encodedSites S.site)),
      ((G.left e).val,(G.right e).val,G.weight e))=decide (S.tag e=none) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change (!(pairs (List.ofFn (encodedSites S.site))).any
    (fun p => hits (((G.left e).val,(G.right e).val,G.weight e),p)))=true ↔ _
  rw [Bool.not_eq_true_eq_eq_false,List.any_eq_false]
  constructor
  · intro h
    cases ht : S.tag e with
    | none => rfl
    | some p =>
      have hm := (pairs_ofFn_mem (encodedSites S.site)
        (terminalPair p.2 (encodedSites S.site p.1))).mpr ⟨p.1,p.2,rfl⟩
      have hn := h _ hm
      rw [hits_selected S htag,ht] at hn
      exact (hn (by simp)).elim
  · intro ht p hp
    obtain ⟨i,a,rfl⟩ := (pairs_ofFn_mem (encodedSites S.site) p).mp hp
    rw [hits_selected S htag,ht]
    simp

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingCompiled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space correctness of the computed crossing transformation, starting
from an ordinary finite bond tape and its selected physical terminals. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped Classical

variable {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r) {m : ℕ} (labels : G.Edge ≃ Fin m)

private theorem packed_ofBonds (n : ℕ) (xs : List MediatorListProgram.Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1) :
    QuantumListGraph.packed (QuantumListGraph.ofBonds n xs c hb hn) (Equiv.refl _)=xs := by
  change List.ofFn (fun i : Fin xs.length => xs.get i)=xs
  exact List.ofFn_get xs

theorem compiled_packet (N : ℚ) :
    value (N,(G.n,QuantumListGraph.packed G labels,G.constant),
      List.ofFn (encodedSites S.site)) =
      QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact (packed_ofBonds G.n
            (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels))
            G.constant (retained_bounded _ _ (QuantumListGraph.packed_bounded G labels))
            (retained_noLoops _ _ (QuantumListGraph.packed_noLoops G labels))).symm
        · rfl
  · simp only [value,crossings,QuantumCrossingListLayer.actualInput,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rfl

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRetainedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtering the bond tape retains exactly the unselected physical edges,
including their orientation, regardless of their list order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped Classical

variable {G : QMARationalExchangeGraph} {r m : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin m)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))

include htag in
theorem retained_edge_source (e : (retainedGraph S labels).Edge) :
    ∃ f : S.retained.Edge,
      (retainedGraph S labels).left e = S.retained.left f ∧
      (retainedGraph S labels).right e = S.retained.right f := by
  let xs := retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels)
  have hm : xs.get e ∈ xs := List.get_mem xs e
  obtain ⟨hm,hk⟩ := List.mem_filter.mp hm
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  have ht : S.tag (labels.symm i)=none := by
    rw [← hi] at hk
    exact of_decide_eq_true ((keep_selected S htag (labels.symm i)).symm.trans hk)
  refine ⟨⟨labels.symm i,ht⟩,?_,?_⟩
  · apply Fin.ext
    change (xs.get e).1=(G.left (labels.symm i)).val
    rw [← hi]
  · apply Fin.ext
    change (xs.get e).2.1=(G.right (labels.symm i)).val
    rw [← hi]

include htag in
theorem retained_edge_target (f : S.retained.Edge) :
    ∃ e : (retainedGraph S labels).Edge,
      (retainedGraph S labels).left e = S.retained.left f ∧
      (retainedGraph S labels).right e = S.retained.right f := by
  let b : MediatorListProgram.Bond := ((G.left f.val).val,(G.right f.val).val,G.weight f.val)
  let xs := retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels)
  have hm : b ∈ xs := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_ofFn.mpr ⟨labels f.val,?_⟩,?_⟩
    · simp only [Equiv.symm_apply_apply]
      rfl
    · exact (keep_selected S htag f.val).trans (decide_eq_true f.property)
  obtain ⟨e,he⟩ := List.mem_iff_get.mp hm
  refine ⟨e,?_,?_⟩
  · apply Fin.ext
    change (xs.get e).1=(G.left f.val).val
    rw [he]
  · apply Fin.ext
    change (xs.get e).2.1=(G.right f.val).val
    rw [he]

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumComputedCrossingRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed retained-edge scan and the canonical crossing layer have
the same physical edges after the old spins and crossing cells are relabeled. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open scoped Classical

variable {G H : QMARationalExchangeGraph} {r t m : ℕ}
    (vertex : Fin G.n ≃ Fin H.n) (edge : G.Edge ≃ H.Edge)
    (left : ∀ e, vertex (G.left e)=H.left (edge e))
    (right : ∀ e, vertex (G.right e)=H.right (edge e))
    (s : Fin r → Fin 4 → Fin G.n) (u : Fin t → Fin 4 → Fin H.n)
    (cell : Fin r ≃ Fin t) (site : ∀ i a, vertex (s i a)=u (cell i) a)
    (hs : ∀ i, Function.Injective (s i)) (hu : ∀ i, Function.Injective (u i))
    (hglobal : Function.Injective (fun p : Fin r × Fin 4 => s p.1 p.2))
    (labels : G.Edge ≃ Fin m)

include left right site hglobal in
theorem computed_base_source
    (e : (computedLayer (G.crossingSelection s hs) labels).base.Edge) :
    ∃ f : (H.crossingSelection u hu).layer.base.Edge,
      vertex ((computedLayer (G.crossingSelection s hs) labels).base.left e) =
        (H.crossingSelection u hu).layer.base.left f ∧
      vertex ((computedLayer (G.crossingSelection s hs) labels).base.right e) =
        (H.crossingSelection u hu).layer.base.right f := by
  have ht := fun e i a => G.crossingTag_some_iff s hglobal e (i,a)
  obtain ⟨k,hk1,hk2⟩ := retained_edge_source (G.crossingSelection s hs) labels ht e
  obtain ⟨f,hf1,hf2⟩ := QMARationalExchangeGraph.retained_source vertex edge left right s u cell site hs hu k
  exact ⟨f,(congrArg vertex hk1).trans hf1,(congrArg vertex hk2).trans hf2⟩

include left right site hglobal in
theorem computed_base_target (f : (H.crossingSelection u hu).layer.base.Edge) :
    ∃ e : (computedLayer (G.crossingSelection s hs) labels).base.Edge,
      vertex ((computedLayer (G.crossingSelection s hs) labels).base.left e) =
        (H.crossingSelection u hu).layer.base.left f ∧
      vertex ((computedLayer (G.crossingSelection s hs) labels).base.right e) =
        (H.crossingSelection u hu).layer.base.right f := by
  have ht := fun e i a => G.crossingTag_some_iff s hglobal e (i,a)
  obtain ⟨k,hk1,hk2⟩ := QMARationalExchangeGraph.retained_target vertex edge left right s u cell site hs hu f
  obtain ⟨e,he1,he2⟩ := retained_edge_target (G.crossingSelection s hs) labels ht k
  exact ⟨e,(congrArg vertex he1).trans hk1,(congrArg vertex he2).trans hk2⟩

include left right site hglobal in
theorem computed_output_support (N M : ℚ) :
    let C := computedLayer (G.crossingSelection s hs) labels
    let E := (H.crossingSelection u hu).layer
    (∀ e : (C.output N).Edge, ∃ f : (E.output M).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f)) ∧
    (∀ f : (E.output M).Edge, ∃ e : (C.output N).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f)) := by
  let C := computedLayer (G.crossingSelection s hs) labels
  let E := (H.crossingSelection u hu).layer
  apply C.output_support E vertex cell site
  · intro e
    obtain ⟨f,h1,h2⟩ := computed_base_source vertex edge left right s u cell site hs hu hglobal labels e
    exact ⟨f,congrArg₂ (fun a b : Fin H.n => s(a,b)) h1 h2⟩
  · intro f
    obtain ⟨e,h1,h2⟩ := computed_base_target vertex edge left right s u cell site hs hu hglobal labels f
    exact ⟨e,congrArg₂ (fun a b : Fin H.n => s(a,b)) h1 h2⟩

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal nine-bond crossing block has precisely the unordered
endpoint support of the physical crossing graph. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock
open scoped Classical

variable {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)

theorem edge_base_or_tag (e : (C.output N).Edge) :
    (∃ a : C.base.Edge, e = Sum.inl (Sum.inl a)) ∨
      ∃ i k, e = edgeTag C N i k := by
  rcases e with (a | ⟨i,k⟩) | (i | ⟨i,k⟩)
  · exact Or.inl ⟨a,rfl⟩
  · right
    fin_cases k
    · exact ⟨i,0,rfl⟩
    · exact ⟨i,1,rfl⟩
    · exact ⟨i,2,rfl⟩
    · exact ⟨i,3,rfl⟩
  · exact Or.inr ⟨i,4,rfl⟩
  · right
    fin_cases k
    · exact ⟨i,5,rfl⟩
    · exact ⟨i,6,rfl⟩
    · exact ⟨i,7,rfl⟩
    · exact ⟨i,8,rfl⟩

theorem bond_support_actual {m : ℕ} (labels : C.base.Edge ≃ Fin m)
    (p : Sym2 ℕ) :
    (∃ b ∈ bonds (actualInput C N labels), s(b.1,b.2.1) = p) ↔
      ∃ e : (C.output N).Edge,
        s(((C.output N).left e).val,((C.output N).right e).val) = p := by
  have hb (a : C.base.Edge) :
      s(((C.output N).left (Sum.inl (Sum.inl a))).val,
        ((C.output N).right (Sum.inl (Sum.inl a))).val) =
        s((C.base.left a).val,(C.base.right a).val) := rfl
  have hmem (i : Fin r) (k : Fin 9) :
      bond ((C.base.n,C.scale N),i.val,actualCrossing C i) k ∈
        family ((C.base.n,C.scale N),List.ofFn (actualCrossing C)) := by
    rw [family_ofFn]
    exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
      List.mem_ofFn.mpr ⟨k,rfl⟩⟩
  change (∃ b ∈ QuantumListGraph.packed C.base labels ++
    family (parameters (actualInput C N labels),List.ofFn (actualCrossing C)),
      s(b.1,b.2.1)=p) ↔ _
  rw [parameters_actual]
  constructor
  · rintro ⟨b,hbonds,hp⟩
    rcases List.mem_append.mp hbonds with ho | hf
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ho
      exact ⟨Sum.inl (Sum.inl (labels.symm i)),(hb _).trans hp⟩
    · rw [family_ofFn] at hf
      obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hf
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hbs
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb
      exact ⟨edgeTag C N i k,by simpa only [bond_actual] using hp⟩
  · rintro ⟨e,he⟩
    rcases edge_base_or_tag C N e with ⟨a,rfl⟩ | ⟨i,k,rfl⟩
    · refine ⟨((C.base.left a).val,(C.base.right a).val,C.base.weight a),
        List.mem_append_left _ (List.mem_ofFn.mpr ⟨labels a,?_⟩),?_⟩
      · simp only [Equiv.symm_apply_apply]
      · exact (hb a).symm.trans he
    · exact ⟨_,List.mem_append_right _ (hmem i k),by simpa only [bond_actual] using he⟩

private theorem fin_pair {n : ℕ} {a b c d : Fin n}
    (h : s(a.val,b.val)=s(c.val,d.val)) : s(a,b)=s(c,d) := by
  rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext h1,Fin.ext h2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext h1,Fin.ext h2⟩)

theorem actual_support_source {m : ℕ} (labels : C.base.Edge ≃ Fin m)
    (e : (actualGraph C N labels).Edge) :
    ∃ f : (C.output N).Edge,
      s(actualVertex C N labels ((actualGraph C N labels).left e),
        actualVertex C N labels ((actualGraph C N labels).right e)) =
          s((C.output N).left f,(C.output N).right f) := by
  let xs := bonds (actualInput C N labels)
  obtain ⟨f,hf⟩ := (bond_support_actual C N labels
    s(((xs.get e).1),((xs.get e).2.1))).mp ⟨xs.get e,List.get_mem xs e,rfl⟩
  refine ⟨f,fin_pair ?_⟩
  exact hf.symm

theorem actual_support_target {m : ℕ} (labels : C.base.Edge ≃ Fin m)
    (f : (C.output N).Edge) :
    ∃ e : (actualGraph C N labels).Edge,
      s(actualVertex C N labels ((actualGraph C N labels).left e),
        actualVertex C N labels ((actualGraph C N labels).right e)) =
          s((C.output N).left f,(C.output N).right f) := by
  obtain ⟨b,hb,hp⟩ := (bond_support_actual C N labels
    s(((C.output N).left f).val,((C.output N).right f).val)).mpr ⟨f,rfl⟩
  obtain ⟨e,he⟩ := List.mem_iff_get.mp hb
  refine ⟨e,fin_pair ?_⟩
  change s(((bonds (actualInput C N labels)).get e).1,
    ((bonds (actualInput C N labels)).get e).2.1) = _
  rw [he]
  exact hp

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingTableCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite table is the data of the actual port routes. Its membership
tests agree exactly with the permissions used in the geometric proof. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open QuantumRoutingTable
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem routingTable_crossing (p : ℕ × ℕ) :
    p ∈ P.routingTable.2.2 ↔ P.IsCrossing p := by
  exact Finset.mem_toList.trans P.mem_crossingCells

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPositionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal physical coordinates after crossing removal. Only ports in the
computed crossing cells move; the two fresh spins use fixed local coordinates. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPositionProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open scoped Classical

theorem move_eq {cs : List Pair} {cross : Pair → Prop} [DecidablePred cross]
    (hc : ∀ p, p ∈ cs ↔ cross p) (z : Pair) :
    move (cs,z)=qmaCrossingMove cross z := by
  simp only [move,qmaCrossingMove,hc]

theorem moved_ofFn {cs : List Pair} {cross : Pair → Prop} [DecidablePred cross]
    (hc : ∀ p, p ∈ cs ↔ cross p) {n : ℕ} (pos : Fin n → Pair) :
    moved (cs,List.ofFn pos)=List.ofFn (fun v => qmaCrossingMove cross (pos v)) := by
  simp only [moved,List.map_ofFn,Function.comp_def,move_eq hc]

end ContinuumCoulomb.QuantumCrossingPositionProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPositionRelabel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reordering the port vertices or crossing cells reorders the output
positions by a finite equivalence, preserving their injectivity. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPositionProgram
open MediatorGraph QuantumRouteCode
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) (D : ℕ) {n r : ℕ}
    (σ : Fin n ≃ Fin (P.finishedGraph N D).n)
    (τ : Fin r ≃ Fin P.crossingCells.card)

theorem extend_old (v : Fin n) : extend P N D σ τ (old n r v)=old _ _ (σ v) := by
  simp [extend,old]

theorem extend_fresh (i : Fin r) (a : Fin 2) :
    extend P N D σ τ (MediatorGraph.fresh n r i a)=MediatorGraph.fresh _ _ (τ i) a := by
  simp [extend,MediatorGraph.fresh]

theorem reordered_cells_mem (p : Pair) :
    p ∈ List.ofFn (fun i => (P.crossingCell (τ i)).val) ↔ P.IsCrossing p := by
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩
    exact P.mem_crossingCells.mp (P.crossingCell (τ i)).property
  · intro hp
    let c : P.Crossing := ⟨p,P.mem_crossingCells.mpr hp⟩
    refine ⟨τ.symm (P.crossingCells.equivFin c),?_⟩
    simp only [Equiv.apply_symm_apply,QMAPortRouteData.crossingCell,
      Equiv.symm_apply_apply]
    rfl

theorem positions_reordered :
    positions (List.ofFn (fun i => (P.crossingCell (τ i)).val),
      List.ofFn (fun v => P.finishedPosition N D (σ v))) =
      List.ofFn (fun v => P.crossingPosition N D (extend P N D σ τ v)) := by
  rw [positions,moved_ofFn (reordered_cells_mem P τ)]
  rw [List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · apply congrArg List.ofFn
    funext v
    change qmaCrossingMove P.IsCrossing (P.finishedPosition N D (σ v))=
      P.crossingPosition N D (extend P N D σ τ (old n r v))
    rw [extend_old,P.crossingPosition_old]
    rfl
  · rw [fresh,List.map_ofFn,List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    have hf (a : Fin 2) :
        P.crossingPosition N D (extend P N D σ τ
          ((⟨i.val*2+a.val,by omega⟩ : Fin (r*2)).natAdd n)) =
          qmaGadgetAncilla (P.crossingCell (τ i)).val a := by
      have he : ((⟨i.val*2+a.val,by omega⟩ : Fin (r*2)).natAdd n)=MediatorGraph.fresh n r i a := by
        apply Fin.ext
        change n+(i.val*2+a.val)=n+(a.val+2*i.val)
        omega
      rw [he,extend_fresh,P.crossingPosition_fresh]
      rfl
    simp only [hf,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one]
    rfl

end ContinuumCoulomb.QuantumCrossingPositionProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSiteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locate crossing terminals by scanning the actual physical position tape.
The finite search returns exactly the existing terminal spin indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSiteProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumCrossingListBlock
open scoped Classical

theorem index_eq (x : Input) : index x=x.1.findIdx (fun p => decide (p=x.2)) := by
  rw [index,QuantumFirstUseProgram.first_eq_findIdx,flags,List.findIdx_map]
  rfl

theorem index_ofFn {n : ℕ} (pos : Fin n → Pair) (hinj : Function.Injective pos) (v : Fin n) :
    index (List.ofFn pos,pos v)=v.val := by
  rw [index_eq]
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using v.isLt)).mpr
  constructor
  · simp only [List.getElem_ofFn,decide_eq_true_eq]
  · intro j hj
    simp only [List.getElem_ofFn,decide_eq_false_iff_not]
    intro h
    have hv := congrArg Fin.val (hinj h)
    exact (Nat.ne_of_lt hj) hv

end ContinuumCoulomb.QuantumCrossingSiteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSiteRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal scan is independent of the finite vertex enumeration.
It returns the actual terminal in the emitted position tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSiteProgram
open QuantumRouteCode QuantumCrossingListBlock
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) {n : ℕ}
    (σ : Fin n ≃ Fin (P.finishedGraph N D).n) (pos : Fin n → Pair)
    (hpos : ∀ v, P.finishedPosition N D (σ v)=pos v)

include hpos in
theorem relabeled_injective : Function.Injective pos := by
  intro v w h
  apply σ.injective
  apply (P.toEmbedding.iterate N D).position_injective
  change P.finishedPosition N D (σ v)=P.finishedPosition N D (σ w)
  rw [hpos,hpos]
  exact h

include hpos in
theorem terminal_relabeled (i : Fin P.crossingCells.card) (a : Fin 4) :
    terminal a (List.ofFn pos,(P.crossingCell i).val)=
      (σ.symm (P.crossingSiteFin N hD i a)).val := by
  have hp : pos (σ.symm (P.crossingSiteFin N hD i a))=
      qmaGridPort (P.crossingCell i).val (qmaPatchDirection a) := by
    rw [← hpos,Equiv.apply_symm_apply]
    exact P.crossingSite_spec N hD (P.crossingCell i) (qmaPatchDirection a)
  unfold terminal target
  rw [← hp]
  exact index_ofFn pos (relabeled_injective P N σ pos hpos) _

include hpos in
theorem sites_relabeled (i : Fin P.crossingCells.card) :
    sites (List.ofFn pos,(P.crossingCell i).val)=
      QuantumCrossingSelectProgram.encodedSites
        (fun i a => σ.symm (P.crossingSiteFin N hD i a)) i := by
  simp only [sites,terminal_relabeled P N hD σ pos hpos,
    QuantumCrossingSelectProgram.encodedSites]

include hpos in
theorem allSites_reordered {r : ℕ} (τ : Fin r ≃ Fin P.crossingCells.card) :
    allSites (List.ofFn pos,List.ofFn (fun i => (P.crossingCell (τ i)).val))=
      List.ofFn (QuantumCrossingSelectProgram.encodedSites
        (fun i a => σ.symm (P.crossingSiteFin N hD (τ i) a))) := by
  simp only [allSites,List.map_ofFn,Function.comp_def,sites_relabeled P N hD σ pos hpos]
  apply congrArg List.ofFn
  funext i
  rfl

end ContinuumCoulomb.QuantumCrossingSiteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal short support lists for the time-ordered history compiler.
The list order, duplicate removal, and local-coordinate equivalence are
explicit; no arbitrary finite-type enumeration enters the input algorithm. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSupport
open scoped Classical

theorem supportEquiv_apply (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) (i : Fin (sites c hT a).length) :
    (supportEquiv c hT a i).val = (sites c hT a).get i := rfl

theorem siteNumber_injective (c : QMACircuit) : Function.Injective (siteNumber c) := by
  intro i j h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [siteNumber] at h
  all_goals have hi := i.isLt
  all_goals have hj := j.isLt
  · exact congrArg Sum.inl (Fin.ext h)
  · omega
  · omega
  · omega
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Fin.ext (by omega))

end ContinuumCoulomb.QuantumOrderedSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySiteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal ordered gate and propagation support lists. The values agree
with the exact support order used by the local history matrix tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySiteProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem gateLabels_actual (work : ℕ) (g : QMAGate) :
    gateLabels (work,g)=(QuantumOrderedSupport.gateSites work g).map Fin.val := by
  cases g <;> rfl

theorem propagationLabels_actual (c : QMACircuit) (t : Fin c.gates.length) :
    propagationLabels (c,t.val)=
      (QuantumOrderedSupport.propagationSites c t).map (distributedNumber c) := by
  simp only [propagationLabels,gateAt,gateLabels_actual,
    QuantumOrderedSupport.propagationSites,List.map_append,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,distributedNumber,qmaClockLeft,qmaClockMiddle,qmaClockRight]
  rfl

end ContinuumCoulomb.QuantumHistorySiteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric time grouping agrees with the exact ordered reference family.
The first-use time is computed from the actual gate list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem ordered_get (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    (ordered c)[i.val]'(by rw [ordered_length c hT]; exact i.isLt) =
      encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) := by
  simp only [ordered_actual c hT,List.getElem_map,qmaOrderedTermEquiv_get]

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational-register tables for every actual ordered history term.
Only the propagation core is multiplied, so its summation has at most
32 states regardless of the number of spectator qubits. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem value_localY (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) :
    value (localY n i s t) = sourceLocalPauli n i 1 s t := by
  rw [localY,value_finiteProduct]
  unfold sourceLocalPauli sourceTensor
  apply Finset.prod_congr rfl
  intro k _
  by_cases h : k = i
  · simp only [h,ite_true, if_true,value_pauli]
    rfl
  · simp only [h,ite_false, if_false,value_identity]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSourceIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite sum/product indices for the history qubits and padded
terms. Their natural values are the literal support-list site numbers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSourceIndex
open scoped Classical

theorem qubits_index (c : QMACircuit) :
    QuantumOrderedLabelTable.index (qubits c)=QuantumOrderedSupport.siteNumber c := by
  funext i
  rcases i with i | (i | i)
  · rfl
  · rfl
  · change qmaHistoryReferenceWork c+1+((c.gates.length+2)+i.val) =
      qmaHistoryReferenceWork c+1+(c.gates.length+2)+i.val
    omega

end ContinuumCoulomb.QuantumOrderedSourceIndex

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDescriptorSites
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The descriptor compiler computes the very same ordered support labels
as the mathematical local-history construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open QuantumHistorySiteProgram

theorem distributedLabels_actual (c : QMACircuit) (a : QMACircuitTerm c) :
    distributedLabels c (encode c a) =
      (QuantumOrderedSupport.distributedSites c (qmaFirstUseTime c) a).map
        (distributedNumber c) := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b <;>
      simp [distributedLabels,encode,QuantumOrderedSupport.distributedSites,distributedNumber]
  · simp only [distributedLabels,encode]
    norm_num only
    rw [QuantumFirstUseProgram.value_eq]
    rfl
  · cases u
    rfl
  · simp only [distributedLabels,encode]
    norm_num only
    exact propagationLabels_actual c t

theorem referenceWork_eq (c : QMACircuit) : referenceWork c=qmaHistoryReferenceWork c := rfl

theorem orderedAt_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    orderedAt c i.val = encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) := by
  unfold orderedAt
  rw [List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by rw [ordered_length c hT]; exact i.isLt)]
  exact ordered_get c hT i

theorem number_inr (c : QMACircuit) (q : QMACircuitQubit c) :
    QuantumOrderedSupport.siteNumber c (.inr q)=
      referenceWork c+1+distributedNumber c q := by
  cases q <;> simp [QuantumOrderedSupport.siteNumber,distributedNumber,referenceWork_eq,
    Nat.add_assoc]

theorem rebitLabels_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    rebitLabels c i.val =
      (QuantumOrderedSupport.rawSites c hT (.inl i)).map
        (QuantumOrderedSupport.siteNumber c) := by
  rw [rebitLabels,orderedAt_actual c hT i,distributedLabels_actual]
  simp only [QuantumOrderedSupport.rawSites,List.map_cons,List.map_map,Function.comp_def,
    QuantumOrderedSupport.siteNumber]
  congr 1
  apply List.map_congr_left
  intro q _
  exact (number_inr c q).symm

theorem referenceLabels_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    referenceLabels c ((QuantumOrderedSourceIndex.reference c).symm a).val =
      (QuantumOrderedSupport.rawSites c hT a).map
        (QuantumOrderedSupport.siteNumber c) := by
  cases a with
  | inl i =>
    change (if i.val < referenceWork c+1 then rebitLabels c i.val else _) = _
    rw [ite_eq_left (by simpa only [referenceWork_eq] using i.isLt)]
    exact rebitLabels_actual c hT i
  | inr i =>
    change referenceLabels c (qmaHistoryReferenceWork c+1+i.val) = _
    rw [referenceLabels,ite_eq_right (by rw [referenceWork_eq]; omega)]
    simp only [referenceWork_eq,Nat.add_sub_cancel_left,QuantumOrderedSupport.rawSites,
      List.map_cons,List.map_nil,QuantumOrderedSupport.siteNumber,Fin.val_castSucc,Fin.val_succ]

theorem supportLabels_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    supportLabels c ((QuantumOrderedSourceIndex.reference c).symm a).val =
      QuantumOrderedSupport.encodedSites c hT a := by
  rw [supportLabels,referenceLabels_actual c hT a,
    List.dedup_map_of_injective (QuantumOrderedSupport.siteNumber_injective c)]
  rfl

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSupportLookup
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local support coordinates are read by literal label lookup.
This identifies a small matrix input with its zero extension on spectator
qubits, without enumerating the ambient spin basis. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSupportLookup
open ExactQuantumFactoring.BitStackProgram

theorem value_map_get {α : Type} (xs : List α) (hx : xs.Nodup)
    (f : α → ℕ) (hf : Function.Injective f) (s : Fin xs.length → ℕ)
    (i : Fin xs.length) :
    value (f (xs.get i),xs.map f,List.ofFn s)=s i := by
  have hi : i.val < (xs.map f).length := by simpa only [List.length_map] using i.isLt
  have he : (xs.map f)[i.val]'hi = f (xs.get i) := by
    simp only [List.getElem_map,List.get_eq_getElem]
  have hind := (hx.map hf).idxOf_getElem i.val hi
  rw [he] at hind
  unfold value
  rw [hind,List.headD_eq_head?_getD,List.head?_drop]
  simp

theorem value_not_mem (xs ys : List ℕ) (q : ℕ)
    (hq : q ∉ xs) (hy : ys.length ≤ xs.length) : value (q,xs,ys)=0 := by
  unfold value
  rw [List.idxOf_of_notMem hq,List.drop_eq_nil_of_le hy]
  rfl

open QuantumOrderedSupport
open scoped Classical

private theorem extend_mem {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (u : QMASupportBasis S) (q : α) (hq : q ∈ S) :
    qmaSupportExtend S u q = u ⟨q,hq⟩ :=
  dite_eq_left hq

private theorem extend_not_mem {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (u : QMASupportBasis S) (q : α) (hq : q ∉ S) :
    qmaSupportExtend S u q = 0 :=
  dite_eq_right hq

theorem support_value (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) (q : Qubit c) :
    value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
      (qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun i => s ((supportEquiv c hT a).symm i)) q).val := by
  by_cases hq : q ∈ (qmaOrderedHistoryModel c hT).sites a
  · let i := (supportEquiv c hT a).symm ⟨q,hq⟩
    have hi : (sites c hT a).get i=q := by
      have h := congrArg Subtype.val ((supportEquiv c hT a).apply_symm_apply ⟨q,hq⟩)
      exact h
    have hlookup := value_map_get (sites c hT a) (sites_nodup c hT a)
      (siteNumber c) (siteNumber_injective c) (fun j => (s j).val) i
    have hv : value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
        (s i).val := by
      simpa only [encodedSites,supportBits,hi] using hlookup
    exact hv.trans (congrArg Fin.val (extend_mem
      ((qmaOrderedHistoryModel c hT).sites a)
      (fun j => s ((supportEquiv c hT a).symm j)) q hq)).symm
  · have hn : siteNumber c q ∉ encodedSites c hT a := by
      intro h
      obtain ⟨p,hp,he⟩ := List.mem_map.mp h
      have hpq := siteNumber_injective c he
      subst p
      apply hq
      rw [← sites_finset c hT a]
      exact List.mem_toFinset.mpr hp
    have hzero := value_not_mem (encodedSites c hT a) (supportBits c hT a s)
      (siteNumber c q) hn (by simp only [supportBits,List.length_ofFn,
        encodedSites,List.length_map,le_refl])
    have hv : value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) = 0 := by
      exact hzero
    exact hv.trans (congrArg Fin.val (extend_not_mem
      ((qmaOrderedHistoryModel c hT).sites a)
      (fun j => s ((supportEquiv c hT a).symm j)) q hq)).symm

theorem support_readBit (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) (q : Qubit c) :
    readBit (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun i => s ((supportEquiv c hT a).symm i)) q := by
  apply Fin.ext
  change value _ % 2 = _
  rw [support_value]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

end ContinuumCoulomb.QuantumSupportLookup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryBitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal bit reads for the small history tables, and a bounded Boolean
scan.  The register bound is unary; this scan has no spin-configuration loop. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryBitProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar

theorem row_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c) :
    row (QuantumOrderedSupport.encodedSites c hT a,
      QuantumSupportLookup.supportBits c hT a s,
      QuantumSupportLookup.supportBits c hT a t)
      (QuantumOrderedSupport.siteNumber c q) =
    qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
      (fun i => s ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) q :=
  QuantumSupportLookup.support_readBit c hT a s q

theorem column_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c) :
    column (QuantumOrderedSupport.encodedSites c hT a,
      QuantumSupportLookup.supportBits c hT a s,
      QuantumSupportLookup.supportBits c hT a t)
      (QuantumOrderedSupport.siteNumber c q) =
    qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
      (fun i => t ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) q :=
  QuantumSupportLookup.support_readBit c hT a t q

end ContinuumCoulomb.QuantumHistoryBitProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDiagonal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four diagonal descriptor cases are evaluated directly from their
clock/work bits.  Their values are exact rational entries of the actual
distributed history operator, before the rebit construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumHistoryDescriptors QuantumHistorySiteProgram QuantumHistoryBitProgram
open QuantumAlgebraicScalar
open scoped Classical

theorem distributed_entry (c : QMACircuit) (a : QMACircuitTerm c)
    (ha : (encode c a).1<4) (d : Data) :
    QuantumAlgebraicHistory.distributed c (qmaFirstUseTime c) a
      (readRow c d) (readColumn c d) =
    if readRow c d=readColumn c d then rat (weight c (encode c a) d) else rat 0 := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b <;> rfl
  · change (if readRow c d=readColumn c d then rat
        (if qmaClockAt c.gates.length (qmaFirstUseTime c i) (readRow c d ∘ Sum.inl) ∧
          qmaInputCheck c i (readRow c d ∘ Sum.inr) then 14 else 0) else rat 0) =
      if readRow c d=readColumn c d then rat
        (if clockRow c d (QuantumFirstUseProgram.value (c,i.val))=1 ∧
          clockRow c d (QuantumFirstUseProgram.value (c,i.val)+1)=0 ∧
          c.witness ≤ i.val ∧ workRow c d i.val≠0 then 14 else 0) else rat 0
    simp only [QuantumFirstUseProgram.value_eq]
    unfold qmaClockAt qmaInputCheck
    have he : (clockRow c d (qmaFirstUse c i)=1 ∧
        clockRow c d (qmaFirstUse c i+1)=0) ∧
        (c.witness ≤ i.val ∧ workRow c d i.val≠0) ↔
      clockRow c d (qmaFirstUse c i)=1 ∧
        clockRow c d (qmaFirstUse c i+1)=0 ∧
        c.witness ≤ i.val ∧ workRow c d i.val≠0 := by tauto
    simp only [readRow,clockRow,workRow,referenceWork_eq,
      QuantumOrderedSupport.siteNumber,Function.comp_apply,Fin.val_castSucc,Fin.val_succ] at *
    simp only [he]
    rfl
  · cases u
    rfl
  · norm_num [encode] at ha

theorem readRow_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    readRow c (supportData c hT a s t) = fun q =>
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => s ((QuantumOrderedSupport.supportEquiv c hT a).symm j)) (.inr q) := by
  funext q
  exact QuantumHistoryBitProgram.row_actual c hT a s t (.inr q)

theorem readColumn_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    readColumn c (supportData c hT a s t) = fun q =>
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => t ((QuantumOrderedSupport.supportEquiv c hT a).symm j)) (.inr q) := by
  funext q
  exact QuantumHistoryBitProgram.column_actual c hT a s t (.inr q)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRebitDiagonal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_imaginary _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realHeight_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realHeight_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real diagonal term remains diagonal under the reference-spin rebit
construction.  These entry identities avoid any sum over spectators. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumAlgebraicHistory QuantumAlgebraicScalar
open scoped Classical

theorem rebit_rat_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (q : ℚ)
    (hA : A (s ∘ Sum.inr) (t ∘ Sum.inr)=rat q) :
    rebit n i A s t = if s ∘ Sum.inl=t ∘ Sum.inl then rat q else rat 0 := by
  by_cases h : s ∘ Sum.inl=t ∘ Sum.inl
  · simp [rebit,hA,identity,h,rat,realRat,QuantumAlgebraicScalar.realPart,imagPart,mul,add,neg,
      realAdd,realSub,realNeg,realMul,imaginary]
  · simp [rebit,hA,identity,h,rat,realRat,QuantumAlgebraicScalar.realPart,imagPart,mul,add,neg,
      realAdd,realSub,realNeg,realMul,imaginary]

theorem rebit_diagonal_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (q : ℚ)
    (hA : A (s ∘ Sum.inr) (t ∘ Sum.inr)=
      if s ∘ Sum.inr=t ∘ Sum.inr then rat q else rat 0) :
    rebit n i A s t = if s=t then rat q else rat 0 := by
  by_cases hb : s ∘ Sum.inr=t ∘ Sum.inr
  · rw [ite_eq_left hb] at hA
    rw [rebit_rat_entry n i A s t q hA]
    have he : (s ∘ Sum.inl=t ∘ Sum.inl) ↔ s=t := by
      constructor
      · intro hr
        funext a
        cases a with
        | inl a => exact congrFun hr a
        | inr a => exact congrFun hb a
      · intro h
        exact congrArg (fun f => f ∘ Sum.inl) h
    simp only [he]
  · rw [ite_eq_right hb] at hA
    rw [rebit_rat_entry n i A s t 0 hA]
    have hne : s≠t := fun h => hb (congrArg (fun f => f ∘ Sum.inr) h)
    simp [hne]

theorem orderedExtend_at (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (i : Fin (QuantumOrderedSupport.sites c hT a).length) :
    orderedExtend c hT a s ((QuantumOrderedSupport.supportEquiv c hT a i).val)=s i := by
  calc
    orderedExtend c hT a s ((QuantumOrderedSupport.supportEquiv c hT a i).val) =
      s ((QuantumOrderedSupport.supportEquiv c hT a).symm
        (QuantumOrderedSupport.supportEquiv c hT a i)) :=
      dite_eq_left (QuantumOrderedSupport.supportEquiv c hT a i).property
    _ = s i := congrArg s ((QuantumOrderedSupport.supportEquiv c hT a).symm_apply_apply i)

theorem orderedExtend_injective (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Function.Injective (orderedExtend c hT a) := by
  intro s t h
  funext i
  have he := congrFun h (QuantumOrderedSupport.supportEquiv c hT a i).val
  simpa only [orderedExtend_at] using he

theorem ordered_diagonal_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (QuantumHistoryDescriptors.encode c
      (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4)
    (s t : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    orderedTable c hT (.inl i) s t = if s=t then rat (weight c
      (QuantumHistoryDescriptors.encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i))
      (supportData c hT (.inl i) s t)) else rat 0 := by
  let S := orderedExtend c hT (.inl i) s
  let T := orderedExtend c hT (.inl i) t
  let a := qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i
  have hd := distributed_entry c a ha (supportData c hT (.inl i) s t)
  rw [readRow_actual,readColumn_actual] at hd
  have he := rebit_diagonal_entry (qmaHistoryReferenceWork c+1) i
    (distributed c (qmaFirstUseTime c) a) S T
    (weight c (QuantumHistoryDescriptors.encode c a) (supportData c hT (.inl i) s t)) hd
  have hs : S=T ↔ s=t := (orderedExtend_injective c hT (.inl i)).eq_iff
  change rebit (qmaHistoryReferenceWork c+1) i (distributed c (qmaFirstUseTime c) a) S T = _
  rw [he]
  simp only [hs]
  rfl

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDiagonalTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity scalar tables for the actual diagonal history terms.
Only the local support bits are tabulated; the arity is at most six. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumCircuitCode QuantumHistoryDescriptors
open scoped Classical

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4) :
    table (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i),
        QuantumOrderedSupport.encodedSites c hT (.inl i)) =
      QuantumAlgebraicHistory.orderedTable c hT (.inl i) := by
  funext s t
  exact (ordered_diagonal_entry c hT i ha s t).symm

theorem tableList_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4) :
    tableList (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i),
        QuantumOrderedSupport.encodedSites c hT (.inl i)) =
      matrixData (QuantumAlgebraicHistory.orderedTable c hT (.inl i)) :=
  congrArg matrixData (table_actual c hT i ha)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite lists of actual routes produce a routing table with exactly
the permissions of the physical graph proof. Lists may use any complete edge
order; this does not change a routing decision. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable QuantumPathVisitProgram
namespace QuantumPathTable

 theorem compile_allowed {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (R : QMACellRouteBody) :
    allowed (compile (List.ofFn P.position,es.map P.routeList)) R = allowed P.routingTable R := by
  let x := (List.ofFn P.position,es.map P.routeList)
  have hc (p : Pair) : decide (p ∈ (compile x).2.2) = decide (p ∈ P.routingTable.2.2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,compile_crossings P es hcover,P.routingTable_crossing,x]
  have hv (v : Visit) : decide (v ∈ (compile x).2.1) = decide (v ∈ P.routingTable.2.1) := by
    apply Bool.eq_iff_iff.mpr
    have hh := beforeCrossings_visits P es hcover v
    constructor
    · intro h; exact decide_eq_true (hh.mp (of_decide_eq_true h))
    · intro h; exact decide_eq_true (hh.mpr (of_decide_eq_true h))
  have hs (p : Pair) : decide (p ∈ (compile x).1) = decide (p ∈ P.routingTable.1) := rfl
  change allowed (compile x) R = _
  cases R <;> simp only [allowed,hc,hv,hs]

end QuantumPathTable
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistinctCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite crossing list, with duplicates removed, enumerates
each physical crossing cell exactly once. -/

noncomputable section
namespace ContinuumCoulomb.QuantumDistinctCrossings
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es)

theorem list_eq : value (List.ofFn P.position,es.map P.routeList)=
    List.ofFn (fun i => (cellsEquiv P es hcover i).val) :=
  (List.ofFn_get _).symm

end ContinuumCoulomb.QuantumDistinctCrossings

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRoutePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite route pieces used by one literal subdivision round. -/

namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumRouteCode

theorem lookup_range (f : ℕ → Pair) (n i : ℕ) (hi : i<n) :
    lookup ((List.range n).map f) i = f i := by
  unfold lookup
  rw [List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hi)]
  simp only [List.getElem_map,List.getElem_range,Option.getD_some]

theorem tail_reverse (f : ℕ → Pair) (w : ℕ) :
    (((List.range (2*w+2)).map f).drop 2).reverse =
      (List.range (2*w)).map (fun k => f (2*w+1-k)) := by
  apply List.ext_getElem
  · simp only [List.length_reverse,List.length_drop,List.length_map,List.length_range]
    omega
  · intro i hi hj
    have hi' : i<2*w := by simpa only [List.length_map,List.length_range] using hj
    rw [List.getElem_reverse]
    simp only [List.getElem_drop,List.getElem_map,List.getElem_range,
      List.length_drop,List.length_map,List.length_range]
    congr 1
    omega

theorem freshPoints_range (e : QuantumListSchedule.Entry) (f : ℕ → Pair) (w : ℕ)
    (hw : 0<w) : freshPoints (e,(List.range (2*w+2)).map f) = [f 1,f 2] := by
  simp only [freshPoints,lookup_range f (2*w+2) 1 (by omega),
    lookup_range f (2*w+2) 2 (by omega)]

end ContinuumCoulomb.QuantumListRouteProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual edge-indexed schedule represented by a literal bond/work tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorListProgram
open scoped Classical

theorem graph_packed (s : State) (hs : Valid s) :
    QuantumListGraph.packed (graph s hs) (Equiv.refl _) = erase s.2.2 := by
  change List.ofFn (fun i => (s.2.2.get i).2) = s.2.2.map Prod.snd
  simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map s.2.2 Prod.snd

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The route-array filter selects exactly the same source indices as the
literal work-list filter, preserving their order. -/

namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule

theorem selectedRoutes_get (b : Bool) (x : Input) (i : Fin (partition b x.2.1.2.2).length) :
    (selectedRoutes b x).get (Fin.cast (selectedRoutes_length b x).symm i) =
      decoratedEntry x (indexEquiv b x.2.1.2.2 i).val := by
  change _ = decoratedEntry x ((indices b x.2.1.2.2).get
    (Fin.cast (indices_length b x.2.1.2.2).symm i))
  have hl : i.val<(selectedRoutes b x).length := by
    rw [selectedRoutes_length]
    exact i.isLt
  have hr : i.val<(indices b x.2.1.2.2).length := by
    rw [indices_length]
    exact i.isLt
  have h := congrArg (fun rs : List Routed => rs[i.val]?) (selectedRoutes_eq b x)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hl,List.getElem?_eq_getElem hr,
    Option.map_some,Option.some.injEq,List.get_eq_getElem,Fin.val_cast] using h

end ContinuumCoulomb.QuantumListRouteProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact emitted edge order realizes the abstract scheduled subdivision.
This transfers the disjoint-route invariant to the literal list compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorGraph
open scoped Classical

theorem nextEdge_tag (x : Input) (hs : Valid x.2) (t : Tags x) :
    nextEdge x hs ((tagEquiv x).symm t) = tagEdge x hs t := by
  have h := nextEdge_eq x hs ((tagEquiv x).symm t)
  simpa only [Equiv.apply_symm_apply] using h

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteRepresentation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Representation of a scheduled embedding by finite position and route arrays. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

theorem decoratedEntry_represents (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P)
    (i : Fin x.2.1.2.2.length) : decoratedEntry x i=
      (x.2.1.2.2.get i,(List.range (2*(schedule x.2.1 hx).work i+2)).map (P.point i)) := by
  unfold decoratedEntry
  rw [hP.2,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp only [dite_eq_left i.isLt,Option.getD_some]

theorem map_selectedRoutes {α : Type} (b : Bool) (x : Input) (f : Routed → α) :
    (selectedRoutes b x).map f=List.ofFn
      (fun i : Fin (partition b x.2.1.2.2).length =>
        f (decoratedEntry x (indexEquiv b x.2.1.2.2 i).val)) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,selectedRoutes_length]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn]
    have hb : i<(partition b x.2.1.2.2).length := by simpa using hj
    have h := selectedRoutes_get b x ⟨i,hb⟩
    exact congrArg f h

theorem selected_index (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)=
      (indexEquiv true s.2.2 i).val :=
  congrArg Subtype.val ((schedule s hs).active.equivFin.symm_apply_apply (activeEquiv s hs i))

theorem selected_freshPoints (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P)
    (i : Fin (partition true x.2.1.2.2).length) :
    freshPoints (decoratedEntry x (indexEquiv true x.2.1.2.2 i).val)=
      [P.point (qmaSelectedIndex (schedule x.2.1 hx).active (activePermutation x.2.1 hx i)) 1,
       P.point (qmaSelectedIndex (schedule x.2.1 hx).active (activePermutation x.2.1 hx i)) 2] := by
  rw [decoratedEntry_represents x hx P hP]
  have hw : 0<(schedule x.2.1 hx).work (indexEquiv true x.2.1.2.2 i).val :=
    (selected_true_iff _).mp (indexEquiv true x.2.1.2.2 i).property
  rw [freshPoints_range _ _ _ hw,selected_index]

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteNextPosition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal new-coordinate list is exactly the placement of the
next scheduled embedding, in the emitted spin order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode MediatorGraph
open scoped Classical

private theorem ofFn_pairs {r : ℕ} (f : Fin r × Fin 2 → Pair) :
    List.ofFn (fun k : Fin (r*2) => f (finProdFinEquiv.symm k)) =
      (List.ofFn fun i : Fin r => [f (i,0),f (i,1)]).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin r → List Pair => List.ofFn g)
  funext i
  have hh : (fun k : Fin 2 => f (finProdFinEquiv.symm
      ⟨i.val*2+k.val,by omega⟩)) = fun k : Fin 2 => f (i,k) := by
    funext k
    have he : (⟨i.val*2+k.val,by omega⟩ : Fin (r*2))=finProdFinEquiv (i,k) := by
      apply Fin.ext
      change i.val*2+k.val=k.val+2*i.val
      omega
    rw [he,Equiv.symm_apply_apply]
  rw [hh]
  simp [List.ofFn_succ,List.ofFn_zero,Fin.succ]

private theorem ofFn_vertices {n r : ℕ} (f : Fin (n+r*2) → Pair) :
    List.ofFn f = List.ofFn (fun i => f (old n r i)) ++
      (List.ofFn fun i => [f (fresh n r i 0),f (fresh n r i 1)]).flatten := by
  rw [List.ofFn_add]
  apply congrArg₂ (fun a b : List Pair => a++b)
  · apply congrArg List.ofFn
    funext i
    apply congrArg f
    exact Fin.ext rfl
  · rw [← ofFn_pairs (fun p : Fin r × Fin 2 => f (fresh n r p.1 p.2))]
    apply congrArg List.ofFn
    funext k
    apply congrArg f
    apply Fin.ext
    change n+k.val=n+(finProdFinEquiv (finProdFinEquiv.symm k)).val
    rw [Equiv.apply_symm_apply]

private theorem ofFn_cast {n m : ℕ} (h : n=m) (f : Fin n → Pair) :
    List.ofFn (fun i : Fin m => f ((finCongr h).symm i))=List.ofFn f := by
  subst m
  rfl

variable {Γ : SimpleGraph Pair}

theorem next_position (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (v : Fin (QuantumListSchedule.value (N,s)).1) :
    (nextEmbedding (N,s) hs P).position v =
      (P.next N).position (nextVertex (N,s) hs v) := rfl

theorem next_position_old (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (v : Fin s.1) :
    (nextEmbedding (N,s) hs P).position
      ((finCongr (value_count (N,s))).symm (old s.1 (partition true s.2.2).length v)) =
      P.position v := by
  rw [next_position]
  change (P.next N).position (vertexRelabel s hs
    ((finCongr (value_count (N,s))) ((finCongr (value_count (N,s))).symm
      (old s.1 (partition true s.2.2).length v)))) = _
  rw [Equiv.apply_symm_apply,vertexRelabel_old]
  exact P.nextPosition_old v

theorem next_position_fresh (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (a : Fin 2) :
    (nextEmbedding (N,s) hs P).position
      ((finCongr (value_count (N,s))).symm (fresh s.1 (partition true s.2.2).length i a)) =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) (a.val+1) := by
  rw [next_position]
  change (P.next N).position (vertexRelabel s hs
    ((finCongr (value_count (N,s))) ((finCongr (value_count (N,s))).symm
      (fresh s.1 (partition true s.2.2).length i a)))) = _
  rw [Equiv.apply_symm_apply,vertexRelabel_fresh]
  exact P.nextPosition_fresh _ a

theorem positions_next (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P) :
    positions x=List.ofFn (nextEmbedding (x.1,x.2.1) hx P).position := by
  let Q := nextEmbedding (x.1,x.2.1) hx P
  calc
    positions x = List.ofFn (fun v => Q.position ((finCongr (value_count (x.1,x.2.1))).symm v)) := by
      rw [ofFn_vertices]
      change x.2.2.1++((selectedRoutes true x).map freshPoints).flatten = _
      apply congrArg₂ (fun a b : List Pair => a++b)
      · have he : (fun v => Q.position ((finCongr (value_count (x.1,x.2.1))).symm
            (old x.2.1.1 (partition true x.2.1.2.2).length v)))=P.position := by
          funext v
          exact next_position_old x.1 x.2.1 hx P v
        rw [he]
        exact hP.1
      · rw [map_selectedRoutes]
        apply congrArg List.flatten
        apply congrArg (fun f : Fin (partition true x.2.1.2.2).length → List Pair => List.ofFn f)
        funext i
        rw [next_position_fresh,next_position_fresh]
        exact selected_freshPoints x hx P hP i
    _ = List.ofFn Q.position := ofFn_cast _ _

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteNextPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact route-index formulas for the three emitted edges of a selected
source edge and for every retained edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

theorem next_edge_retained (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition false s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inl i)) = .inl (retainedEquiv s hs i) := by
  exact nextEdge_tag (N,s) hs (.inl i)

theorem next_edge_central (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inr (i,0))) =
      .inr (.inl (activePermutation s hs i)) := by
  exact nextEdge_tag (N,s) hs (.inr (i,0))

theorem next_edge_left (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inr (i,1))) =
      .inr (.inr (activePermutation s hs i,0)) := by
  exact nextEdge_tag (N,s) hs (.inr (i,1))

theorem next_edge_right (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inr (i,2))) =
      .inr (.inr (activePermutation s hs i,1)) := by
  exact nextEdge_tag (N,s) hs (.inr (i,2))

theorem next_point (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (e : Fin (QuantumListSchedule.value (N,s)).2.2.length)
    (k : ℕ) : (nextEmbedding (N,s) hs P).point e k =
      (P.next N).point (nextEdge (N,s) hs e) k := rfl

theorem next_point_retained (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition false s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inl i)) k =
      P.point (retainedEquiv s hs i).val k := by
  rw [next_point,next_edge_retained]
  rfl

theorem next_point_central (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inr (i,0))) k =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) (k+1) := by
  rw [next_point,next_edge_central]
  rfl

theorem next_point_left (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inr (i,1))) k =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) k := by
  rw [next_point,next_edge_left]
  rfl

theorem next_point_right (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inr (i,2))) k =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i))
        (2*(schedule s hs).work
          (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i))+1-k) := by
  rw [next_point,next_edge_right]
  rfl

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteNextWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact remaining-work values in the finite output edge order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

private theorem work_map (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (e : Fin (QuantumListSchedule.value (N,s)).2.2.length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work e =
      ((schedule s hs).next N).work (nextEdge (N,s) hs e) :=
  (nextRelabel (N,s) hs).work e

theorem next_work_retained (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition false s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inl i))=0 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_retained N s hs i))

theorem next_work_central (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inr (i,0)))=0 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_central N s hs i))

theorem next_work_left (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inr (i,1)))=0 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_left N s hs i))

theorem next_work_right (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inr (i,2))) =
      (schedule s hs).work (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i))-1 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_right N s hs i))

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRoutePathOrder
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The output path array has exactly the output bond array's tag order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode

theorem pathBlock_ofFn (r : Routed) : pathBlock r=List.ofFn (pathPiece r) := by
  simp [pathBlock,pathPiece,List.ofFn_succ,List.ofFn_zero]

private theorem ofFn_triples {m : ℕ} (f : Fin m × Fin 3 → List Pair) :
    List.ofFn (fun k : Fin (m*3) => f (finProdFinEquiv.symm k)) =
      (List.ofFn fun i : Fin m => List.ofFn fun k : Fin 3 => f (i,k)).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin m → List (List Pair) => List.ofFn g)
  funext i
  apply congrArg (fun g : Fin 3 → List Pair => List.ofFn g)
  funext k
  have he : (⟨i.val*3+k.val,by omega⟩ : Fin (m*3))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    change i.val*3+k.val=k.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

theorem paths_flat (x : Input) : paths x=List.ofFn
    (fun i => tagPath x (flatTagEquiv (x.1,x.2.1) i)) := by
  rw [List.ofFn_add]
  change _ = (List.ofFn (fun i : Fin (partition false x.2.1.2.2).length =>
    tagPath x (flatTagEquiv (x.1,x.2.1) (Fin.castAdd ((partition true x.2.1.2.2).length*3) i))))++
    List.ofFn (fun i : Fin ((partition true x.2.1.2.2).length*3) =>
      tagPath x (flatTagEquiv (x.1,x.2.1) (Fin.natAdd (partition false x.2.1.2.2).length i)))
  simp only [flatTagEquiv,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,Equiv.refl_apply,
    Sum.map_inl,Sum.map_inr,tagPath]
  have h3 := ofFn_triples (fun p : Fin (partition true x.2.1.2.2).length × Fin 3 =>
    pathPiece (decoratedEntry x (indexEquiv true x.2.1.2.2 p.1).val) p.2)
  rw [h3]
  change (selectedRoutes false x).map Prod.snd++((selectedRoutes true x).map pathBlock).flatten = _
  rw [map_selectedRoutes,map_selectedRoutes]
  simp_rw [pathBlock_ofFn]

theorem paths_tagged (x : Input) : paths x=List.ofFn
    (fun i => tagPath x (tagEquiv (x.1,x.2.1) i)) := by
  rw [paths_flat]
  apply List.ext_getElem
  · simp only [List.length_ofFn,value_length]
  · intro i hi hj
    simp only [List.getElem_ofFn,tagEquiv,Equiv.trans_apply,finCongr_apply]
    apply congrArg (tagPath x)
    apply congrArg (flatTagEquiv (x.1,x.2.1))
    exact Fin.ext rfl

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRoutePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preservation of the exact finite coordinate/route representation by one
round, and hence by the fixed number of rounds of the literal compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

private theorem range_map_congr {a b : ℕ} {f g : ℕ → Pair}
    (h : a=b) (hf : ∀ k, f k=g k) :
    (List.range (2*a+2)).map f=(List.range (2*b+2)).map g :=
  congrArg₂ List.map (funext hf) (congrArg (fun k => List.range (2*k+2)) h)

theorem tagPath_next (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P)
    (t : Tags (x.1,x.2.1)) :
    tagPath x t = (List.range (2*(schedule (QuantumListSchedule.value (x.1,x.2.1))
      (value_valid (x.1,x.2.1) hx)).work ((tagEquiv (x.1,x.2.1)).symm t)+2)).map
        ((nextEmbedding (x.1,x.2.1) hx P).point ((tagEquiv (x.1,x.2.1)).symm t)) := by
  rcases t with i | ⟨i,k⟩
  · change (decoratedEntry x (indexEquiv false x.2.1.2.2 i).val).2 = _
    rw [decoratedEntry_represents x hx P hP]
    change (List.range (2*(schedule x.2.1 hx).work (retainedEquiv x.2.1 hx i).val+2)).map
      (P.point (retainedEquiv x.2.1 hx i).val) = _
    exact (range_map_congr
      ((schedule x.2.1 hx).retained_work_zero (retainedEquiv x.2.1 hx i))
      (fun _ => rfl)).trans
      (range_map_congr (next_work_retained x.1 x.2.1 hx i)
        (next_point_retained x.1 x.2.1 hx P i)).symm
  · change pathPiece (decoratedEntry x (indexEquiv true x.2.1.2.2 i).val) k = _
    rw [decoratedEntry_represents x hx P hP,← selected_index x.2.1 hx i]
    let e := qmaSelectedIndex (schedule x.2.1 hx).active (activePermutation x.2.1 hx i)
    let w := (schedule x.2.1 hx).work e
    let f := P.point e
    have hw : 0<w := (schedule x.2.1 hx).selected_work_pos (activePermutation x.2.1 hx i)
    have h0 : 0<2*w+2 := by omega
    have h1 : 1<2*w+2 := by omega
    have h2 : 2<2*w+2 := by omega
    have hn : 2*(w-1)+2=2*w := by omega
    fin_cases k
    · change [lookup ((List.range (2*w+2)).map f) 1,
        lookup ((List.range (2*w+2)).map f) 2] = _
      have hl : [lookup ((List.range (2*w+2)).map f) 1,
        lookup ((List.range (2*w+2)).map f) 2] =
        (List.range 2).map (fun k => f (k+1)) := by
        rw [lookup_range f _ _ h1,lookup_range f _ _ h2]
        rfl
      exact hl.trans (range_map_congr (next_work_central x.1 x.2.1 hx i)
        (next_point_central x.1 x.2.1 hx P i)).symm
    · change [lookup ((List.range (2*w+2)).map f) 0,
        lookup ((List.range (2*w+2)).map f) 1] = _
      have hl : [lookup ((List.range (2*w+2)).map f) 0,
        lookup ((List.range (2*w+2)).map f) 1] = (List.range 2).map f := by
        rw [lookup_range f _ _ h0,lookup_range f _ _ h1]
        rfl
      exact hl.trans (range_map_congr (next_work_left x.1 x.2.1 hx i)
        (next_point_left x.1 x.2.1 hx P i)).symm
    · change (((List.range (2*w+2)).map f).drop 2).reverse = _
      have hl : (((List.range (2*w+2)).map f).drop 2).reverse =
        (List.range (2*(w-1)+2)).map (fun k => f (2*w+1-k)) := by
        rw [tail_reverse,hn]
      exact hl.trans (range_map_congr (next_work_right x.1 x.2.1 hx i)
        (next_point_right x.1 x.2.1 hx P i)).symm

theorem paths_next (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P) :
    paths x=List.ofFn (fun e => (List.range (2*(schedule
      (QuantumListSchedule.value (x.1,x.2.1)) (value_valid (x.1,x.2.1) hx)).work e+2)).map
        ((nextEmbedding (x.1,x.2.1) hx P).point e)) := by
  rw [paths_tagged]
  apply congrArg List.ofFn
  funext e
  have h := tagPath_next x hx P hP (tagEquiv (x.1,x.2.1) e)
  simpa only [Equiv.symm_apply_apply] using h

theorem value_represents (x : Input) (hx : Valid x.2.1)
    (P : QMAPathEmbedding (schedule x.2.1 hx) Γ) (hP : Represents x.2 hx P) :
    Represents (value x) (value_valid (x.1,x.2.1) hx) (nextEmbedding (x.1,x.2.1) hx P) :=
  ⟨positions_next x hx P hP,paths_next x hx P hP⟩

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFinalPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Precision for all nine early simulation errors and the subsequent
routing errors, retaining the exact final inverse-polynomial promise gap. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open ExactQuantumFactoring.BitStackProgram

theorem finalPrecision_pos (rounds : ℕ) (c : QMACircuit) :
    0 < finalPrecision rounds c := by
  unfold finalPrecision
  positivity

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regrouping the literal initial ports recovers the two physical end
couplings of each input edge. The regrouping uses its actual endpoint table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialBond_mem (bs : List Bond) (j : ℕ) (hj : j < 2*bs.length) :
    initialBond bs j ∈ bs := by
  have hi : j/2 < bs.length := by omega
  simp only [initialBond,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem initialEndpoint_bound (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (j : ℕ) (hj : j < 2*bs.length) : initialEndpoint bs j < n := by
  have h := hb _ (initialBond_mem bs j hj)
  unfold initialEndpoint
  split
  · exact h.1
  · exact h.2

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrdinalProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal ordinal-slot program. For an encoded cell list and a unary
label it counts earlier labels in the same cell; the result agrees with the
bounded injective slots used by the spatial construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrdinalProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem value_eq_card (x : Input) :
    value x = ((Finset.range x.1).filter (fun i =>
      QuantumPathVisitProgram.lookup x.2 i = QuantumPathVisitProgram.lookup x.2 x.1)).card := by
  unfold value sameCell
  rw [List.countP_map]
  simp only [Function.comp_def,id_eq]
  symm
  simpa only [List.toFinset_range,Function.comp_apply,id_eq] using
    (List.nodup_range (n := x.1)).card_eq_countP
      (P := fun i => QuantumPathVisitProgram.lookup x.2 i = QuantumPathVisitProgram.lookup x.2 x.1)

theorem lookup_ofFn {n : ℕ} (cells : Fin n → Pair) (q : Fin n) :
    QuantumPathVisitProgram.lookup (List.ofFn cells) q.val = cells q := by
  unfold QuantumPathVisitProgram.lookup
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp

theorem value_ofFn {n : ℕ} (cells : Fin n → Pair) (q : Fin n) :
    value (q.val,List.ofFn cells) = QuantumOrdinalSlots.rank cells q := by
  rw [value_eq_card]
  unfold QuantumOrdinalSlots.rank
  symm
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    obtain ⟨_,hlt,hcell⟩ := Finset.mem_filter.mp hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hlt,?_⟩
    simpa only [lookup_ofFn] using hcell
  · intro r hr s hs h
    exact Fin.ext h
  · intro i hi
    obtain ⟨hi,hcell⟩ := Finset.mem_filter.mp hi
    have hiq : i < q.val := Finset.mem_range.mp hi
    let r : Fin n := ⟨i,hiq.trans q.isLt⟩
    refine ⟨r,?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hiq,?_⟩
    simpa only [← show r.val=i from rfl,lookup_ofFn] using hcell

end ContinuumCoulomb.QuantumOrdinalProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialSlotProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fine-grid positions and lane colors of the ordinal-slot model
are computed directly from encoded lists of cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialSlotProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumOrdinalProgram

theorem colorEquiv_val {B : ℕ} (c : Fin 3 × Fin 3 × Fin B) :
    (qmaGridColorEquiv B c).val = c.2.2.val+B*c.2.1.val+(3*B)*c.1.val := by
  rfl

theorem fineSite_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    {m : ℕ} (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    fineSite A (q.val,List.ofFn (QuantumOrdinalPlacement.coordinates M.cell)) =
      (M.withOrdinalSlots labels).routeVertex q := by
  unfold fineSite
  rw [lookup_ofFn,value_ofFn]
  rfl

theorem lane_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    {m : ℕ} (labels : M.Term ≃ Fin m) (e : M.Term) :
    lane B ((labels e).val,
      List.ofFn (QuantumOrdinalPlacement.coordinates (M.anchor ∘ labels.symm))) =
      ((M.withOrdinalSlots labels).laneColor e).val := by
  unfold lane
  rw [lookup_ofFn,value_ofFn]
  change _ = (qmaGridColorEquiv B ((M.withOrdinalSlots labels).termSlots.color e)).val
  rw [colorEquiv_val]
  simp only [QMASpatialExchangeModel.withOrdinalSlots,QMACellSlots.color,
    QMACellSlots.transport,QuantumOrdinalPlacement.slots,QuantumOrdinalPlacement.coordinates,
    Function.comp_apply,Equiv.symm_apply_apply]

end ContinuumCoulomb.QuantumSpatialSlotProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint arm assigned to an incident interaction is the number of
incident lane colors below it. This exposes the finite count used by the
literal route evaluator. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaPort_orderRank {C : ℕ} (s : Finset (Fin C)) (x : s) :
    ((s.orderIsoOfFin rfl).symm x).val = (s.filter (fun y => y < x.val)).card := by
  let E := s.orderIsoOfFin rfl
  have h : (Finset.Iio (E.symm x)).card = (s.filter (fun y => y < x.val)).card := by
    apply Finset.card_bij (fun i _ => (E i).val)
    · intro i hi
      refine Finset.mem_filter.mpr ⟨(E i).property,?_⟩
      have hh := E.strictMono (Finset.mem_Iio.mp hi)
      change (E i).val < (E (E.symm x)).val at hh
      simpa only [E.apply_symm_apply] using hh
    · intro i hi j hj hij
      exact E.injective (Subtype.ext hij)
    · intro y hy
      obtain ⟨hys,hyx⟩ := Finset.mem_filter.mp hy
      refine ⟨E.symm ⟨y,hys⟩,Finset.mem_Iio.mpr ?_,?_⟩
      · exact E.symm.strictMono hyx
      · exact congrArg Subtype.val (E.apply_symm_apply ⟨y,hys⟩)
  simpa only [Fin.card_Iio] using h

theorem qmaCanonicalSortedPorts_assign_rank {κ : Type} [Fintype κ] {C : ℕ}
    (color : κ → Fin C) (hc : Fintype.card κ ≤ 3) (hi : Function.Injective color) (e : κ) :
    ((qmaCanonicalSortedPorts color hc).assign e).val =
      (Finset.univ.filter (fun f => color f < color e)).card := by
  let s := Finset.univ.image color
  have he : color e ∈ s := Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩
  change ((s.orderIsoOfFin rfl).symm ⟨color e,he⟩).val = _
  rw [qmaPort_orderRank]
  symm
  apply Finset.card_bij (fun f _ => color f)
  · intro f hf
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨f,Finset.mem_univ _,rfl⟩,(Finset.mem_filter.mp hf).2⟩
  · intro f hf g hg h
    exact hi h
  · intro y hy
    obtain ⟨hys,hy⟩ := Finset.mem_filter.mp hy
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hys
    exact ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,rfl⟩

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem endpointPorts_assign_rank (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) (e : M.Incident v) :
    ((M.endpointPorts hd v).assign e).val =
      (Finset.univ.filter (fun f : M.Incident v => M.laneColor f.val < M.laneColor e.val)).card :=
  qmaCanonicalSortedPorts_assign_rank _ _ (M.incident_color_injective hA v) e

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRankProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sorted endpoint port is evaluated by counting incident edges whose
lane color is smaller. Each record contains the two endpoints and lane color. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortRankProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem count_ofFn {n : ℕ} (entries : Fin n → Entry) (vc : Pair) :
    value (vc,List.ofFn entries) =
      (Finset.univ.filter (fun i =>
        ((entries i).1=vc.1 ∨ (entries i).2.1=vc.1) ∧ (entries i).2.2<vc.2)).card := by
  unfold value below
  rw [List.ofFn_eq_map,List.map_map,List.countP_map]
  simp only [Function.comp_def,id_eq]
  symm
  simpa only [List.toFinset_finRange] using (List.nodup_finRange n).card_eq_countP
    (P := fun i => ((entries i).1=vc.1 ∨ (entries i).2.1=vc.1) ∧ (entries i).2.2<vc.2)

end ContinuumCoulomb.QuantumPortRankProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRankActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal incidence count computes the very arm assignment used by the
spatial routing proof, for any explicit enumeration of the interaction labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortRankProgram
open scoped Classical

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    value ((v.val,(M.laneColor e.val).val),List.ofFn (entries M labels)) =
      ((M.endpointPorts hd v).assign e).val := by
  rw [count_ofFn,M.endpointPorts_assign_rank hA]
  symm
  apply Finset.card_bij (fun f _ => labels f.val)
  · intro f hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [entries,labels.symm_apply_apply]
    refine ⟨?_,(Finset.mem_filter.mp hf).2⟩
    rcases f.property with hl | hr
    · exact Or.inl (congrArg Fin.val hl)
    · exact Or.inr (congrArg Fin.val hr)
  · intro f hf g hg h
    exact Subtype.ext (labels.injective h)
  · intro i hi
    obtain ⟨_,hinc,hlt⟩ := Finset.mem_filter.mp hi
    dsimp only [entries] at hinc hlt
    have hmember : M.left (labels.symm i)=v ∨ M.right (labels.symm i)=v :=
      hinc.imp Fin.ext Fin.ext
    let f : M.Incident v := ⟨labels.symm i,hmember⟩
    refine ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩,?_⟩
    exact labels.apply_symm_apply i

end ContinuumCoulomb.QuantumPortRankProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell arrays follow the same term-major order as the literal local-word
compiler. Each new mediator inherits its term's cell; each output word retains
that cell as its anchor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem cells_ofFn {n m : ℕ} (d : ℕ) (cell : Fin n → Pair) (anchor : Fin m → Pair) :
    (value d (List.ofFn cell,List.ofFn anchor)).1=List.ofFn (Fin.append cell anchor) :=
  (List.ofFn_fin_append cell anchor).symm

theorem anchors_ofFn {m : ℕ} (d : ℕ) (anchor : Fin m → Pair) :
    anchors d (List.ofFn anchor)=
      (List.ofFn (fun i : Fin m => List.ofFn (fun _ : Fin d => anchor i))).flatten := by
  simp only [anchors,List.map_ofFn,List.ofFn_const,Function.comp_def]

end ContinuumCoulomb.QuantumOrderedCellProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellTable
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed spatial arrays use exactly the same sum/product enumeration
as the actual ordered Hamiltonian compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellTable
open QuantumOrderedCellProgram QuantumOrderedLabelTable QuantumOrderedSpatialComplete
open ExactQuantumFactoring.BitStackProgram
open QuantumRouteCode
variable {ι κ : Type} {n m : ℕ}

theorem value_table (d : ℕ) (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    value d (table q e cell anchor)=
      table (nextQubit q e) (nextTerm e d) (extendCell cell anchor) (extendAnchor d anchor) := by
  apply Prod.ext
  · rw [show (value d (table q e cell anchor)).1=
        List.ofFn (Fin.append (fun i => cell (q i)) (fun i => anchor (e i))) from cells_ofFn d _ _]
    apply congrArg List.ofFn
    funext i
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n+m)).surjective i
    cases i <;> simp [nextQubit,extendCell,Fin.append]
  · change anchors d (List.ofFn (fun i => anchor (e i)))=List.ofFn _
    rw [anchors_ofFn]
    rw [← product_table (fun p : Fin m × Fin d => anchor (e p.1))]
    apply congrArg List.ofFn
    funext i
    rfl

theorem complete_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    complete (table q e cell anchor)=
      table (QuantumOrderedLabelTable.qubits6 q e) (QuantumOrderedLabelTable.terms6 e)
        (cell6 cell anchor) (anchor6 anchor) := by
  unfold complete
  rw [value_table,value_table,value_table,value_table,value_table,value_table]
  rfl

end ContinuumCoulomb.QuantumOrderedCellTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw four-spin compiler repeats each computed logical cell four times,
in exactly the order of its physical spin indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawCells
open QuantumOrderedCellProgram QuantumOrderedCellTable QuantumOrderedSpatialComplete
open QuantumOrderedLabelTable QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

theorem four_ofFn {n : ℕ} (cell : Fin n → Pair) :
    anchors 4 (List.ofFn cell)=
      List.ofFn (fun i : Fin (n*4) => cell (finProdFinEquiv.symm i).1) := by
  rw [anchors_ofFn,← product_table (fun p : Fin n × Fin 4 => cell p.1)]

theorem value_table {ι κ : Type} {n m : ℕ} (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    value (table q e cell anchor)=
      List.ofFn (fun i : Fin (finalCount n m*4) =>
        cell6 cell anchor (qubits6 q e (finProdFinEquiv.symm i).1)) := by
  unfold value
  rw [complete_table]
  exact four_ofFn _

end ContinuumCoulomb.QuantumOrderedRawCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual row/column arrays for the fork compiler. The scale remains an
input register; only the number of fork rounds is fixed. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem run_state (k : ℕ) (x : Input) : (run k x).1=iterate x.1 k x.2.1 := by
  induction k with
  | zero => rfl
  | succ k ih => change next x.1 (run k x).1=next x.1 (iterate x.1 k x.2.1); rw [ih]

theorem run_length (k : ℕ) (x : Input) (h : x.2.2.length=x.2.1.1) :
    (run k x).2.length=(run k x).1.1 := by
  cases k with
  | zero => exact h
  | succ k => simp only [run,step,nextCells,List.length_map,List.length_range,next]

theorem lookup_nextCells (x : Cells) (v : ℕ) (hv : v<x.1.1+2*pairCount x.1.2.2.2) :
    lookup (nextCells x) v=nextCell x.1 (lookup x.2) v := by
  simp only [lookup,nextCells,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hv)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem nextCell_congr (s : QuantumForkList.State) (hs : ValidPorts s.1 s.2.2.2)
    (f g : ℕ → QuantumRouteCode.Pair) (h : ∀ v, v < s.1 → f v=g v) (v : ℕ)
    (hv : v<(next 0 s).1) : nextCell s f v=nextCell s g v := by
  by_cases ho : v < s.1
  · simpa only [nextCell,ite_eq_left ho] using h v ho
  have hi : (v-s.1)/2<pairCount s.2.2.2 := by
    change v < s.1+2*pairCount s.2.2.2 at hv
    omega
  simp only [nextCell,ite_eq_right ho]
  rw [catalog_actualSite hs ⟨(v-s.1)/2,hi⟩]
  exact h _ (actualSite hs ⟨(v-s.1)/2,hi⟩ 0).isLt

theorem step_represents (x : Input) (hs : ValidPorts x.2.1.1 x.2.1.2.2.2)
    (cell : ℕ → QuantumRouteCode.Pair) (h : Represents x.2 cell) :
    Represents (step x) (nextCell x.2.1 cell) := by
  intro v hv
  change lookup (nextCells x.2) v=nextCell x.2.1 cell v
  rw [lookup_nextCells x.2 v hv]
  exact nextCell_congr x.2.1 hs _ _ h v hv

theorem run_represents (k : ℕ) (x : Input) (hs : ValidPorts x.2.1.1 x.2.1.2.2.2)
    (cell : ℕ → QuantumRouteCode.Pair) (h : Represents x.2 cell) :
    Represents (run k x) (iterateCell x.1 k x.2.1 cell) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hi : ValidPorts (run k x).1.1 (run k x).1.2.2.2 := by
      rw [run_state]
      exact iterate_validPorts x.1 x.2.1 hs k
    have hn := step_represents (x.1,run k x) hi _ ih
    simpa only [run_state,run,iterateCell] using hn

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial subdivision computes its row/column array from the actual
endpoint list, before the same fixed-round grid program is applied. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList MediatorListProgram ExactQuantumFactoring.BitStackProgram

theorem lookup_initialCells (x : InitialCells) (v : ℕ) (hv : v<x.1+2*x.2.1.length) :
    lookup (initialCells x) v=initialCell x.1 x.2.1 (lookup x.2.2) v := by
  simp only [lookup,initialCells,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hv)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem output_state (k : ℕ) (x : PreparedInput) :
    (output k x).1=iterate x.1.1 k
      (initial x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.1.1) := run_state k (prepare x)

theorem output_length (k : ℕ) (x : PreparedInput) :
    (output k x).2.length=(output k x).1.1 := by
  apply run_length
  simp only [prepare,initialCells,List.length_map,List.length_range,initial]

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingInputActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The encoded cell/edge arrays evaluate to the actual buffered path of the
ordinal-slot spatial model. No arbitrary finite-fiber choice remains in this
part of the routing compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingInputProgram
open QuantumRouteCode

theorem edge_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (e : M.Term) :
    edge (actualData M labels) (labels e).val = ((M.left e).val,(M.right e).val) := by
  unfold edge actualData
  rw [QuantumOrdinalProgram.lookup_ofFn]
  simp only [Equiv.symm_apply_apply]

theorem fine_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    fine A (actualData M labels) q.val = (M.withOrdinalSlots labels).routeVertex q := by
  unfold fine actualData
  simp only [List.length_ofFn,Nat.min_eq_right q.isLt.le]
  exact QuantumSpatialSlotProgram.fineSite_actual M labels q

theorem lane_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (e : M.Term) :
    lane B ((labels e).val,actualData M labels) = ((M.withOrdinalSlots labels).laneColor e).val :=
  QuantumSpatialSlotProgram.lane_actual M labels e

theorem entry_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (e : M.Term) :
    entry B (actualData M labels) (labels e).val =
      QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels (labels e) := by
  unfold entry
  rw [edge_actual,lane_actual]
  exact (congrArg (fun t : M.Term => ((M.left t).val,(M.right t).val,
    ((M.withOrdinalSlots labels).laneColor t).val)) (labels.symm_apply_apply e)).symm

private theorem entries_ofFn (B : ℕ) (d : Data) {m : ℕ}
    (f : Fin m → QuantumPortRankProgram.Entry) (hlen : d.2.length = m)
    (h : ∀ i : Fin m, entry B d i.val = f i) : entries B d = List.ofFn f := by
  apply List.ext_getElem
  · simp only [entries,List.length_map,List.length_range,List.length_ofFn,hlen]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    simpa only [entries,List.getElem_map,List.getElem_range,List.getElem_ofFn] using h ⟨i,hi'⟩

theorem entries_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) :
    entries B (actualData M labels) =
      List.ofFn (QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels) := by
  apply entries_ofFn B (actualData M labels)
    (QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels)
    (by simp only [actualData,List.length_ofFn])
  intro j
  calc
    entry B (actualData M labels) j.val =
        entry B (actualData M labels) (labels (labels.symm j)).val :=
      congrArg (fun k : Fin m => entry B (actualData M labels) k.val)
        (labels.apply_symm_apply j).symm
    _ = QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels
        (labels (labels.symm j)) := entry_actual M labels (labels.symm j)
    _ = _ := congrArg (QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels)
      (labels.apply_symm_apply j)

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    value A B ((labels e).val,actualData M labels) =
      QuantumBufferedListProgram.actualInput (M.withOrdinalSlots labels) hd e := by
  unfold value
  rw [edge_actual,lane_actual,entries_actual]
  dsimp only
  exact congrArg₂ Prod.mk
    (congrArg₂ Prod.mk (fine_actual M labels (M.left e)) (fine_actual M labels (M.right e)))
    (congrArg (Prod.mk ((M.withOrdinalSlots labels).laneColor e).val)
      (congrArg₂ Prod.mk
        (QuantumPortRankProgram.value_actual (M.withOrdinalSlots labels) labels hA hd
          (M.left e) ⟨e,Or.inl rfl⟩)
        (QuantumPortRankProgram.value_actual (M.withOrdinalSlots labels) labels hA hd
          (M.right e) ⟨e,Or.inr rfl⟩)))

theorem path_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    QuantumBufferedListProgram.path A B (value A B ((labels e).val,actualData M labels)) =
      ((M.withOrdinalSlots labels).bufferedPath hd e).val.support := by
  exact (congrArg (QuantumBufferedListProgram.path A B)
    (value_actual M labels hA hd e)).trans
    (QuantumBufferedListProgram.path_actual (M.withOrdinalSlots labels) hd e)

end ContinuumCoulomb.QuantumRoutingInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkRoutingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal routing-input tape from the full fork state. Active-star bonds
are retained, and each anchor is the integer midpoint of its endpoint cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkRoutingData
open ExactQuantumFactoring.BitStackProgram QuantumForkList MediatorListProgram

private theorem lookup_ofFn {n : ℕ} (f : Fin n → QuantumRouteCode.Pair) (i : Fin n) :
    QuantumForkGridProgram.lookup (List.ofFn f) i.val=f i :=
  QuantumOrdinalProgram.lookup_ofFn f i

theorem value_spatialModel {rows width : ℕ} (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) (cell : ℕ → QMAGridCell rows width) (A : ℕ)
    (hc : ∀ p, qmaCellMass (fun v : Fin s.1 => cell v.val) p ≤ A)
    (hd : ∀ v : Fin s.1, degree (fullList s) v.val ≤ 3)
    (hl : BondLocal (fullList s) cell CommonCell) :
    value (s,List.ofFn (fun v : Fin s.1 => ((cell v.val).1.val,(cell v.val).2.val))) =
      QuantumRoutingInputProgram.actualData (spatialModel s hs hb hn cell A hc hd hl)
        (Equiv.refl _) := by
  let G := fullGraph s hs hb hn
  let cells : Fin s.1 → QuantumRouteCode.Pair :=
    fun v => ((cell v.val).1.val,(cell v.val).2.val)
  have endpoints : (fullList s).map endpoint =
      List.ofFn (fun i : Fin (fullList s).length => endpoint ((fullList s).get i)) := by
    simpa only [List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map (fullList s) endpoint).symm
  have anchors : (fullList s).map (fun b => anchor (b,List.ofFn cells)) =
      List.ofFn (fun i : Fin (fullList s).length =>
        QuantumGridMidpoint.value (cells (G.left i),cells (G.right i))) := by
    rw [← List.ofFn_getElem_eq_map (fullList s) (fun b => anchor (b,List.ofFn cells))]
    apply congrArg List.ofFn
    funext i
    change QuantumGridMidpoint.value
      (QuantumForkGridProgram.lookup (List.ofFn cells) (G.left i).val,
        QuantumForkGridProgram.lookup (List.ofFn cells) (G.right i).val) = _
    dsimp only [G,fullGraph,QuantumListGraph.ofBonds]
    rw [lookup_ofFn,lookup_ofFn]
  unfold value QuantumRoutingInputProgram.actualData
  apply congrArg₂ Prod.mk
  · apply congrArg₂ Prod.mk
    · rfl
    · exact anchors
  · exact endpoints

end ContinuumCoulomb.QuantumForkRoutingData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateScalarReduction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar reduction of a one-site gate tensor to its active entry
and spectator equality test. This avoids an ambient spin-basis sum in the
literal history-matrix evaluator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateScalarReduction
open QuantumAlgebraicScalar QuantumFixedPauli QuantumAlgebraicHistory
open scoped Classical

theorem listProduct_single {α : Type} [DecidableEq α] (i : α) (z : Scalar)
    (xs : List α) (hx : xs.Nodup) :
    product (xs.map (fun j => if j=i then z else rat 1)) =
      if i ∈ xs then z else rat 1 := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih =>
    by_cases ha : a=i
    · subst a
      have hn : i ∉ xs := (List.nodup_cons.mp hx).1
      simp [product,ih (List.nodup_cons.mp hx).2,hn]
    · simp [product,ha,ih (List.nodup_cons.mp hx).2,Ne.symm ha]

theorem listProduct_zero (xs : List Scalar) (h : rat 0 ∈ xs) : product xs=rat 0 := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with ha | hx
    · subst a
      simp [product]
    · simp [product,ih hx]

theorem finiteProduct_single {α : Type} [Fintype α] [DecidableEq α]
    (i : α) (z : Scalar) :
    finiteProduct (fun j => if j=i then z else rat 1)=z := by
  have hn : (enumerate α).Nodup :=
    List.nodup_ofFn.mpr (Fintype.equivFin α).symm.injective
  have hi : i ∈ enumerate α :=
    List.mem_ofFn.mpr ⟨(Fintype.equivFin α) i,(Fintype.equivFin α).symm_apply_apply i⟩
  rw [finiteProduct,listProduct_single i z _ hn,ite_eq_left hi]

theorem finiteProduct_zero {α : Type} [Fintype α] (f : α → Scalar)
    (i : α) (hi : f i=rat 0) : finiteProduct f=rat 0 := by
  apply listProduct_zero
  apply List.mem_map.mpr
  refine ⟨i,?_,hi⟩
  exact List.mem_ofFn.mpr
    ⟨(Fintype.equivFin α) i,(Fintype.equivFin α).symm_apply_apply i⟩

theorem finiteProduct_sparse {α : Type} [Fintype α] [DecidableEq α]
    (i : α) (A : Fin 2 → Fin 2 → Scalar) (s t : α → Fin 2) :
    finiteProduct (fun j => if j=i then A (s j) (t j) else identity (s j) (t j)) =
      sparseEntry i A s t := by
  by_cases h : ∀ j, j ≠ i → s j=t j
  · have he : (fun j => if j=i then A (s j) (t j) else identity (s j) (t j)) =
        (fun j => if j=i then A (s i) (t i) else rat 1) := by
      funext j
      by_cases hj : j=i
      · simp [hj]
      · simp [hj,identity,h j hj]
    rw [he,finiteProduct_single]
    exact (ite_eq_left h).symm
  · obtain ⟨j,hj⟩ := not_forall.mp h
    have hji : j ≠ i := fun he => hj (by simp [he])
    have hst : s j ≠ t j := fun he => hj (fun _ => he)
    rw [finiteProduct_zero _ j (by simp [hji,identity,hst])]
    exact (ite_eq_right h).symm

theorem hadamard_entry (work j : ℕ) (s t : SourceSpinBasis (work+1)) :
    gate work (.hadamard j) s t=sparseEntry (qmaQubit work j) hadamard s t :=
  finiteProduct_sparse _ _ _ _

theorem phaseT_entry (work j : ℕ) (s t : SourceSpinBasis (work+1)) :
    gate work (.phaseT j) s t=sparseEntry (qmaQubit work j) phaseT s t :=
  finiteProduct_sparse _ _ _ _

end ContinuumCoulomb.QuantumGateScalarReduction

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateEntryProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact gate entries from a bounded register scan.  Work is unary, addresses
and support labels are binary, and each quantum bit is read from the supplied
small support table.  No sum over ambient configurations occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateEntryProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumCircuitCode
open scoped Classical

theorem allWork_iff (x : Input) : allWork x = true ↔
    ∀ i : Fin (x.1+1), point x i.val = true := by
  simp only [allWork,List.all_map,List.all_eq_true,List.mem_range,Function.comp_apply,id_eq]
  exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩

theorem allWork_single (x : Input) (hg : gateTag x.2.2.1 ≠ 2) :
    allWork x = true ↔ ∀ i : Fin (x.1+1),
      i ≠ qmaQubit x.1 (gateLeft x.2.2.1) → row x i.val=column x i.val := by
  rw [allWork_iff]
  simp only [point,ite_eq_right hg,Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · intro h i hi
    rcases h i with he | he
    · exact False.elim (hi (Fin.ext he))
    · exact Fin.ext he
  · intro h i
    by_cases hi : i=qmaQubit x.1 (gateLeft x.2.2.1)
    · exact Or.inl (congrArg Fin.val hi)
    · exact Or.inr (congrArg Fin.val (h i hi))

private theorem swap_val (b : Fin 2) : (Equiv.swap (0 : Fin 2) 1 b).val = 1-b.val := by
  fin_cases b <;> decide

theorem allWork_cnot (work base a b : ℕ) (d : QuantumHistoryBitProgram.Data) :
    allWork (work,base,.controlledNot a b,d) = true ↔
      (fun i : Fin (work+1) => row (work,base,.controlledNot a b,d) i.val) =
      qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun i => column (work,base,.controlledNot a b,d) i.val) := by
  rw [allWork_iff,funext_iff]
  apply forall_congr'
  intro i
  change decide ((row (work,base,.controlledNot a b,d) i.val).val =
    if i.val=b%(work+1) ∧ (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1 then
      1-(column (work,base,.controlledNot a b,d) i.val).val
    else (column (work,base,.controlledNot a b,d) i.val).val)=true ↔ _
  rw [decide_eq_true_eq]
  have ht : (i.val=b%(work+1)) ↔ i=qmaQubit work b :=
    ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have hc : (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1 ↔
      column (work,base,.controlledNot a b,d) (a%(work+1))=1 :=
    ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have he : (i.val=b%(work+1) ∧
      (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1) ↔
      (i=qmaQubit work b ∧
        column (work,base,.controlledNot a b,d) (a%(work+1))=1) := and_congr ht hc
  by_cases h : i=qmaQubit work b ∧
      column (work,base,.controlledNot a b,d) (a%(work+1))=1
  · have hr : qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun j => column (work,base,.controlledNot a b,d) j.val) i =
        Equiv.swap (0:Fin 2) 1 (column (work,base,.controlledNot a b,d) i.val) :=
      ite_eq_left h
    rw [ite_eq_left (he.mpr h),hr,Fin.ext_iff,swap_val]
  · have hr : qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun j => column (work,base,.controlledNot a b,d) j.val) i =
        column (work,base,.controlledNot a b,d) i.val := ite_eq_right h
    rw [ite_eq_right (mt he.mp h),hr,Fin.ext_iff]

theorem entry_eq (work base : ℕ) (g : QMAGate) (d : QuantumHistoryBitProgram.Data) :
    entry (work,base,g,d) = QuantumAlgebraicHistory.gate work g
      (fun i => row (work,base,g,d) i.val) (fun i => column (work,base,g,d) i.val) := by
  cases g with
  | hadamard j =>
    rw [QuantumGateScalarReduction.hadamard_entry]
    have hh := allWork_single (work,base,.hadamard j,d) (by change (0 : ℕ) ≠ 2; decide)
    by_cases h : allWork (work,base,.hadamard j,d)=true
    · have hv : entry (work,base,.hadamard j,d) = QuantumAlgebraicHistory.hadamard
          (row (work,base,.hadamard j,d) (left (work,base,.hadamard j,d)))
          (column (work,base,.hadamard j,d) (left (work,base,.hadamard j,d))) := by
        unfold entry
        rw [ite_eq_left h]
        exact ite_eq_left rfl
      refine hv.trans ?_
      symm
      exact ite_eq_left (hh.mp h)
    · have hv : entry (work,base,.hadamard j,d)=rat 0 := ite_eq_right h
      refine hv.trans ?_
      symm
      exact ite_eq_right (mt hh.mpr h)
  | phaseT j =>
    rw [QuantumGateScalarReduction.phaseT_entry]
    have hh := allWork_single (work,base,.phaseT j,d) (by change (1 : ℕ) ≠ 2; decide)
    by_cases h : allWork (work,base,.phaseT j,d)=true
    · have hv : entry (work,base,.phaseT j,d) = QuantumAlgebraicHistory.phaseT
          (row (work,base,.phaseT j,d) (left (work,base,.phaseT j,d)))
          (column (work,base,.phaseT j,d) (left (work,base,.phaseT j,d))) := by
        unfold entry
        rw [ite_eq_left h]
        rw [ite_eq_right (by change (1 : ℕ) ≠ 0; decide)]
        exact ite_eq_left rfl
      refine hv.trans ?_
      symm
      exact ite_eq_left (hh.mp h)
    · have hv : entry (work,base,.phaseT j,d)=rat 0 := ite_eq_right h
      refine hv.trans ?_
      symm
      exact ite_eq_right (mt hh.mpr h)
  | controlledNot a b =>
    have hh := allWork_cnot work base a b d
    unfold entry QuantumAlgebraicHistory.gate
    simp only [gateTag]
    by_cases h : allWork (work,base,.controlledNot a b,d)=true
    · simp [h,hh.mp h]
    · have hn := mt hh.mpr h
      simp [h,hn]

end ContinuumCoulomb.QuantumGateEntryProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelData
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history word is obtained by zipping its literal
site-number list with a fixed local pattern. No spectator basis occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open scoped Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem local_word_at {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (w : Fin (n+m) → Fin 4) (i : Fin n) :
    QuantumPaddedLocal.word S e m w (e i).val=QuantumPaddedPauli.paddedWord n m w i := by
  simp only [QuantumPaddedLocal.word,qmaPauliExtend,dite_eq_left (e i).property]
  apply congrArg (QuantumPaddedPauli.paddedWord n m w)
  apply e.injective
  rw [Equiv.apply_symm_apply]

private theorem map_get_zip {α β γ : Type} (xs : List α) (g : α → β)
    (f : Fin xs.length → γ) :
    (List.ofFn (fun i => (g (xs.get i),f i)))= (xs.map g).zip (List.ofFn f) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem source_tag (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT p.1) (word c hT p) =
      (QuantumOrderedSupport.encodedSites c hT p.1).zip
        (localLabels (QuantumOrderedSupport.sites c hT p.1).length
          (6-(QuantumOrderedSupport.sites c hT p.1).length)
          (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)) := by
  let xs := QuantumOrderedSupport.sites c hT p.1
  let e := QuantumOrderedSupport.supportEquiv c hT p.1
  let v : QuantumOrderedSupport.Qubit c → Fin 4 := word c hT p
  let w := widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2
  have hw (i : Fin xs.length) :
      v (xs.get i)=
        QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i := by
    have hi := QuantumOrderedSupport.supportEquiv_apply c hT p.1 i
    change (e i).val=xs.get i at hi
    rw [← hi]
    exact local_word_at _ e _ w i
  change xs.map (fun i => (QuantumOrderedSupport.siteNumber c i,(v i).val)) = _
  calc
    _ = List.ofFn (fun i : Fin xs.length =>
        (QuantumOrderedSupport.siteNumber c (xs.get i),(v (xs.get i)).val)) :=
      (List.ofFn_getElem_eq_map xs
        (fun i => (QuantumOrderedSupport.siteNumber c i,(v i).val))).symm
    _ = List.ofFn (fun i : Fin xs.length =>
        (QuantumOrderedSupport.siteNumber c (xs.get i),
          (QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i).val)) := by
      apply congrArg List.ofFn
      funext i
      rw [hw]
    _ = _ := map_get_zip xs (QuantumOrderedSupport.siteNumber c)
      (fun i => (QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i).val)

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity local history packets: sparse numeric labels and sampled
algebraic coefficients share exactly the same fixed Pauli-word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem uniformPacket_eq (x : Input) (h : x.2.1.length ≤ 6) :
    uniformPacket x=packet x.2.1.length (6-x.2.1.length) x := by
  generalize hn : x.2.1.length=n at *
  interval_cases n <;> simp only [uniformPacket,hn] <;> norm_num

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelMeaning
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every emitted local packet entry is the actual padded history word
and its sampled coefficient, in the supplied support-list order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.finDecision
private theorem labels_eq_zip (n m : ℕ) (w : Fin (n+m) → Fin 4)
    (xs : List ℕ) (hlen : xs.length=n) :
    labels n m w xs = xs.zip (localLabels n m w) := by
  apply List.ext_getElem
  · simp [labels,localLabels,hlen]
  · intro i hi hj
    have hi' : i < xs.length := by simpa only [labels,List.length_ofFn,← hlen] using hi
    simp only [labels,localLabels,List.getElem_ofFn,List.getElem_zip]
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi',Option.getD_some]

theorem entry_source (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (w : Fin ((QuantumOrderedSupport.sites c hT a).length+
      (6-(QuantumOrderedSupport.sites c hT a).length)) → Fin 4) :
    entry (QuantumOrderedSupport.sites c hT a).length
      (6-(QuantumOrderedSupport.sites c hT a).length) w
      (k,QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)) =
    let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
    (QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p),sampledWeight k c hT p) := by
  let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
  have hw : widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2 = w :=
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).apply_symm_apply w
  apply Prod.ext
  · change labels _ _ w (QuantumOrderedSupport.encodedSites c hT a) = _
    rw [labels_eq_zip _ _ w _ (by simp only [QuantumOrderedSupport.encodedSites,List.length_map])]
    have hs := source_tag c hT p
    change QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p) =
      (QuantumOrderedSupport.encodedSites c hT a).zip (localLabels _ _
        (widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2)) at hs
    rw [hw] at hs
    exact hs.symm
  · change sample k (QuantumPaddedTable.coefficient _ _ _ w) = _
    unfold sampledWeight
    apply congrArg (sample k)
    unfold scalar
    rw [hw]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal concatenation of fixed-width history packets is an exact
enumeration of the actual padded history family.  The local pattern order is
allowed to depend on the support width; its explicit bijection is retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

theorem packet_reindex (n : ℕ) (hn : n ≤ 6) (x : Input) :
    packet n (6-n) x = List.ofFn (fun j => entry n (6-n) (packetPatterns n hn j) x) := by
  simp only [packet,enumerate,List.map_ofFn,Function.comp_def]
  rw [List.ofFn_congr (pattern_card n hn)]
  rfl

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.tableFinDecision
theorem sourceEntries_table (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    sourceEntries k c hT =
      QuantumOrderedLabelTable.table (sourceTerms c hT)
        (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
        (fun p => QuantumOrderedSupport.sites c hT p.1)
        (sourceWord c hT) (sampledWeight k c hT) := by
  unfold sourceEntries QuantumOrderedLabelTable.table sourceTerms
  simp only [Equiv.trans_apply]
  let entryAt (j : Fin (QuantumOrderedSourceIndex.referenceCount c) ×
      Fin QuantumOrderedSourceIndex.patternCount) :=
    let p := Equiv.prodShear (QuantumOrderedSourceIndex.reference c)
      (fun i => (packetPatterns _ (QuantumOrderedSupport.sites_length c hT
        (QuantumOrderedSourceIndex.reference c i))).trans
          (widthIndex _ (QuantumOrderedSupport.sites_length c hT
            (QuantumOrderedSourceIndex.reference c i))).symm) j
    (QuantumOrderedLabelData.tag
      (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
      (QuantumOrderedSupport.sites c hT p.1) (sourceWord c hT p),sampledWeight k c hT p)
  change _ = List.ofFn (fun i => entryAt (finProdFinEquiv.symm i))
  rw [QuantumOrderedLabelTable.product_table entryAt]
  dsimp only [entryAt]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  let a := QuantumOrderedSourceIndex.reference c i
  have hn := QuantumOrderedSupport.sites_length c hT a
  rw [uniformPacket_eq _ (by
    simpa only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map] using hn)]
  rw [show (sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)).2.1.length =
    (QuantumOrderedSupport.sites c hT a).length by
      simp only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map,a]]
  change packet (QuantumOrderedSupport.sites c hT a).length
    (6-(QuantumOrderedSupport.sites c hT a).length) (sourceInput k c hT a) = _
  rw [packet_reindex _ hn]
  apply congrArg List.ofFn
  funext j
  have h := entry_source k c hT a (packetPatterns _ hn j)
  simpa only [sourceInput,sourceWord,Equiv.trans_apply,Equiv.prodShear_apply,
    Equiv.symm_apply_apply,
    QuantumOrderedSourceIndex.qubits_index] using h

theorem sourceEntries_length (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    (sourceEntries k c hT).length = QuantumOrderedSourceIndex.termCount c := by
  rw [sourceEntries_table]
  simp only [QuantumOrderedLabelTable.table,List.length_ofFn,
    QuantumOrderedSourceIndex.termCount]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal natural row/column tags for the sparse sweep.  The
three gates of each wire transfer carry the same column; the original gate
keeps its proved arrival column. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSweepCells
open QuantumCircuitCode

theorem transfer_columns {width work : ℕ}
    (l r : Fin (width+1) → Fin (work+1)) (xs : List (Fin (width+1))) :
    (qmaColumnTransfer l r xs).map (fun p => p.2.val)=
      repeatColumns (xs.map Fin.val) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [qmaColumnTransfer,List.flatMap_cons,List.map_append,
      qmaWireSwapGates,List.map_cons,List.map_nil,repeatColumns]
    simpa only [repeatColumns,qmaColumnTransfer,qmaWireSwapGates,List.map_cons,List.map_nil]
      using congrArg (fun ys => [j.val,j.val,j.val]++ys) ih

theorem columns_actual (width order : ℕ) :
    (List.ofFn (qmaSweepOrder width order)).map Fin.val=columns width order := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,columns,List.length_range]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn,columns,List.getElem_range,
      sweepIndex_value]

theorem arrival_actual (width order : ℕ) (g : QMAGate) :
    (qmaGateArrivalColumn width (qmaSweepOrder width order) g).val=
      sweepIndex width order (rowCut width order g-1) := by
  rw [qmaGateArrivalColumn,sweepIndex_value]
  simp only [qmaGateArrivalIndex,rowCut_eq]

theorem rowColumns_actual (width work order : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (g : QMAGate) :
    (qmaTaggedRowStage width work l r (qmaSweepOrder width order) g).map
        (fun p => p.2.val)=rowColumns width order g := by
  simp only [qmaTaggedRowStage,List.map_append,List.map_cons,List.map_nil,
    transfer_columns,List.map_take,List.map_drop,columns_actual,rowCut_eq,
    arrival_actual,rowColumns]

theorem rowCells_actual (rows width start : ℕ) (hs : start < rows) (g : QMAGate) :
    ((qmaTaggedRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width ⟨start,by omega⟩)
      (qmaGridQubit rows width ⟨start+1,by omega⟩)
      (qmaSweepOrder width (rows-1-start)) g).map
        (fun p => (p.1,((⟨start,by omega⟩ : Fin (rows+1)),p.2)))).map
        (fun p => (p.2.1.val,p.2.2.val))=rowCells rows width start g := by
  simpa only [List.map_map,Function.comp_def,rowCells] using
    congrArg (List.map (fun j => (start,j)))
      (rowColumns_actual width (qmaGridWork rows width) (rows-1-start)
        (qmaGridQubit rows width ⟨start,by omega⟩)
        (qmaGridQubit rows width ⟨start+1,by omega⟩) g)

theorem sweepCells_cons (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate) :
    sweepCells rows width start (g::gs)=
      rowCells rows width start g++sweepCells rows width (start+1) gs := by
  simp only [sweepCells,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
    List.flatMap_map,readGate,List.drop_zero,List.headD_cons,Nat.add_zero,List.drop_succ_cons]
  congr 1
  have h : (fun i => rowCells rows width (start+Nat.succ i)
      ((gs.drop i).headD (.hadamard 0)))=
      (fun i => rowCells rows width (start+1+i) ((gs.drop i).headD (.hadamard 0))) := by
    funext i
    congr 1
    omega
  rw [h]

theorem sweepCells_actual (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaTaggedSweepFrom rows width start gs h).map
      (fun p => (p.2.1.val,p.2.2.val))=sweepCells rows width start gs := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    rw [sweepCells_cons]
    simp only [qmaTaggedSweepFrom,List.map_append]
    rw [rowCells_actual rows width start hs g,ih]

theorem value_actual (c : QMACircuit) :
    value c=(qmaSparseTags c).map (fun p => (p.2.1.val,p.2.2.val)) :=
  (sweepCells_actual _ _ _ _ _).symm

theorem value_length (c : QMACircuit) :
    (value c).length=(qmaSparseCircuit c).gates.length := by
  rw [value_actual,List.length_map,qmaSparseTags_length]

end ContinuumCoulomb.QuantumSweepCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural cell lookups for the actual sparse history.  The reference
lookup uses the same time-grouped descriptors as the sampled Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open QuantumHistoryDescriptors QuantumOrderedSourceIndex

theorem gateCell_actual (c : QMACircuit) (t : Fin (qmaSparseCircuit c).gates.length) :
    gateCell c t.val=encodeCell (qmaSparseGateCell c t) := by
  unfold gateCell
  rw [List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by rw [QuantumSweepCells.value_length]; exact t.isLt)]
  simp only [QuantumSweepCells.value_actual,List.getElem_map,encodeCell,
    qmaSparseGateCell,qmaSparseCell,Fin.val_cast,Option.getD_some]

theorem referenceCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :
    referenceCell c i.val=encodeCell (qmaOrderedSparseReferenceCell c hT i) := by
  unfold referenceCell
  rw [orderedAt_actual _ hT i,time_encode _ hT]
  exact gateCell_actual c _

theorem qubitCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (q : QuantumOrderedSupport.Qubit (qmaSparseCircuit c)) :
    qubitCell c (QuantumOrderedSupport.siteNumber (qmaSparseCircuit c) q)=
      encodeCell (qmaOrderedQubitCell c hT q) := by
  rcases q with i | (b | w)
  · have hi : i.val < referenceWork (qmaSparseCircuit c)+1 := by
      simpa only [referenceWork_eq] using i.isLt
    simp only [qubitCell,QuantumOrderedSupport.siteNumber,hi,ite_true, if_true,
      qmaOrderedQubitCell,Sum.elim_inl]
    exact referenceCell_actual c hT i
  · change (if qmaHistoryReferenceWork (qmaSparseCircuit c)+1+b.val<
        qmaHistoryReferenceWork (qmaSparseCircuit c)+1 then _ else _)=_
    rw [ite_eq_right (by omega)]
    simp only [QuantumOrderedSupport.siteNumber,referenceWork_eq,Nat.add_sub_cancel_left]
    change (if b.val<(qmaSparseCircuit c).gates.length+2 then _ else _)=_
    rw [ite_eq_left b.isLt]
    exact gateCell_actual c (qmaClockAnchorIndex _ hT b)
  · have hnot : ¬qmaHistoryReferenceWork (qmaSparseCircuit c)+1+
        ((qmaSparseCircuit c).gates.length+2)+w.val<
        referenceWork (qmaSparseCircuit c)+1 := by rw [referenceWork_eq]; omega
    have hd : qmaHistoryReferenceWork (qmaSparseCircuit c)+1+
        ((qmaSparseCircuit c).gates.length+2)+w.val-
        (referenceWork (qmaSparseCircuit c)+1)=
        (qmaSparseCircuit c).gates.length+2+w.val := by rw [referenceWork_eq]; omega
    simp only [qubitCell,QuantumOrderedSupport.siteNumber,hnot,ite_false, if_false,hd]
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    rfl

theorem termCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c))) :
    termCell c ((reference (qmaSparseCircuit c)).symm a).val=
      encodeCell (qmaOrderedTermCell c hT a) := by
  cases a with
  | inl i =>
    change referenceCell c (if i.val < referenceWork (qmaSparseCircuit c)+1
      then i.val else _)=_
    rw [ite_eq_left (by simpa only [referenceWork_eq] using i.isLt)]
    exact referenceCell_actual c hT i
  | inr i =>
    change referenceCell c (if qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val<
      qmaHistoryReferenceWork (qmaSparseCircuit c)+1
      then qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val
      else qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val-
        (qmaHistoryReferenceWork (qmaSparseCircuit c)+1))=_
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    exact referenceCell_actual c hT i.castSucc

theorem qubitCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    qubitCells c=List.ofFn (fun i : Fin (qubitCount (qmaSparseCircuit c)) =>
      encodeCell (qmaOrderedQubitCell c hT (qubits (qmaSparseCircuit c) i))) := by
  apply List.ext_getElem
  · simp only [qubitCells,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [qubitCells,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    let j : Fin (qubitCount (qmaSparseCircuit c)) := ⟨i,by
      simpa only [List.length_ofFn] using hj⟩
    have he := congrFun (qubits_index (qmaSparseCircuit c)) (qubits (qmaSparseCircuit c) j)
    simp only [QuantumOrderedLabelTable.index,Equiv.symm_apply_apply] at he
    simpa only [←he] using qubitCell_actual c hT (qubits (qmaSparseCircuit c) j)

theorem referenceCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    referenceCells c=List.ofFn (fun i : Fin (referenceCount (qmaSparseCircuit c)) =>
      encodeCell (qmaOrderedTermCell c hT (reference (qmaSparseCircuit c) i))) := by
  apply List.ext_getElem
  · simp only [referenceCells,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [referenceCells,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    let j : Fin (referenceCount (qmaSparseCircuit c)) := ⟨i,by
      simpa only [List.length_ofFn] using hj⟩
    simpa only [Equiv.symm_apply_apply] using
      termCell_actual c hT (reference (qmaSparseCircuit c) j)

private theorem sourceTerms_first (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (referenceCount c*patternCount)) :
    (QuantumPaddedLabelProgram.sourceTerms c hT i).1=
      reference c (finProdFinEquiv.symm i).1 := by
  simp only [QuantumPaddedLabelProgram.sourceTerms,Equiv.trans_apply,
    Equiv.prodShear_apply]

private theorem anchors_source (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c) → ℕ × ℕ) :
    QuantumOrderedCellProgram.anchors patternCount
      (List.ofFn (fun i : Fin (referenceCount c) => a (reference c i)))=
      List.ofFn (fun i : Fin (referenceCount c*patternCount) =>
        a (QuantumPaddedLabelProgram.sourceTerms c hT i).1) := by
  rw [QuantumOrderedCellProgram.anchors_ofFn]
  rw [←QuantumOrderedLabelTable.product_table (fun p :
    Fin (referenceCount c) × Fin patternCount => a (reference c p.1))]
  apply congrArg List.ofFn
  funext i
  rw [sourceTerms_first]

theorem value_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    value c=QuantumOrderedCellTable.table (qubits (qmaSparseCircuit c))
      (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
      (fun q => encodeCell (qmaOrderedQubitCell c hT q))
      (fun a => encodeCell (qmaOrderedTermCell c hT a.1)) := by
  apply Prod.ext
  · exact qubitCells_actual c hT
  · change QuantumOrderedCellProgram.anchors patternCount (referenceCells c)=_
    rw [referenceCells_actual c hT]
    dsimp only [QuantumOrderedCellTable.table]
    exact anchors_source (qmaSparseCircuit c) hT (fun a => encodeCell (qmaOrderedTermCell c hT a))

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary-bounded equality checks for the clock/work registers. A single
specified bit may be flipped, as required by the propagation delta. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryComparison
open ExactQuantumFactoring.BitStackProgram QuantumHistoryBitProgram

theorem value_iff (x : Input) : value x=true ↔
    ∀ i : Fin x.1, row x.2.2.2.2 (x.2.1+i.val) =
      if x.2.2.1=true ∧ x.2.1+i.val=x.2.2.2.1 then
        Equiv.swap (0:Fin 2) 1 (column x.2.2.2.2 (x.2.1+i.val))
      else column x.2.2.2.2 (x.2.1+i.val) := by
  simp only [value,List.all_map,List.all_eq_true,List.mem_range,
    Function.comp_apply,id_eq,point,decide_eq_true_eq]
  exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩

theorem no_flip_iff (count base target : ℕ) (d : Data) :
    value (count,base,false,target,d)=true ↔
      ∀ i : Fin count, row d (base+i.val)=column d (base+i.val) := by
  rw [value_iff]
  simp only [Bool.false_eq_true,false_and,ite_false, if_false]

theorem value_equiv_iff {ι : Type} {count : ℕ} (e : ι ≃ Fin count)
    (base target : ℕ) (d : Data) :
    value (count,base,false,target,d)=true ↔
      (fun i => row d (base+(e i).val))=(fun i => column d (base+(e i).val)) := by
  rw [no_flip_iff,funext_iff]
  constructor
  · intro h i
    exact h (e i)
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact h j

theorem value_flip_iff {ι : Type} [DecidableEq ι] {count : ℕ} (e : ι ≃ Fin count)
    (base : ℕ) (q : ι) (d : Data) :
    value (count,base,true,base+(e q).val,d)=true ↔
      (fun i => row d (base+(e i).val))=
        qmaBitFlip q (fun i => column d (base+(e i).val)) := by
  rw [value_iff,funext_iff]
  have hv (i : ι) (hi : i≠q) : (e i).val≠(e q).val :=
    fun h => hi (e.injective (Fin.ext h))
  constructor
  · intro h i
    by_cases hi : i=q
    · subst i
      simpa [qmaBitFlip] using h (e q)
    · simpa [qmaBitFlip,hi,hv i hi] using h (e i)
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    by_cases hj : j=q
    · subst j
      simpa [qmaBitFlip] using h q
    · simpa [qmaBitFlip,hj,hv j hj] using h j

end ContinuumCoulomb.QuantumHistoryComparison

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDelta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact register evaluation of the propagation delta.  The equality scans
are bounded by the unary circuit size; every bit is read from the supplied
local support table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDelta
open QuantumAlgebraicScalar QuantumHistoryDescriptors QuantumHistoryBitProgram
open QuantumHistoryDiagonal QuantumHistorySiteProgram

theorem qubitEquiv_val (c : QMACircuit) (q : QMACircuitQubit c) :
    (qubitEquiv c q).val=distributedNumber c q := by
  cases q <;> rfl

theorem readRow_eq (c : QMACircuit) (d : Data) (q : QMACircuitQubit c) :
    readRow c d q=row d (referenceWork c+1+(qubitEquiv c q).val) := by
  rw [qubitEquiv_val]
  exact congrArg (row d) (number_inr c q)

theorem readColumn_eq (c : QMACircuit) (d : Data) (q : QMACircuitQubit c) :
    readColumn c d q=column d (referenceWork c+1+(qubitEquiv c q).val) := by
  rw [qubitEquiv_val]
  exact congrArg (column d) (number_inr c q)

theorem guard_iff (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    guard c t.val d=true ↔
      QMAClockGuard c.gates.length t (readRow c d ∘ Sum.inl) ∧
        readRow c d (.inl (qmaClockMiddle c.gates.length t))=0 := by
  have he : (clockRow c d t.val=1 ∧ clockRow c d (t.val+2)=0 ∧
      clockRow c d (t.val+1)=0) ↔
      QMAClockGuard c.gates.length t (readRow c d ∘ Sum.inl) ∧
        readRow c d (.inl (qmaClockMiddle c.gates.length t))=0 := by
    simp only [QMAClockGuard,Function.comp_apply,readRow,QuantumOrderedSupport.siteNumber,
      clockRow,referenceWork_eq,qmaClockLeft,qmaClockRight,qmaClockMiddle,and_assoc]
  exact ⟨fun h => he.mp (of_decide_eq_true h),fun h => decide_eq_true (he.mpr h)⟩

theorem flipped_iff (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    flipped c t.val d=true ↔ readRow c d=
      qmaBitFlip (.inl (qmaClockMiddle c.gates.length t)) (readColumn c d) := by
  have h := QuantumHistoryComparison.value_flip_iff (qubitEquiv c)
    (referenceWork c+1) (.inl (qmaClockMiddle c.gates.length t)) d
  have he : (qubitEquiv c (.inl (qmaClockMiddle c.gates.length t))).val=t.val+1 := rfl
  change QuantumHistoryComparison.value
    (c.gates.length+2+(c.work+1),referenceWork c+1,true,referenceWork c+1+(t.val+1),d)=true ↔ _
  simpa only [he,← readRow_eq,← readColumn_eq] using h

theorem sameClock_iff (c : QMACircuit) (d : Data) :
    sameClock c d=true ↔ readRow c d ∘ Sum.inl=readColumn c d ∘ Sum.inl := by
  have h := QuantumHistoryComparison.value_equiv_iff
    (Equiv.refl (Fin (c.gates.length+2))) (referenceWork c+1) 0 d
  simpa only [sameClock,Equiv.refl_apply,readRow,readColumn,
    QuantumOrderedSupport.siteNumber,referenceWork_eq,Function.comp_def] using h

theorem gate_entry (c : QMACircuit) (t : ℕ) (d : Data) :
    QuantumGateEntryProgram.entry
      (c.work,referenceWork c+1+(c.gates.length+2),gateAt (c,t),d)=
      QuantumAlgebraicHistory.gate c.work (gateAt (c,t))
        (readRow c d ∘ Sum.inr) (readColumn c d ∘ Sum.inr) := by
  rw [QuantumGateEntryProgram.entry_eq]
  rfl

theorem entry_actual (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    entry c t.val d=QuantumAlgebraicHistory.delta c t (readRow c d) (readColumn c d) := by
  unfold entry QuantumAlgebraicHistory.delta QuantumAlgebraicHistory.identity
  rw [gate_entry]
  simp only [flipped_iff c t d,sameClock_iff c d,gateAt]
  by_cases hg : guard c t.val d=true
  · have hh := (guard_iff c t d).mp hg
    simp only [hg,hh,and_self,ite_true, if_true]
  · have hh := mt (guard_iff c t d).mpr hg
    simp only [hg,hh,Bool.false_eq_true,ite_false, if_false]

end ContinuumCoulomb.QuantumHistoryDelta

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortChainActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal port-chain program returns precisely the sites used by the
physical subdivision construction, including its two endpoint centers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortChainProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem lookup_support {u v : Pair} (p : qmaSquareGrid.Walk u v) (k : ℕ)
    (hk : k ≤ p.length) : QuantumPathVisitProgram.lookup p.support k = p.getVert k := by
  unfold QuantumPathVisitProgram.lookup
  rw [List.headD_eq_head?_getD,List.head?_drop,← p.getVert_eq_support_getElem? hk]
  rfl

theorem point_eq (xs : List Pair) (p : ℕ → Pair) (L : ℕ)
    (hlen : xs.length = L+1) (hp : ∀ i ≤ L, QuantumPathVisitProgram.lookup xs i = p i)
    (k : ℕ) (hk : k ≤ 2*L+1) : point xs k = qmaPortChain p L k := by
  have hlen' : xs.length-1 = L := by omega
  unfold point
  rw [hlen']
  unfold qmaPortChain
  split_ifs with hzero hlast
  · rw [hp 0 (by omega)]
  · rw [hp L le_rfl]
  · have hi := qmaPortNeighborIndex_bounds (L := L) (by omega : 0 < k)
      (by omega : k < 2*L+1)
    unfold qmaRoutePort
    rw [hp _ hi.1,hp _ hi.2]

theorem value_support {u v : Pair} (p : qmaSquareGrid.Walk u v) :
    value p.support = (List.range (2*p.length+2)).map (qmaPortChain p.getVert p.length) := by
  unfold value
  rw [p.length_support]
  simp only [Nat.add_sub_cancel]
  apply List.map_congr_left
  intro k hk
  have hk' : k < 2*p.length+2 := List.mem_range.mp hk
  exact point_eq p.support p.getVert p.length p.length_support
    (lookup_support p) k (by omega)

theorem routed_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    routed A B ((labels e).val,QuantumRoutingInputProgram.actualData M labels) =
      (List.range (2*(M.withOrdinalSlots labels).coarseLength hd e+2)).map
        (qmaPortChain ((M.withOrdinalSlots labels).coarseRoute hd e)
          ((M.withOrdinalSlots labels).coarseLength hd e)) := by
  exact (congrArg value (QuantumRoutingInputProgram.path_actual M labels hA hd e)).trans
    (value_support ((M.withOrdinalSlots labels).bufferedPath hd e).val)

end ContinuumCoulomb.QuantumPortChainProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal enumeration of every coarse route and source center. These are
the exact lists consumed by the finite crossing and permission tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingFamily
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingInputProgram

theorem placed_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    placed A B (q.val,actualData M labels) = (M.withOrdinalSlots labels).placedVertex q := by
  unfold placed actualData
  rw [QuantumSpatialSlotProgram.fineSite_actual M labels q]
  rfl

theorem positions_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) :
    positions A B (actualData M labels) = List.ofFn (M.withOrdinalSlots labels).placedVertex := by
  apply List.ext_getElem
  · simp only [positions,actualData,List.length_map,List.length_range,List.length_ofFn]
    rfl
  · intro i hi hj
    have hi' : i < M.n := by simpa only [List.length_ofFn,
      QMASpatialExchangeModel.withOrdinalSlots] using hj
    simp only [positions,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact placed_actual M labels ⟨i,hi'⟩

theorem coarse_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    coarse A B (actualData M labels) = List.ofFn (fun e : Fin m =>
      ((M.withOrdinalSlots labels).bufferedPath hd (labels.symm e)).val.support) := by
  apply List.ext_getElem
  · simp only [coarse,actualData,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    have h := path_actual M labels hA hd (labels.symm ⟨i,hi'⟩)
    simpa only [coarse,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      Equiv.apply_symm_apply] using h

private theorem support_range {u v : Pair} (p : qmaSquareGrid.Walk u v) :
    p.support = (List.range (p.length+1)).map p.getVert := by
  apply List.ext_getElem
  · simp only [p.length_support,List.length_map,List.length_range]
  · intro i hi hj
    have hi' : i ≤ p.length := by
      simp only [p.length_support] at hi
      omega
    simpa only [List.getElem_map,List.getElem_range] using
      (p.getVert_eq_support_getElem hi').symm

theorem table_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    table A B (actualData M labels) =
      (List.ofFn (M.withOrdinalSlots labels).placedVertex,
        List.ofFn (fun e : Fin m =>
          ((M.withOrdinalSlots labels).portRouteData hA hd).routeList (labels.symm e))) := by
  unfold table
  rw [positions_actual,coarse_actual M labels hA hd]
  apply congrArg (Prod.mk _)
  apply congrArg List.ofFn
  funext e
  exact support_range ((M.withOrdinalSlots labels).bufferedPath hd (labels.symm e)).val

end ContinuumCoulomb.QuantumRoutingFamily

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialInputTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed fork-state/cell tape is exactly the array of the spatial
model. Only cells at actual spin indices are read. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialInputTape
open QuantumForkList QuantumForkGridProgram QuantumRouteCode

private theorem iterate_coordinates {rows width : ℕ} (N : ℚ) (s : State)
    (cell : ℕ → QMAGridCell rows width) (k : ℕ) :
    iterateCell N k s (coordinates ∘ cell) = coordinates ∘ iterateCell N k s cell := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext v
    simp only [iterateCell,nextCell,Function.comp_apply]
    split <;> exact congrFun ih _

theorem state_eq {rows width A D : ℕ} (I : SpatialInput rows width A D) :
    (output D (input I)).1 = I.state := output_state D (input I)

private theorem prepare_represents_input {rows width A D : ℕ}
    (I : SpatialInput rows width A D) :
    Represents (prepare (input I)).2 (coordinates ∘ initialCell I.n I.bonds I.cell) := by
  intro v hv
  change v < I.n+2*I.bonds.length at hv
  change lookup (initialCells (I.n,I.bonds,
    List.ofFn (fun v : Fin I.n => coordinates (I.cell v.val)))) v = _
  rw [lookup_initialCells _ v hv]
  change initialCell I.n I.bonds
    (lookup (List.ofFn (fun v : Fin I.n => coordinates (I.cell v.val)))) v = _
  by_cases h : v < I.n
  · simp only [Function.comp_apply,initialCell,h,ite_true, if_true]
    exact QuantumOrdinalProgram.lookup_ofFn _ ⟨v,h⟩
  · have hb : v-I.n < 2*I.bonds.length := by
      change v < I.n+2*I.bonds.length at hv
      omega
    have he := initialEndpoint_bound I.n I.bonds I.bounded (v-I.n) hb
    simp only [initialCell,h,ite_false, if_false,Function.comp_apply]
    exact QuantumOrdinalProgram.lookup_ofFn _ ⟨_,he⟩

theorem output_represents_input {rows width A D : ℕ}
    (I : SpatialInput rows width A D) :
    Represents (output D (input I)) (coordinates ∘ I.cells) := by
  have h := run_represents D (prepare (input I)) (initial_validPorts _ _ _ _)
    (coordinates ∘ initialCell I.n I.bonds I.cell) (prepare_represents_input I)
  change Represents (output D (input I))
    (iterateCell I.precision D (initial I.n I.bonds I.constant I.precision)
      (coordinates ∘ initialCell I.n I.bonds I.cell)) at h
  rw [iterate_coordinates] at h
  exact h

theorem output_eq {rows width A D : ℕ} (I : SpatialInput rows width A D) :
    output D (input I) =
      (I.state,List.ofFn (fun v : Fin I.state.1 => coordinates (I.cells v.val))) := by
  apply Prod.ext
  · exact state_eq I
  · apply List.ext_getElem
    · rw [List.length_ofFn,output_length,state_eq]
    · intro i hi hj
      have hi' : i < I.state.1 := by simpa only [List.length_ofFn] using hj
      have h := output_represents_input I i (by rwa [state_eq])
      simpa only [lookup,List.headD_eq_head?_getD,List.head?_drop,
        List.getElem?_eq_getElem hi,Option.getD_some,Function.comp_apply,
        List.getElem_ofFn] using h

theorem routing_eq {rows width A D : ℕ} (I : SpatialInput rows width A D) :
    QuantumForkRoutingData.value (output D (input I)) =
      QuantumRoutingInputProgram.actualData I.model (Equiv.refl _) := by
  rw [output_eq]
  exact QuantumForkRoutingData.value_spatialModel I.state I.validPorts I.state_bounded
    I.state_noLoops I.cells (spatialDensity A D) I.state_density I.state_degree I.state_locality

end ContinuumCoulomb.QuantumSpatialInputTape

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialRoutingTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal initial/fork program supplies the same source-center and
coarse-path arrays used by the actual lattice crossing construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialRoutingTape
open QuantumForkList ExactQuantumFactoring.BitStackProgram

theorem value_actual {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) :
    value A D (QuantumSpatialInputTape.input I) =
      (List.ofFn I.model.placedVertex,
        List.ofFn (fun e : I.model.Term => (I.model.portRouteData hA I.model_degree).routeList e)) := by
  unfold value
  rw [QuantumSpatialInputTape.routing_eq]
  have h := QuantumRoutingFamily.table_actual I.model (Equiv.refl _) hA I.model_degree
  exact h

end ContinuumCoulomb.QuantumSpatialRoutingTape

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortScheduleTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed port paths decorate the actual full bond list with its
remaining subdivision work. Erasing that work leaves the same Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortScheduleTape
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

theorem entries_ofFn {m : ℕ} (bs : Fin m → Bond) (ps : Fin m → List Pair) :
    entries (List.ofFn bs,List.ofFn ps) = List.ofFn (fun i => ((ps i).length-1,bs i)) := by
  apply List.ext_getElem
  · simp only [entries,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    simp only [entries,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      entry,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn,
      dite_eq_left hi',Option.getD_some]

theorem allRouted_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    QuantumPortChainProgram.allRouted A B (QuantumRoutingInputProgram.actualData M labels) =
      List.ofFn (fun i : Fin m =>
        (List.range (2*(M.withOrdinalSlots labels).coarseLength hd (labels.symm i)+2)).map
          (qmaPortChain ((M.withOrdinalSlots labels).coarseRoute hd (labels.symm i))
            ((M.withOrdinalSlots labels).coarseLength hd (labels.symm i)))) := by
  apply List.ext_getElem
  · simp only [QuantumPortChainProgram.allRouted,QuantumRoutingInputProgram.actualData,
      List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    have h := QuantumPortChainProgram.routed_actual M labels hA hd (labels.symm ⟨i,hi'⟩)
    simpa only [QuantumPortChainProgram.allRouted,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,Equiv.apply_symm_apply] using h

end ContinuumCoulomb.QuantumPortScheduleTape

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPackedSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packing a finite exchange graph with a work counter retains its endpoints
and work exactly. This bridges the literal schedule to the geometric one. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPackedSchedule
open QuantumListSchedule
open scoped Classical

theorem layout_represents (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding ⟨G,work⟩ Γ) :
    QuantumListRouteProgram.Represents (layout G labels work P) (valid G labels work)
      ((scheduleRelabel G labels work).symm.transport P) := by
  constructor
  · rfl
  · apply List.ext_getElem
    · simp only [layout,List.length_ofFn,schedule,graph,state]
    · intro i hi hj
      have hi' : i < m := by simpa only [layout,List.length_ofFn] using hi
      simp only [layout,List.getElem_ofFn]
      have hw := (scheduleRelabel G labels work).work
        (⟨i,by simpa only [state,List.length_ofFn] using hi'⟩ :
          (schedule (state G labels work) (valid G labels work)).graph.Edge)
      rw [hw]
      rfl

end ContinuumCoulomb.QuantumPackedSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortScheduleActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed schedule has precisely the coefficients, work counts and
physical port paths of the proved spatial construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortScheduleActual
open QuantumForkList QuantumRouteCode QuantumPortScheduleTape

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)

theorem bonds_ofFn : fullList I.state = List.ofFn (fun e : I.model.Term =>
    ((I.model.left e).val,(I.model.right e).val,I.model.weight e)) := by
  change fullList I.state = List.ofFn (fun i => (fullList I.state).get i)
  exact (List.ofFn_get (fullList I.state)).symm

include hA in
theorem entries_actual :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1.2.2 =
      List.ofFn (fun e : I.model.Term =>
        (I.model.coarseLength I.model_degree e,
          (I.model.left e).val,(I.model.right e).val,I.model.weight e)) := by
  change entries (fullList (tape I).1,
    QuantumRoutingFamily.coarse (spatialDensity A D) (27*spatialDensity A D)
      (QuantumForkRoutingData.value (tape I))) = _
  rw [QuantumSpatialInputTape.state_eq,QuantumSpatialInputTape.routing_eq]
  have hp : QuantumRoutingFamily.coarse (spatialDensity A D) (27*spatialDensity A D)
      (QuantumRoutingInputProgram.actualData I.model (Equiv.refl _)) =
        List.ofFn (fun e : I.model.Term => (I.model.bufferedPath I.model_degree e).val.support) :=
    QuantumRoutingFamily.coarse_actual I.model (Equiv.refl _) hA I.model_degree
  rw [hp]
  calc
    _ = entries (List.ofFn (fun e : I.model.Term =>
        ((I.model.left e).val,(I.model.right e).val,I.model.weight e)),
        List.ofFn (fun e : I.model.Term => (I.model.bufferedPath I.model_degree e).val.support)) :=
      congrArg (fun bs => entries (bs,
        List.ofFn (fun e : I.model.Term => (I.model.bufferedPath I.model_degree e).val.support)))
        (bonds_ofFn I)
    _ = _ := by
      refine (entries_ofFn (m := (fullList I.state).length)
        (fun e => ((I.model.left e).val,(I.model.right e).val,I.model.weight e))
        (fun e => (I.model.bufferedPath I.model_degree e).val.support)).trans ?_
      apply congrArg List.ofFn
      funext e
      apply Prod.ext
      · simp only [SimpleGraph.Walk.length_support,Nat.add_sub_cancel]
        rfl
      · rfl

theorem positions_actual :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).2.1 =
      List.ofFn (fun v : Fin I.model.n => qmaExpandedPoint (I.model.placedVertex v)) := by
  change (QuantumRoutingFamily.positions (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkRoutingData.value (tape I))).map qmaExpandedPoint = _
  rw [QuantumSpatialInputTape.routing_eq]
  have hp : QuantumRoutingFamily.positions (spatialDensity A D) (27*spatialDensity A D)
      (QuantumRoutingInputProgram.actualData I.model (Equiv.refl _)) =
        List.ofFn I.model.placedVertex :=
    QuantumRoutingFamily.positions_actual I.model (Equiv.refl _)
  rw [hp,List.map_ofFn]
  rfl

include hA in
theorem paths_actual :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).2.2 =
      List.ofFn (fun e : I.model.Term =>
        (List.range (2*I.model.coarseLength I.model_degree e+2)).map
          (qmaPortChain (I.model.coarseRoute I.model_degree e)
            (I.model.coarseLength I.model_degree e))) := by
  change QuantumPortChainProgram.allRouted (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkRoutingData.value (tape I)) = _
  rw [QuantumSpatialInputTape.routing_eq]
  exact allRouted_actual I.model (Equiv.refl _) hA I.model_degree

end ContinuumCoulomb.QuantumPortScheduleActual

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortSchedulePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual computed scheduler begins with the exact spatial exchange
graph, with one work counter for each of its enumerated interactions. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPackedSchedule

theorem port_layout {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    layout M.exchangeGraph labels (M.coarseLength hd) (M.portEmbedding hA hd) =
      (state M.exchangeGraph labels (M.coarseLength hd),
        List.ofFn (fun v => qmaExpandedPoint (M.placedVertex v)),
        List.ofFn (fun i : Fin m => (List.range (2*M.coarseLength hd (labels.symm i)+2)).map
          (qmaPortChain (M.coarseRoute hd (labels.symm i)) (M.coarseLength hd (labels.symm i))))) := by
  simp only [layout,QMASpatialExchangeModel.portEmbedding,
    QMASpatialExchangeModel.portRouteData,QMAPortRouteData.toEmbedding]

end ContinuumCoulomb.QuantumPackedSchedule

namespace ContinuumCoulomb.QuantumPortSchedulePacking
open QuantumForkList QuantumPortScheduleTape QuantumPortScheduleActual

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)
include hA

theorem state_eq :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1 =
      QuantumPackedSchedule.state I.model.exchangeGraph (Equiv.refl _)
        (I.model.coarseLength I.model_degree) := by
  apply Prod.ext
  · change (tape I).1.1=I.model.n
    rw [QuantumSpatialInputTape.state_eq]
    rfl
  · apply Prod.ext
    · change (tape I).1.2.2.1=I.model.constant
      rw [QuantumSpatialInputTape.state_eq]
      rfl
    · exact entries_actual I hA

theorem layout_eq :
    value (spatialDensity A D) (27*spatialDensity A D) (tape I) =
      QuantumPackedSchedule.layout I.model.exchangeGraph (Equiv.refl _)
        (I.model.coarseLength I.model_degree) (I.model.portEmbedding hA I.model_degree) := by
  refine Eq.trans ?_ (QuantumPackedSchedule.port_layout I.model
    (m := (fullList I.state).length) (Equiv.refl _) hA I.model_degree).symm
  apply Prod.ext
  · exact state_eq I hA
  · apply Prod.ext
    · exact positions_actual I
    · exact paths_actual I hA

end ContinuumCoulomb.QuantumPortSchedulePacking

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScalarReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reindexing of the four-rational local-core sums.  This lets the
literal support-list coordinates evaluate the propagation Gram matrix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped BigOperators

private theorem scalar_add_eq (x y : Scalar) : add x y=x+y := rfl
theorem scalar_sum_eq (xs : List Scalar) : QuantumAlgebraicScalar.sum xs=xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [QuantumAlgebraicScalar.sum,ih,List.sum_cons,scalar_add_eq]

theorem scalar_finiteSum_eq {α : Type} [Fintype α] (f : α → Scalar) :
    finiteSum f=∑ a,f a := by
  rw [finiteSum,scalar_sum_eq]
  simp only [enumerate,List.map_ofFn,List.sum_ofFn]
  exact (Fintype.equivFin α).symm.sum_comp f

theorem scalar_finiteSum_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → Scalar) :
    finiteSum (fun a => f (e a))=finiteSum f := by
  rw [scalar_finiteSum_eq,scalar_finiteSum_eq]
  exact e.sum_comp f

theorem matMul_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A B : Matrix β β Scalar) :
    matMul (reindex e A) (reindex e B)=reindex e (matMul A B) := by
  funext s t
  exact scalar_finiteSum_reindex e (fun u => mul (A (e s) u) (B u (e t)))

theorem adjoint_reindex {α β : Type} (e : α ≃ β) (A : Matrix β β Scalar) :
    adjoint (reindex e A)=reindex e (adjoint A) := rfl

theorem gram_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Matrix β β Scalar) :
    matMul (adjoint (reindex e A)) (reindex e A)=
      reindex e (matMul (adjoint A) A) := by
  rw [adjoint_reindex,matMul_reindex]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal, duplicate-free five-site propagation support.  Lookup in its
encoded labels agrees with the zero extension used by the actual local core. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSupport
open QuantumHistoryBitProgram QuantumHistoryDiagonal QuantumOrderedSupport
open scoped Classical

theorem supportEquiv_apply (c : QMACircuit) (t : Fin c.gates.length)
    (i : Fin (sites c t).length) : (supportEquiv c t i).val=(sites c t).get i := rfl

theorem lookup_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s : Fin (sites c t).length → Fin 2) (q : QMACircuitQubit c) :
    QuantumSupportLookup.value (siteNumber c (.inr q),labels c t,
      List.ofFn (fun i => (s i).val))=
      (qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q).val := by
  have hf : Function.Injective (fun q : QMACircuitQubit c => siteNumber c (.inr q)) := by
    intro a b h
    exact Sum.inr_injective (siteNumber_injective c h)
  by_cases hq : q∈qmaPropagationSites c t
  · let i := (supportEquiv c t).symm ⟨q,hq⟩
    have hi : (sites c t).get i=q :=
      congrArg Subtype.val ((supportEquiv c t).apply_symm_apply ⟨q,hq⟩)
    have he := QuantumSupportLookup.value_map_get (sites c t) (sites_nodup c t)
      (fun q => siteNumber c (.inr q)) hf (fun j => (s j).val) i
    have hv : QuantumSupportLookup.value (siteNumber c (.inr q),labels c t,
        List.ofFn (fun j => (s j).val))=(s i).val := by
      simpa only [hi,labels] using he
    exact hv.trans (congrArg Fin.val (show
      qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q=s i from dite_eq_left hq)).symm
  · have hn : siteNumber c (.inr q)∉labels c t := by
      intro h
      obtain ⟨p,hp,he⟩ := List.mem_map.mp h
      have hpq := hf he
      subst p
      exact hq (by rw [← sites_finset]; exact List.mem_toFinset.mpr hp)
    have he := QuantumSupportLookup.value_not_mem (labels c t)
      (List.ofFn (fun i => (s i).val)) (siteNumber c (.inr q)) hn
      (by simp only [List.length_ofFn,labels,List.length_map,le_refl])
    exact he.trans (congrArg Fin.val (show
      qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q=0 from dite_eq_right hq)).symm

theorem readRow_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) :
    readRow c (data c t s r)=qmaSupportExtend (qmaPropagationSites c t)
      (fun j => s ((supportEquiv c t).symm j)) := by
  funext q
  apply Fin.ext
  change QuantumSupportLookup.value _ % 2 = _
  dsimp only [data]
  rw [lookup_actual]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

theorem readColumn_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) :
    readColumn c (data c t s r)=qmaSupportExtend (qmaPropagationSites c t)
      (fun j => r ((supportEquiv c t).symm j)) := by
  funext q
  apply Fin.ext
  change QuantumSupportLookup.value _ % 2 = _
  dsimp only [data]
  rw [lookup_actual]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

end ContinuumCoulomb.QuantumPropagationSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-size propagation tables and their adjoint-product.  The
largest table has five qubits, independently of the circuit work register. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationTable
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumAlgebraicHistory QuantumCircuitCode
open scoped Classical

theorem table_actual (c : QMACircuit) (t : Fin c.gates.length) :
    table (QuantumPropagationSupport.sites c t).length
      (c,t.val,QuantumPropagationSupport.labels c t)=
      reindex (supportBasisEquiv c t) (deltaCore c t) := by
  funext s r
  change QuantumHistoryDelta.entry c t.val (QuantumPropagationSupport.data c t s r)=_
  rw [QuantumHistoryDelta.entry_actual,QuantumPropagationSupport.readRow_actual,
    QuantumPropagationSupport.readColumn_actual]
  rfl

theorem gram_actual (c : QMACircuit) (t : Fin c.gates.length) :
    matMul (adjoint (table (QuantumPropagationSupport.sites c t).length
      (c,t.val,QuantumPropagationSupport.labels c t)))
      (table (QuantumPropagationSupport.sites c t).length
        (c,t.val,QuantumPropagationSupport.labels c t))=
      reindex (supportBasisEquiv c t) (propagationCore c t) := by
  rw [table_actual,gram_reindex]
  rfl

end ContinuumCoulomb.QuantumPropagationTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScalarFaithful
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four rational registers faithfully represent their complex value.
This permits exact local-table identities to reuse the established complex
matrix identities, without changing the arithmetic program. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar

theorem sqrtHalf_irrational : Irrational (Real.sqrt (1/2 : ℝ)) := by
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one,one_div]
  exact irrational_sqrt_two.inv

theorem realValue_injective : Function.Injective realValue := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hb : b=d := by
    by_contra hbd
    have hi := (sqrtHalf_irrational.ratCast_mul (sub_ne_zero.mpr hbd)).ratCast_add (a-c)
    have hz : ((a-c : ℚ) : ℝ)+((b-d : ℚ) : ℝ)*Real.sqrt (1/2 : ℝ)=0 := by
      dsimp only [realValue] at h
      push_cast
      nlinarith [h]
    rw [hz] at hi
    exact not_irrational_zero hi
  have ha : a=c := by
    subst d
    have he : (a:ℝ)=(c:ℝ) := by
      dsimp only [realValue] at h
      linarith
    exact_mod_cast he
  exact Prod.ext ha hb

theorem value_injective : Function.Injective value := by
  intro x y h
  apply Prod.ext
  · apply realValue_injective
    simpa only [value_re] using congrArg Complex.re h
  · apply realValue_injective
    simpa only [value_im] using congrArg Complex.im h

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRebitLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact scalar core of a lifted term with one active reference qubit.
Spectator reference bits are zero in the local core and contribute identities. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical BigOperators

theorem referenceState_eq_iff (n : ℕ) (i : Fin n) (a b : Fin 2) :
    referenceState n i a=referenceState n i b ↔ a=b := by
  constructor
  · intro h
    simpa only [referenceState,ite_true, if_true] using congrFun h i
  · rintro rfl
    rfl

theorem reference_identity (n : ℕ) (i : Fin n) (a b : Fin 2) :
    identity (referenceState n i a) (referenceState n i b)=identity a b := by
  simp only [identity,referenceState_eq_iff]

theorem localY_referenceState (n : ℕ) (i : Fin n) (a b : Fin 2) :
    localY n i (referenceState n i a) (referenceState n i b)=
      QuantumFixedPauli.pauli 2 a b := by
  apply value_injective
  rw [value_localY,value_pauli]
  change sourceLocalPauli n i 1 (referenceState n i a) (referenceState n i b)=
    ContinuumCoulomb.pauli 1 a b
  unfold sourceLocalPauli sourceTensor
  rw [Finset.prod_eq_single i]
  · simp only [ite_true, if_true,referenceState,ite_true]
  · intro j _ hji
    simp only [hji,ite_false, if_false,referenceState,Matrix.one_apply,ite_true, if_true]
  · simp

theorem lift_extend {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (u v : QMASupportBasis S) :
    lift S A (qmaSupportExtend S u) (qmaSupportExtend S v)=A u v := by
  have hu : (fun j : {j // j∈S} => qmaSupportExtend S u j.val)=u := by
    funext j
    exact dite_eq_left j.property
  have hv : (fun j : {j // j∈S} => qmaSupportExtend S v j.val)=v := by
    funext j
    exact dite_eq_left j.property
  have he : (fun j : {j // j∉S} => qmaSupportExtend S u j.val)=
      (fun j : {j // j∉S} => qmaSupportExtend S v j.val) := by
    funext j
    have hu0 : qmaSupportExtend S u j.val=0 := dite_eq_right j.property
    have hv0 : qmaSupportExtend S v j.val=0 := dite_eq_right j.property
    exact hu0.trans hv0.symm
  simp only [lift,hu,hv,identity,ite_eq_left he]
  apply value_injective
  simp only [value_mul,value_rat,Rat.cast_one,mul_one]

theorem rebit_entry_of_references {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (a b : Fin 2)
    (hs : s ∘ Sum.inl=referenceState n i a)
    (ht : t ∘ Sum.inl=referenceState n i b) :
    rebit n i A s t=oneReference a b (A (s ∘ Sum.inr) (t ∘ Sum.inr)) := by
  simp only [rebit,hs,ht,reference_identity,localY_referenceState,oneReference]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationOrder
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered support has its reference bit first, followed by
the duplicate-free propagation support in its literal source order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationOrder
open QuantumOrderedSupport
open scoped Classical

theorem firstIndex_site (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    (supportEquiv c hT (.inl i) (firstIndex c hT i t ht)).val=.inl i := by
  rw [supportEquiv_apply]
  change (sites c hT (.inl i))[0]'(firstIndex c hT i t ht).isLt=_
  simp only [sites_eq c hT i t ht,List.getElem_cons_zero]

theorem nextIndex_site (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (j : Fin (QuantumPropagationSupport.sites c t).length) :
    (supportEquiv c hT (.inl i) (nextIndex c hT i t ht j)).val=
      .inr (QuantumPropagationSupport.supportEquiv c t j).val := by
  rw [supportEquiv_apply,QuantumPropagationSupport.supportEquiv_apply]
  change (sites c hT (.inl i))[j.val+1]'(nextIndex c hT i t ht j).isLt=_
  simp only [sites_eq c hT i t ht,List.getElem_cons_succ,List.getElem_map,
    List.get_eq_getElem]

theorem extend_reference (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s ∘ Sum.inl=
      QuantumAlgebraicHistory.referenceState (qmaHistoryReferenceWork c+1) i
        (referenceBit c hT i t ht s) := by
  funext j
  by_cases hj : j=i
  · subst j
    have he := QuantumHistoryDiagonal.orderedExtend_at c hT (.inl i) s
      (firstIndex c hT i t ht)
    rw [firstIndex_site c hT i t ht] at he
    simpa [QuantumAlgebraicHistory.referenceState,referenceBit] using he
  · have hn : Sum.inl j ∉ (qmaOrderedHistoryModel c hT).sites (.inl i) := by
      intro hm
      rw [← rawSites_finset] at hm
      have hl := List.mem_toFinset.mp hm
      change Sum.inl j ∈ Sum.inl i :: _ at hl
      rcases List.mem_cons.mp hl with he | he
      · exact hj (Sum.inl_injective he)
      · obtain ⟨q,_,he⟩ := List.mem_map.mp he
        cases he
    have hz : QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s (.inl j)=0 :=
      dite_eq_right hn
    simpa only [Function.comp_apply,QuantumAlgebraicHistory.referenceState,
      ite_eq_right hj] using hz

theorem extend_data (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s ∘ Sum.inr=
      qmaSupportExtend (qmaPropagationSites c t)
        (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) := by
  funext q
  by_cases hq : q∈qmaPropagationSites c t
  · let j := (QuantumPropagationSupport.supportEquiv c t).symm ⟨q,hq⟩
    have hj : (QuantumPropagationSupport.supportEquiv c t j).val=q :=
      congrArg Subtype.val ((QuantumPropagationSupport.supportEquiv c t).apply_symm_apply ⟨q,hq⟩)
    have he := QuantumHistoryDiagonal.orderedExtend_at c hT (.inl i) s
      (nextIndex c hT i t ht j)
    rw [nextIndex_site c hT i t ht,hj] at he
    exact he.trans (show qmaSupportExtend (qmaPropagationSites c t)
      (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) q=
      s (nextIndex c hT i t ht j) from dite_eq_left hq).symm
  · have hn : Sum.inr q ∉ (qmaOrderedHistoryModel c hT).sites (.inl i) := by
      intro hm
      have hl : Sum.inr q ∈ (sites c hT (.inl i)).toFinset := by
        rw [sites_finset]
        exact hm
      have hx := List.mem_toFinset.mp hl
      rw [sites_eq c hT i t ht] at hx
      rcases List.mem_cons.mp hx with he | he
      · cases he
      · obtain ⟨r,hr,he⟩ := List.mem_map.mp he
        have hrq : r=q := Sum.inr_injective he
        subst r
        apply hq
        rw [← QuantumPropagationSupport.sites_finset]
        exact List.mem_toFinset.mpr hr
    have hz : qmaSupportExtend (qmaPropagationSites c t)
        (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) q=0 :=
      dite_eq_right hq
    exact (show QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s (.inr q)=0 from
      dite_eq_right hn).trans hz.symm

theorem ordered_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s r : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i) s r=
      QuantumAlgebraicHistory.oneReference
        (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
        (QuantumAlgebraicScalar.mul
          (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ))
          (QuantumAlgebraicHistory.propagationCore c t
            (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q))
            (fun q => localBits c hT i t ht r ((QuantumPropagationSupport.supportEquiv c t).symm q)))) := by
  let S := QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s
  let R := QuantumHistoryDiagonal.orderedExtend c hT (.inl i) r
  change QuantumAlgebraicHistory.rebit (qmaHistoryReferenceWork c+1) i
    (QuantumAlgebraicHistory.distributed c (qmaFirstUseTime c)
      (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)) S R=_
  rw [QuantumAlgebraicHistory.rebit_entry_of_references _ _ _ _ _ _ _
    (extend_reference c hT i t ht s) (extend_reference c hT i t ht r)]
  rw [ht]
  change QuantumAlgebraicHistory.oneReference _ _
    (QuantumAlgebraicScalar.mul _ (QuantumAlgebraicHistory.lift _ _
      (S ∘ Sum.inr) (R ∘ Sum.inr)))=_
  have hs := extend_data c hT i t ht s
  have hr := extend_data c hT i t ht r
  change S ∘ Sum.inr=_ at hs
  change R ∘ Sum.inr=_ at hr
  rw [hs,hr,QuantumAlgebraicHistory.lift_extend]

theorem ordered_gram_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s r : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i) s r=
      QuantumAlgebraicHistory.oneReference
        (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
        (QuantumAlgebraicScalar.mul
          (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ))
          (QuantumAlgebraicHistory.matMul
            (QuantumAlgebraicHistory.adjoint
              (QuantumPropagationTable.table (QuantumPropagationSupport.sites c t).length
                (c,t.val,QuantumPropagationSupport.labels c t)))
            (QuantumPropagationTable.table (QuantumPropagationSupport.sites c t).length
              (c,t.val,QuantumPropagationSupport.labels c t))
            (localBits c hT i t ht s) (localBits c hT i t ht r))) := by
  rw [ordered_entry c hT i t ht]
  have hg := congrFun (congrFun (QuantumPropagationTable.gram_actual c t)
    (localBits c hT i t ht s)) (localBits c hT i t ht r)
  exact congrArg (fun z => QuantumAlgebraicHistory.oneReference
    (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
    (QuantumAlgebraicScalar.mul
      (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ)) z)) hg.symm

end ContinuumCoulomb.QuantumPropagationOrder

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal local propagation tables after adding the single reference bit.
The arity is fixed in each program; no ambient spin configurations are scanned. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSampler
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open scoped Classical

theorem matrixData_cast {n m : ℕ} (h : n=m)
    (A : Matrix (Fin m → Fin 2) (Fin m → Fin 2) Scalar) :
    matrixData (reindex ((finCongr h).arrowCongr (Equiv.refl (Fin 2))) A)=matrixData A := by
  subst m
  rfl

theorem basisEquiv_zero (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t)
    (s : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    basisEquiv c hT i t ht s 0=QuantumPropagationOrder.referenceBit c hT i t ht s := by
  rfl

theorem basisEquiv_succ (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t)
    (s : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    (fun j => basisEquiv c hT i t ht s j.succ)=
      QuantumPropagationOrder.localBits c hT i t ht s := by
  rfl

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i)=
      reindex (basisEquiv c hT i t ht)
        (table (QuantumPropagationSupport.sites c t).length
          (c,t.val,QuantumPropagationSupport.labels c t)) := by
  funext s r
  rw [QuantumPropagationOrder.ordered_gram_entry c hT i t ht]
  simp only [reindex,table,basisEquiv_zero,basisEquiv_succ,coefficient]

theorem tableList_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    tableList (QuantumOrderedSupport.sites c hT (.inl i)).length
        (c,t.val,QuantumPropagationSupport.labels c t)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT (.inl i)) := by
  calc
    _ = tableList ((QuantumPropagationSupport.sites c t).length+1)
        (c,t.val,QuantumPropagationSupport.labels c t) :=
      congrArg (fun n => tableList n (c,t.val,QuantumPropagationSupport.labels c t))
        (QuantumPropagationOrder.length_eq c hT i t ht)
    _ = matrixData (table (QuantumPropagationSupport.sites c t).length
        (c,t.val,QuantumPropagationSupport.labels c t)) := rfl
    _ = _ := (matrixData_cast (QuantumPropagationOrder.length_eq c hT i t ht) _).symm.trans
      (congrArg matrixData (table_actual c hT i t ht).symm)

end ContinuumCoulomb.QuantumPropagationSampler

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceEdgeTable
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local tables for the reference-chain edges.  Their only nontrivial
entry is the fixed two-spin expression (I-Y tensor Y)/2. -/

noncomputable section
namespace ContinuumCoulomb.QuantumReferenceEdgeTable
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumHistoryDiagonal
open QuantumHistoryBitProgram QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem inactive (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c)
    (hq : q≠.inl i.castSucc ∧ q≠.inl i.succ) :
    orderedExtend c hT (.inr i) s q=0 := by
  have hn : q∉(qmaOrderedHistoryModel c hT).sites (.inr i) := by
    change q∉{Sum.inl i.castSucc,Sum.inl i.succ}
    intro hm
    rcases Finset.mem_insert.mp hm with h | h
    · exact hq.1 h
    · exact hq.2 (Finset.mem_singleton.mp h)
  exact dite_eq_right hn

theorem ordered_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2) :
    orderedTable c hT (.inr i) s t=
      table (QuantumOrderedSupport.sites c hT (.inr i)).length
        (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i)) s t := by
  let S := orderedExtend c hT (.inr i) s
  let T := orderedExtend c hT (.inr i) t
  have hd : S ∘ Sum.inr=T ∘ Sum.inr := by
    funext q
    exact (inactive c hT i s (.inr q) (by simp)).trans
      (inactive c hT i t (.inr q) (by simp)).symm
  have hr : S ∘ Sum.inl=T ∘ Sum.inl ↔ s=t := by
    constructor
    · intro h
      apply orderedExtend_injective c hT (.inr i)
      funext q
      cases q with
      | inl j => exact congrFun h j
      | inr j => exact congrFun hd j
    · rintro rfl
      rfl
  have hs : ∀ k, k≠i.castSucc → k≠i.succ → S (.inl k)=T (.inl k) := by
    intro k hk hl
    exact (inactive c hT i s (.inl k) (by simpa only [ne_eq,Sum.inl.injEq] using And.intro hk hl)).trans
      (inactive c hT i t (.inl k) (by simpa only [ne_eq,Sum.inl.injEq] using And.intro hk hl)).symm
  have hb (u : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
      (v : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
      (j : Fin (qmaHistoryReferenceWork c+1)) :
      row (data _ u v (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))) j.val=
        orderedExtend c hT (.inr i) u (.inl j) :=
    QuantumHistoryBitProgram.row_actual c hT (.inr i) u v (.inl j)
  have hc (j : Fin (qmaHistoryReferenceWork c+1)) :
      column (data _ s t (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))) j.val=
        T (.inl j) :=
    QuantumHistoryBitProgram.column_actual c hT (.inr i) s t (.inl j)
  change referenceEdge (qmaHistoryReferenceWork c) i S T=_
  unfold referenceEdge pairY
  simp only [identity,hd,hr,Function.comp_apply,ite_true, if_true]
  rw [ite_eq_left hs]
  unfold table
  have hbl := hb s t i.castSucc
  have hbr := hb s t i.succ
  have hcl := hc i.castSucc
  have hcr := hc i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hbl hbr hcl hcr
  dsimp only [Prod.fst]
  rw [hbl,hcl,hbr,hcr]
  apply value_injective
  simp only [identity,value_mul,value_sub,value_rat,Rat.cast_one,mul_one]
  rfl

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c)) :
    table (QuantumOrderedSupport.sites c hT (.inr i)).length
        (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))=
      orderedTable c hT (.inr i) := by
  funext s t
  exact (ordered_entry c hT i s t).symm

end ContinuumCoulomb.QuantumReferenceEdgeTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryTableProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total local-table dispatcher for the literal history order.  Its seven
arity templates are fixed; only descriptor and short-label reads vary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

theorem table_eq (x : Input) (h : x.2.2.length≤6) : table x=localTable x.2.2.length x := by
  generalize hn : x.2.2.length=n at *
  interval_cases n <;> simp only [table,hn] <;> norm_num

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryTableCorrectness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total table dispatcher agrees with the actual ordered history core,
including its canonical finite enumeration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open QuantumHistoryDescriptors QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

theorem nondiagonal_term (c : QMACircuit) (a : QMACircuitTerm c)
    (ha : ¬(encode c a).1<4) :
    ∃ t : Fin c.gates.length, a=QuantumPropagationOrder.term c t := by
  rcases a with i | (b | (i | (u | t)))
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · exact ⟨t,rfl⟩

theorem propagationLabels_tail (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    (QuantumOrderedSupport.encodedSites c hT (.inl i)).tail=
      QuantumPropagationSupport.labels c t := by
  simp only [QuantumOrderedSupport.encodedSites,QuantumPropagationOrder.sites_eq c hT i t ht,
    List.map_cons,List.tail_cons,List.map_map,Function.comp_def,QuantumPropagationSupport.labels]

theorem localTable_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    localTable (QuantumOrderedSupport.sites c hT a).length
      (c,((QuantumOrderedSourceIndex.reference c).symm a).val,
        QuantumOrderedSupport.encodedSites c hT a)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT a) := by
  cases a with
  | inl i =>
    change localTable (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,i.val,QuantumOrderedSupport.encodedSites c hT (.inl i))=_
    have hi : i.val < referenceWork c+1 := i.isLt
    simp only [localTable,hi,ite_true, if_true,orderedAt_actual c hT i]
    by_cases ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4
    · rw [ite_eq_left ha]
      exact QuantumHistoryDiagonal.tableList_actual c hT i ha
    · rw [ite_eq_right ha]
      obtain ⟨t,ht⟩ := nondiagonal_term c
        (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) ha
      rw [ht,propagationLabels_tail c hT i t ht]
      exact QuantumPropagationSampler.tableList_actual c hT i t ht
  | inr i =>
    change localTable (QuantumOrderedSupport.sites c hT (.inr i)).length
      (c,qmaHistoryReferenceWork c+1+i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))=_
    have hi : ¬qmaHistoryReferenceWork c+1+i.val<qmaHistoryReferenceWork c+1 := by
      omega
    simp only [localTable,referenceWork_eq,hi,ite_false, if_false,Nat.add_sub_cancel_left]
    exact congrArg matrixData (QuantumReferenceEdgeTable.table_actual c hT i)

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    table (c,((QuantumOrderedSourceIndex.reference c).symm a).val,
        QuantumOrderedSupport.encodedSites c hT a)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT a) := by
  rw [table_eq _ (by
    simpa only [QuantumOrderedSupport.encodedSites,List.length_map] using
      QuantumOrderedSupport.sites_length c hT a)]
  simpa only [QuantumOrderedSupport.encodedSites,List.length_map] using localTable_actual c hT a

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySamplerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial generation of all sampled history packets.  The
runtime list is indexed by the unary number of source terms, not Hilbert-space
dimension; each local matrix uses one of seven fixed arity programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySamplerProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumHistorySamplerProgram.finDecision
private theorem matrixData_instances {β : Type} (F G : Fintype β)
    (A : Matrix β β Scalar) : @matrixData β F A=@matrixData β G A := by
  cases Subsingleton.elim F G
  rfl

private theorem pair_matrixData_instances {β : Type} (F G : Fintype β)
    (A : Matrix β β Scalar) (xs : List ℕ) :
    (xs,@matrixData β F A)=(xs,@matrixData β G A) :=
  congrArg (fun ys : List Scalar => (xs,ys)) (matrixData_instances F G A)

theorem packet_actual (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (QuantumOrderedSourceIndex.referenceCount c)) :
    packet (k,c) i.val=QuantumPaddedLabelProgram.uniformPacket
      (QuantumPaddedLabelProgram.sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)) := by
  let a := QuantumOrderedSourceIndex.reference c i
  have hi : ((QuantumOrderedSourceIndex.reference c).symm a).val=i.val :=
    congrArg Fin.val ((QuantumOrderedSourceIndex.reference c).symm_apply_apply i)
  have hl := supportLabels_actual c hT a
  rw [hi] at hl
  have hm := QuantumHistoryTableProgram.table_actual c hT a
  rw [hi] at hm
  have hp : (supportLabels c i.val,
      QuantumHistoryTableProgram.table (c,i.val,supportLabels c i.val))=
      (QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)) := by
    rw [hl,hm]
    exact pair_matrixData_instances
      (β := Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) _ _
      (QuantumAlgebraicHistory.orderedTable c hT a) (QuantumOrderedSupport.encodedSites c hT a)
  change QuantumPaddedLabelProgram.uniformPacket (k,
      (supportLabels c i.val,QuantumHistoryTableProgram.table (c,i.val,supportLabels c i.val)))=
    QuantumPaddedLabelProgram.uniformPacket (k,
      (QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)))
  exact congrArg (fun p => QuantumPaddedLabelProgram.uniformPacket (k,p)) hp

theorem entries_actual (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    entries (k,c)=QuantumPaddedLabelProgram.sourceEntries k c hT := by
  unfold entries QuantumPaddedLabelProgram.sourceEntries
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact packet_actual k c hT i

end ContinuumCoulomb.QuantumHistorySamplerProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history packets, followed by the literal local and
four-spin compiler, have total full-space error at most nine over N. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex
open scoped Classical

theorem historyQubits_eq (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    historyQubits c hT N=4*(qubitCount c+3717*termCount c) := by
  unfold historyQubits historyInput QuantumOrderedLabelCompile.qubitCount
  rw [QuantumOrderedLabelPipeline.output_qubits,sourceEntries_length]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPrecisionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed sampling precision is computed in unary.  Composition
with the checked local sampler yields the actual early raw exchange compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPrecisionProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumAlgebraicHistory

theorem prepare_actual (N : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    prepare (N,c)=QuantumPaddedLabelProgram.historyInput c hT N := by
  change (N,QuantumOrderedSourceIndex.qubitCount c,
      QuantumHistorySamplerProgram.entries (samplePrecision c N,c))=
    (N,QuantumOrderedSourceIndex.qubitCount c,
      QuantumPaddedLabelProgram.sourceEntries (samplePrecision c N) c hT)
  rw [QuantumHistorySamplerProgram.entries_actual _ c hT]

theorem output_actual (N : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    output (N,c)=QuantumPaddedLabelProgram.historyOutput c hT N :=
  congrArg QuantumOrderedLabelCompile.output (prepare_actual N c hT)

theorem physicalQubits_actual (N : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    physicalQubits (N,c)=QuantumPaddedLabelProgram.historyQubits c hT N :=
  congrArg QuantumOrderedLabelCompile.qubitCount (prepare_actual N c hT)

end ContinuumCoulomb.QuantumHistoryPrecisionProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient envelopes for the actual sparse-history and degree-three
spatial output, preserving the exact numeric output order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumPaddedHistory QuantumOrderedSourceIndex
open QuantumForkList
open scoped Classical

theorem input_bonds (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).bonds=(historyOutput (qmaSparseCircuit c) hT N).1 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_constant (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).constant=(historyOutput (qmaSparseCircuit c) hT N).2 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_n (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).n=historyQubits (qmaSparseCircuit c) hT N := by
  unfold historyQubits historyInput
  rw [sourceEntries_table]
  rfl

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryRawCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed cell array has the exact physical-spin order of the raw
history compiler, including all six mediator layers and the four-spin blocks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumOrderedSourceIndex
open QuantumOrderedLabelTable QuantumOrderedSpatialComplete

theorem map_cell6 {ι κ C D : Type} (f : C → D) (cell : ι → C) (anchor : κ → C) :
    cell6 (f ∘ cell) (f ∘ anchor)=f ∘ cell6 cell anchor := by
  funext q
  rcases q with q | q
  · rcases q with q | q
    · rcases q with q | q
      · rcases q with q | q
        · rcases q with q | q
          · rcases q with q | q <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

theorem rawCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    rawCells c=List.ofFn (fun i : Fin
      (finalCount (qubitCount (qmaSparseCircuit c))
        (referenceCount (qmaSparseCircuit c)*patternCount)*4) =>
      encodeCell (QuantumOrderedOutputSpatial.physicalCell
        (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) i.val)) := by
  rw [rawCells,value_actual c hT,QuantumOrderedRawCells.value_table]
  apply congrArg List.ofFn
  funext i
  rw [QuantumOrderedOutputSpatial.physicalCell,
    QuantumRawCellLocality.blockCell_fin]
  change cell6 (encodeCell ∘ qmaOrderedQubitCell c hT)
      (encodeCell ∘ (fun p => qmaOrderedTermCell c hT p.1))
      (qubits6 (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (finProdFinEquiv.symm i).1)=_
  rw [map_cell6]
  simp only [Function.comp_apply,QuantumOrderedOutputSpatial.logicalCell,qmaFourBlockCell]

theorem rawCells_length (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) (N : ℕ) :
    (rawCells c).length=QuantumPaddedLabelProgram.historyQubits
      (qmaSparseCircuit c) hT N := by
  rw [rawCells_actual c hT,List.length_ofFn,
    QuantumPaddedLabelProgram.historyQubits_eq,finalCount_eq]
  simp only [termCount]
  omega

theorem rawCells_get (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) (j : ℕ)
    (hj : j<(rawCells c).length) :
    (rawCells c)[j]=encodeCell (QuantumOrderedOutputSpatial.physicalCell
      (qubits (qmaSparseCircuit c))
      (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
      (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) j) := by
  simp only [rawCells_actual c hT,List.getElem_ofFn]

theorem input_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N j : ℕ) :
    (QuantumHistorySpatial.input c hc hT hne N).cell j=
      QuantumOrderedOutputSpatial.physicalCell (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) j := by
  simp only [QuantumHistorySpatial.input,QuantumOrderedOutputSpatial.input,id]

theorem rawCells_input_length (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    (rawCells c).length=(QuantumHistorySpatial.input c hc hT hne N).n := by
  rw [QuantumHistorySpatial.input_n]
  exact rawCells_length c hT N

theorem rawCells_input_get (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N j : ℕ)
    (hj : j<(rawCells c).length) :
    (rawCells c)[j]=encodeCell ((QuantumHistorySpatial.input c hc hT hne N).cell j) := by
  rw [input_cell]
  exact rawCells_get c hT j hj

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpatialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal sampled history and its row/column labels are combined into
the exact prepared input of the fixed-round fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatialProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open QuantumHistoryPrecisionProgram

theorem rawCells_input (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    QuantumHistoryCells.rawCells c=List.ofFn
      (fun i : Fin (QuantumHistorySpatial.input c hc hT hne N).n =>
        QuantumSpatialInputTape.coordinates
          ((QuantumHistorySpatial.input c hc hT hne N).cell i.val)) := by
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact QuantumHistoryCells.rawCells_input_length c hc hT hne N
  · intro j hj _
    rw [List.getElem_ofFn]
    simpa only [QuantumSpatialInputTape.coordinates,QuantumHistoryCells.encodeCell] using
      QuantumHistoryCells.rawCells_input_get c hc hT hne N j hj

theorem initialInput_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    initialInput (N,c)=
      ((QuantumHistorySpatial.input c hc hT hne N).precision,
        (QuantumHistorySpatial.input c hc hT hne N).n,
        (QuantumHistorySpatial.input c hc hT hne N).bonds,
        (QuantumHistorySpatial.input c hc hT hne N).constant) := by
  rw [initialInput,sparseInput,physicalQubits_actual N (qmaSparseCircuit c) hT,
    output_actual N (qmaSparseCircuit c) hT,QuantumHistorySpatial.input_n,
    QuantumHistorySpatial.input_bonds,QuantumHistorySpatial.input_constant]
  rfl

theorem prepared_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    prepared (N,c)=QuantumSpatialInputTape.input
      (QuantumHistorySpatial.input c hc hT hne N) := by
  unfold prepared QuantumSpatialInputTape.input
  rw [initialInput_actual c hc hT hne N,rawCells_input c hc hT hne N]

end ContinuumCoulomb.QuantumHistorySpatialProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialPlanarRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual degree-three spatial exchange model has a nearest-neighbor
square-lattice realization. The number of layers and the size factor depend
only on its fixed spatial-density constants. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem placedVertex_positive (v : Fin M.n) :
    0 < (M.placedVertex v).1 ∧ 0 < (M.placedVertex v).2 := by
  change 0 < 8*(9*B+3+6)*(M.routeVertex v).1+17 ∧
    0 < 8*(9*B+3+6)*(M.routeVertex v).2+17
  omega

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPreparedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonempty circuit, final unary precision, exact history cells and
rational promise thresholds are assembled without semantic input oracles. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPreparedProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem precision_pos (c : QMACircuit) : 0<precision c :=
  QuantumAlgebraicHistory.finalPrecision_pos _ _

theorem prepared_actual (c : QMACircuit) (hc : c.WellFormed) :
    prepared c=QuantumSpatialInputTape.input
      (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
        (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)) :=
  QuantumHistorySpatialProgram.prepared_actual _ (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)

theorem finalInput_actual (c : QMACircuit) (hc : c.WellFormed) :
    finalInput c=
      (((precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))),
        (QuantumAlgebraicHistory.xzYesThreshold (qmaPreparedCircuit c),
          QuantumAlgebraicHistory.xzNoThreshold (qmaPreparedCircuit c))) := by
  rw [finalInput,prepared_actual c hc]
  rfl

end ContinuumCoulomb.QuantumHistoryPreparedProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScheduleCrossingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Match the complete literal crossing packet to the canonical port crossing
geometry. The input schedule and the crossing cells may have arbitrary orders. -/

noncomputable section
namespace ContinuumCoulomb.QuantumScheduleCrossingGeometry
open QuantumCrossingSelectProgram QuantumCrossingListLayer
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (s : QuantumListSchedule.State) (hs : QuantumListSchedule.Valid s)
    (E : QMAPathRelabeling (QuantumListSchedule.schedule s hs) (P.schedule.iterate N D))
    {r : ℕ} (cell : Fin r ≃ Fin P.crossingCells.card)

theorem input_actual : input P N hD s hs E cell =
    actualInput (layer P N hD s hs E cell) N (Equiv.refl _) := by
  have h := compiled_packet ((QuantumListSchedule.graph s hs).crossingSelection
    (site P N hD s hs E cell) (site_injective P N hD s hs E cell)) (Equiv.refl _) N
  have hp := congrArg (fun bs => QuantumCrossingSelectProgram.value
    (N,(s.1,bs,s.2.1),List.ofFn (encodedSites (site P N hD s hs E cell))))
      (QuantumListSchedule.graph_packed s hs).symm
  exact hp.trans h

theorem layer_support :
    (∀ e : ((layer P N hD s hs E cell).output N).Edge,
      ∃ f : (P.crossingOutput N hD).Edge,
        s((layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer
            E.vertex cell (((layer P N hD s hs E cell).output N).left e),
          (layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer
            E.vertex cell (((layer P N hD s hs E cell).output N).right e)) =
          s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f)) ∧
    (∀ f : (P.crossingOutput N hD).Edge,
      ∃ e : ((layer P N hD s hs E cell).output N).Edge,
        s((layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer
            E.vertex cell (((layer P N hD s hs E cell).output N).left e),
          (layer P N hD s hs E cell).vertexRelabel (P.portCrossingSelection N hD).layer
            E.vertex cell (((layer P N hD s hs E cell).output N).right e)) =
          s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f)) := by
  exact computed_output_support E.vertex E.edge E.left E.right
    (site P N hD s hs E cell) (P.crossingSiteFin N hD) cell
    (fun _ _ => E.vertex.apply_symm_apply _) (site_injective P N hD s hs E cell)
    (P.crossingSiteFin_injective N hD) (site_global P N hD s hs E cell) (Equiv.refl _) N N

theorem output_support :
    (∀ e : (actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).Edge,
      ∃ f : (P.crossingOutput N hD).Edge,
        s(vertex P N hD s hs E cell ((actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).left e),
          vertex P N hD s hs E cell ((actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).right e)) =
          s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f)) ∧
    (∀ f : (P.crossingOutput N hD).Edge,
      ∃ e : (actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).Edge,
        s(vertex P N hD s hs E cell ((actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).left e),
          vertex P N hD s hs E cell ((actualGraph (layer P N hD s hs E cell) N (Equiv.refl _)).right e)) =
          s((P.crossingOutput N hD).left f,(P.crossingOutput N hD).right f)) := by
  let C := layer P N hD s hs E cell
  let V := C.vertexRelabel (P.portCrossingSelection N hD).layer E.vertex cell
  have hl := layer_support P N hD s hs E cell
  constructor
  · intro e
    obtain ⟨k,hk⟩ := actual_support_source C N (Equiv.refl _) e
    obtain ⟨f,hf⟩ := hl.1 k
    exact ⟨f,(qmaUnorderedPair_map V hk).trans hf⟩
  · intro f
    obtain ⟨k,hk⟩ := hl.2 f
    obtain ⟨e,he⟩ := actual_support_target C N (Equiv.refl _) k
    exact ⟨e,(qmaUnorderedPair_map V he).trans hk⟩

theorem positions_actual :
    QuantumCrossingPositionProgram.positions
      (List.ofFn (fun i => (P.crossingCell (cell i)).val),
        List.ofFn (fun v => P.finishedPosition N D (E.vertex v))) =
      List.ofFn (fun v => P.crossingPosition N D (vertex P N hD s hs E cell v)) := by
  let C := layer P N hD s hs E cell
  have hp := QuantumCrossingPositionProgram.positions_reordered P N D E.vertex cell
  apply hp.trans
  exact List.ofFn_congr (count_actual C N (Equiv.refl _)).symm
    (fun v => P.crossingPosition N D (C.vertexRelabel (P.portCrossingSelection N hD).layer E.vertex cell v))

theorem packet_geometry : QMAPacketGeometry (P.crossingOutput N hD)
    (P.crossingPosition N D) (QuantumCrossingListLayer.value (input P N hD s hs E cell))
    (QuantumCrossingPositionProgram.positions
      (List.ofFn (fun i => (P.crossingCell (cell i)).val),
        List.ofFn (fun v => P.finishedPosition N D (E.vertex v)))) := by
  rw [input_actual]
  let C := layer P N hD s hs E cell
  refine ⟨bonds_bounded _ (QuantumListGraph.packed_bounded C.base (Equiv.refl _))
    (sites_bounded C N (Equiv.refl _)),
    bonds_noLoops _ (QuantumListGraph.packed_noLoops C.base (Equiv.refl _))
      (sites_bounded C N (Equiv.refl _)) (sites_injective C N (Equiv.refl _)),?_⟩
  exact ⟨vertex P N hD s hs E cell,positions_actual P N hD s hs E cell,
    output_support P N hD s hs E cell⟩

end ContinuumCoulomb.QuantumScheduleCrossingGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathRelabelingIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite route relabeling preserves the actual coordinates at every
scheduled subdivision round. -/

noncomputable section
namespace ContinuumCoulomb.QMAPathRelabeling
open MediatorGraph
open scoped Classical
variable {S T U : QMAPathSchedule}

variable (E : QMAPathRelabeling S T)
variable {Γ : SimpleGraph (ℕ × ℕ)}
    (P : QMAPathEmbedding S Γ) (Q : QMAPathEmbedding T Γ)
    (hpos : ∀ v, Q.position (E.vertex v)=P.position v)
    (hpoint : ∀ e k, Q.point (E.edge e) k=P.point e k)

include hpos hpoint in
theorem next_position (N : ℚ) (v : Fin (S.next N).graph.n) :
    (Q.next N).position ((E.next N).vertex v)=(P.next N).position v := by
  obtain ⟨v,rfl⟩ := (vertexEquiv S.graph.n S.active.card).surjective v
  rcases v with v | ⟨i,a⟩
  · change Q.nextPosition (E.nextVertex (old _ _ v))=P.nextPosition (old _ _ v)
    rw [E.nextVertex_old,QMAPathEmbedding.nextPosition_old,
      QMAPathEmbedding.nextPosition_old]
    exact hpos v
  · change Q.nextPosition (E.nextVertex (fresh _ _ i a))=P.nextPosition (fresh _ _ i a)
    rw [E.nextVertex_fresh,QMAPathEmbedding.nextPosition_fresh,
      QMAPathEmbedding.nextPosition_fresh]
    change Q.point (qmaSelectedIndex T.active (E.activeIndex i)) (a.val+1)=
      P.point (qmaSelectedIndex S.active i) (a.val+1)
    rw [← E.selected_index]
    exact hpoint _ _

include hpoint in
theorem next_point (N : ℚ) (e : (S.next N).graph.Edge) (k : ℕ) :
    (Q.next N).point ((E.next N).edge e) k=(P.next N).point e k := by
  rcases e with e | (i | ⟨i,a⟩)
  · exact hpoint e.val k
  · change Q.point (qmaSelectedIndex T.active (E.activeIndex i)) (k+1)=
      P.point (qmaSelectedIndex S.active i) (k+1)
    rw [← E.selected_index]
    exact hpoint _ _
  · change Q.point (qmaSelectedIndex T.active (E.activeIndex i))
        (if a=0 then k else 2*T.work (qmaSelectedIndex T.active (E.activeIndex i))+1-k)=
      P.point (qmaSelectedIndex S.active i)
        (if a=0 then k else 2*S.work (qmaSelectedIndex S.active i)+1-k)
    rw [← E.selected_index,← E.work]
    exact hpoint _ _


end ContinuumCoulomb.QMAPathRelabeling

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal coordinate tape follows the canonical physical subdivision,
with a finite relabeling accounting for each emitted edge order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open scoped Classical
open QuantumListSchedule

theorem iterate_matches {Γ : SimpleGraph (ℕ × ℕ)} (N : ℚ) (s : State)
    (hs : Valid s.1) (P : QMAPathEmbedding (schedule s.1 hs) Γ)
    (hP : Represents s hs P) {T : QMAPathSchedule} (Q : QMAPathEmbedding T Γ)
    (E : QMAPathRelabeling (schedule s.1 hs) T)
    (hpos : ∀ v, Q.position (E.vertex v)=P.position v)
    (hpoint : ∀ e j, Q.point (E.edge e) j=P.point e j) (k : ℕ) :
    ∃ (hk : Valid (iterate N k s).1)
      (Pk : QMAPathEmbedding (schedule (iterate N k s).1 hk) Γ)
      (Ek : QMAPathRelabeling (schedule (iterate N k s).1 hk) (T.iterate N k)),
      Represents (iterate N k s) hk Pk ∧
      (∀ v, (Q.iterate N k).position (Ek.vertex v)=Pk.position v) ∧
      (∀ e j, (Q.iterate N k).point (Ek.edge e) j=Pk.point e j) := by
  induction k with
  | zero => exact ⟨hs,P,E,hP,hpos,hpoint⟩
  | succ k ih =>
    obtain ⟨hk,Pk,Ek,hPk,hvk,hek⟩ := ih
    let F := nextRelabel (N,(iterate N k s).1) hk
    refine ⟨value_valid (N,(iterate N k s).1) hk,
      nextEmbedding (N,(iterate N k s).1) hk Pk,F.trans (Ek.next N),
      value_represents (N,iterate N k s) hk Pk hPk,?_,?_⟩
    · intro v
      exact (Ek.next_position Pk (Q.iterate N k) hvk hek N (F.vertex v)).trans (by rfl)
    · intro e j
      exact (Ek.next_point Pk (Q.iterate N k) hek N (F.edge e) j).trans (by rfl)

theorem packed_matches (G : QMARationalExchangeGraph) {m : ℕ}
    (labels : G.Edge ≃ Fin m) (work : G.Edge → ℕ)
    {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding ⟨G,work⟩ Γ) (N : ℚ) (k : ℕ) :
    ∃ (hk : Valid (iterate N k (QuantumPackedSchedule.layout G labels work P)).1)
      (Pk : QMAPathEmbedding
        (schedule (iterate N k (QuantumPackedSchedule.layout G labels work P)).1 hk) Γ)
      (Ek : QMAPathRelabeling
        (schedule (iterate N k (QuantumPackedSchedule.layout G labels work P)).1 hk)
        ((QMAPathSchedule.mk G work).iterate N k)),
      Represents (iterate N k (QuantumPackedSchedule.layout G labels work P)) hk Pk ∧
      (∀ v, (P.iterate N k).position (Ek.vertex v)=Pk.position v) ∧
      (∀ e j, (P.iterate N k).point (Ek.edge e) j=Pk.point e j) := by
  exact iterate_matches N _ (QuantumPackedSchedule.valid G labels work)
    ((QuantumPackedSchedule.scheduleRelabel G labels work).symm.transport P)
    (QuantumPackedSchedule.layout_represents G labels work P) P
    (QuantumPackedSchedule.scheduleRelabel G labels work) (fun _ => rfl) (fun _ _ => rfl) k

theorem packed_matches_of_eq (G : QMARationalExchangeGraph) {m : ℕ}
    (labels : G.Edge ≃ Fin m) (work : G.Edge → ℕ)
    {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding ⟨G,work⟩ Γ) (N : ℚ) (k : ℕ) (s : State)
    (hs : s=QuantumPackedSchedule.layout G labels work P) :
    ∃ (hk : Valid (iterate N k s).1)
      (Pk : QMAPathEmbedding
        (schedule (iterate N k s).1 hk) Γ)
      (Ek : QMAPathRelabeling
        (schedule (iterate N k s).1 hk)
        ((QMAPathSchedule.mk G work).iterate N k)),
      Represents (iterate N k s) hk Pk ∧
      (∀ v, (P.iterate N k).position (Ek.vertex v)=Pk.position v) ∧
      (∀ e j, (P.iterate N k).point (Ek.edge e) j=Pk.point e j) := by
  subst s
  exact packed_matches G labels work P N k

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialPortMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact geometric matching for the actual spatial compiler. Its position
tape is a permutation of the canonical completed port graph. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialPortProgram
open QuantumForkList
open scoped Classical

theorem port_layout_matches {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ} (labels : M.Term ≃ Fin m)
    (hA : 0<A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (N : ℚ) (k : ℕ) (s : QuantumListRouteProgram.State)
    (hs : s=QuantumPackedSchedule.layout M.exchangeGraph labels
      (M.coarseLength hd) (M.portEmbedding hA hd)) :
    ∃ (hk : QuantumListSchedule.Valid (QuantumListRouteProgram.iterate N k s).1)
      (Pk : QMAPathEmbedding
        (QuantumListSchedule.schedule (QuantumListRouteProgram.iterate N k s).1 hk)
        ((M.portRouteData hA hd).graph))
      (Ek : QMAPathRelabeling
        (QuantumListSchedule.schedule (QuantumListRouteProgram.iterate N k s).1 hk)
        ((M.portRouteData hA hd).schedule.iterate N k)),
      QuantumListRouteProgram.Represents (QuantumListRouteProgram.iterate N k s) hk Pk ∧
      (∀ v, ((M.portEmbedding hA hd).iterate N k).position (Ek.vertex v)=Pk.position v) ∧
      (∀ e j, ((M.portEmbedding hA hd).iterate N k).point (Ek.edge e) j=Pk.point e j) := by
  exact QuantumListRouteProgram.packed_matches_of_eq M.exchangeGraph labels
    (M.coarseLength hd) (M.portEmbedding hA hd) N k s hs

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)
include hA

theorem value_matches (N : ℚ) :
    ∃ (hk : QuantumListSchedule.Valid (value A D (N,QuantumSpatialInputTape.input I)).1)
      (Pk : QMAPathEmbedding
        (QuantumListSchedule.schedule (value A D (N,QuantumSpatialInputTape.input I)).1 hk)
        ((I.model.portRouteData hA I.model_degree).graph))
      (Ek : QMAPathRelabeling
        (QuantumListSchedule.schedule (value A D (N,QuantumSpatialInputTape.input I)).1 hk)
        ((I.model.portRouteData hA I.model_degree).schedule.iterate N (rounds A D))),
      QuantumListRouteProgram.Represents (value A D (N,QuantumSpatialInputTape.input I)) hk Pk ∧
      (∀ v, ((I.model.portEmbedding hA I.model_degree).iterate N (rounds A D)).position
          (Ek.vertex v) = Pk.position v) ∧
      (∀ e j, ((I.model.portEmbedding hA I.model_degree).iterate N (rounds A D)).point
          (Ek.edge e) j = Pk.point e j) := by
  have hi : initial A D (QuantumSpatialInputTape.input I)=
      QuantumPackedSchedule.layout I.model.exchangeGraph (Equiv.refl _)
        (I.model.coarseLength I.model_degree) (I.model.portEmbedding hA I.model_degree) :=
    QuantumPortSchedulePacking.layout_eq I hA
  exact port_layout_matches I.model (Equiv.refl _) hA I.model_degree N (rounds A D)
    (initial A D (QuantumSpatialInputTape.input I)) hi

end ContinuumCoulomb.QuantumSpatialPortProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialCrossingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed crossing cells and terminal scans use exactly the physical
port geometry, with finite permutations accounting for their output order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open QuantumForkList QuantumRouteCode
open scoped Classical

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N : ℚ)

private theorem edgeList_complete (e : I.model.Term) : e ∈ edgeList I :=
  List.mem_ofFn.mpr ⟨e,rfl⟩

private theorem ofFn_map_id {n : ℕ} {α : Type*} (f : Fin n → α) :
    List.ofFn f = (List.ofFn (fun e : Fin n => e)).map f := by
  rw [List.map_ofFn]
  rfl

theorem coarse_actual : coarse A D (N,QuantumSpatialInputTape.input I) =
    (List.ofFn (I.model.portRouteData hA I.model_degree).position,
      (edgeList I).map (I.model.portRouteData hA I.model_degree).routeList) := by
  have h := QuantumSpatialRoutingTape.value_actual I hA
  change QuantumSpatialRoutingTape.value A D (QuantumSpatialInputTape.input I) = _
  rw [h]
  refine Prod.ext ?_ ?_
  · rfl
  exact ofFn_map_id (fun e : Fin (fullList I.state).length =>
    (I.model.portRouteData hA I.model_degree).routeList e)

theorem cells_order :
    ∃ τ : Fin (cells A D (N,QuantumSpatialInputTape.input I)).length ≃
      Fin (I.model.portRouteData hA I.model_degree).crossingCells.card,
      cells A D (N,QuantumSpatialInputTape.input I) =
        List.ofFn (fun i => ((I.model.portRouteData hA I.model_degree).crossingCell (τ i)).val) := by
  unfold cells
  rw [coarse_actual I hA N]
  let P := I.model.portRouteData hA I.model_degree
  refine ⟨(QuantumDistinctCrossings.cellsEquiv P (edgeList I) (edgeList_complete I)).trans
    P.crossingCells.equivFin,?_⟩
  apply (QuantumDistinctCrossings.list_eq P (edgeList I) (edgeList_complete I)).trans
  apply congrArg List.ofFn
  funext i
  change ((QuantumDistinctCrossings.cellsEquiv P (edgeList I) (edgeList_complete I)) i).val =
    (P.crossingCells.equivFin.symm (P.crossingCells.equivFin
      ((QuantumDistinctCrossings.cellsEquiv P (edgeList I) (edgeList_complete I)) i))).val
  rw [Equiv.symm_apply_apply]

theorem table_permission (R : QMACellRouteBody) :
    QuantumRoutingTable.allowed (table A D (N,QuantumSpatialInputTape.input I)) R =
      QuantumRoutingTable.allowed (I.model.portRouteData hA I.model_degree).routingTable R := by
  unfold table
  rw [coarse_actual I hA N]
  exact QuantumPathTable.compile_allowed _ _ (edgeList_complete I) R

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialCrossingSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spatial compiler emits a crossing packet with the canonical
physical support and positions, rather than merely an abstract simulation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open QuantumForkList

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N : ℚ)

theorem packet_geometry :
    QMAPacketGeometry
      ((I.model.portRouteData hA I.model_degree).crossingOutput N (length_bound I hA))
      ((I.model.portRouteData hA I.model_degree).crossingPosition N
        (QuantumSpatialPortProgram.rounds A D))
      (value A D (N,QuantumSpatialInputTape.input I)).1.1
      (value A D (N,QuantumSpatialInputTape.input I)).1.2 := by
  let P := I.model.portRouteData hA I.model_degree
  let S := (QuantumSpatialPortProgram.value A D (N,QuantumSpatialInputTape.input I)).1
  obtain ⟨hs,Ps,E,hrep,hpos,hpoint⟩ := QuantumSpatialPortProgram.value_matches I hA N
  obtain ⟨cell,hcell⟩ := cells_order I hA N
  have hp : oldPositions A D (N,QuantumSpatialInputTape.input I) =
      List.ofFn (fun v => P.finishedPosition N (QuantumSpatialPortProgram.rounds A D)
        (E.vertex v)) := by
    apply hrep.1.trans
    exact congrArg List.ofFn (funext fun v => (hpos v).symm)
  have hsites : sites A D (N,QuantumSpatialInputTape.input I) =
      List.ofFn (QuantumCrossingSelectProgram.encodedSites
        (QuantumScheduleCrossingGeometry.site P N (length_bound I hA) S hs E cell)) := by
    change QuantumCrossingSiteProgram.allSites
      (oldPositions A D (N,QuantumSpatialInputTape.input I),
        cells A D (N,QuantumSpatialInputTape.input I)) = _
    apply (congrArg QuantumCrossingSiteProgram.allSites (congrArg₂ Prod.mk hp hcell)).trans
    exact QuantumCrossingSiteProgram.allSites_reordered P N (length_bound I hA) E.vertex
      (fun v => P.finishedPosition N (QuantumSpatialPortProgram.rounds A D) (E.vertex v))
      (fun _ => rfl) cell
  have hinput : crossingInput A D (N,QuantumSpatialInputTape.input I) =
      QuantumScheduleCrossingGeometry.input P N (length_bound I hA) S hs E cell := by
    exact congrArg (fun ss => QuantumCrossingSelectProgram.value
      (N,oldPacket A D (N,QuantumSpatialInputTape.input I),ss)) hsites
  have hpositions : positions A D (N,QuantumSpatialInputTape.input I) =
      QuantumCrossingPositionProgram.positions
        (List.ofFn (fun i => (P.crossingCell (cell i)).val),
          List.ofFn (fun v => P.finishedPosition N (QuantumSpatialPortProgram.rounds A D)
            (E.vertex v))) :=
    congrArg QuantumCrossingPositionProgram.positions (congrArg₂ Prod.mk hcell hp)
  change QMAPacketGeometry (P.crossingOutput N (length_bound I hA))
    (P.crossingPosition N (QuantumSpatialPortProgram.rounds A D))
    (QuantumCrossingListLayer.value (crossingInput A D (N,QuantumSpatialInputTape.input I)))
    (positions A D (N,QuantumSpatialInputTape.input I))
  rw [hinput,hpositions]
  exact QuantumScheduleCrossingGeometry.packet_geometry P N (length_bound I hA) S hs E cell

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryRoutedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space history comparison and verifier implications for the
literal circuit-to-lattice output, including empty-circuit preparation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram
open QuantumAlgebraicHistory

theorem routedState_actual (c : QMACircuit) (hc : c.WellFormed) :
    routedState c = QuantumFinalRoutingProgram.routed rawDensity historyDegree
      (((precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))),
        thresholds c) :=
  congrArg (QuantumFinalRoutingProgram.routed rawDensity historyDegree) (finalInput_actual c hc)

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialFinalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal spatial routing output carries the exact physical
square-lattice embedding, with a fixed multiple of the original box. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open QuantumForkList

theorem spatial_realization {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 < N) (a b : ℚ) :
    let s := routed A D ((N,QuantumSpatialInputTape.input I),a,b)
    ∃ (hs : QuantumListSchedule.Valid s.1)
      (Q : QMAPathEmbedding (QuantumListSchedule.schedule s.1 hs)),
      QuantumListRouteProgram.Represents s hs Q ∧
      Q.Bounded (256*I.model.bufferedWidth) (256*I.model.bufferedHeight) ∧
      (∀ e, qmaSquareGrid.Adj (Q.position ((QuantumListSchedule.schedule s.1 hs).graph.left e))
        (Q.position ((QuantumListSchedule.schedule s.1 hs).graph.right e))) := by
  let P := I.model.portRouteData hA I.model_degree
  have hpath : ∀ e k, k ≤ P.length e →
      (P.point e k).1 < I.model.bufferedWidth ∧
      (P.point e k).2 < I.model.bufferedHeight := by
    intro e k _
    exact I.model.bufferedPath_bounds I.model_degree e
      ((I.model.bufferedPath I.model_degree e).val.getVert_mem_support k)
  exact QuantumPlanarTapeGeometry.final_realization P N
    (QuantumSpatialCrossingProgram.length_bound I hA)
    (QuantumSpatialCrossingProgram.value A D (N,QuantumSpatialInputTape.input I))
    (QuantumSpatialCrossingProgram.packet_geometry I hA N)
    (QuantumSpatialCrossingProgram.table_permission I hA N)
    (I.model.sourceCell_no_passage hA I.model_degree) I.model.placedVertex_positive
    I.model.placedVertex_bounds hpath hN

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryLiteralCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal circuit compiler satisfies the original Heisenberg yes/no
promise. Its scalar shift and finite edge order are those of the emitted tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram

theorem routed_realization_oai (c : QMACircuit) (hc : c.WellFormed) :
    ∃ (hs : QuantumListSchedule.Valid (routedState c).1)
      (Q : QMAPathEmbedding (QuantumListSchedule.schedule (routedState c).1 hs)),
      QuantumListRouteProgram.Represents (routedState c) hs Q ∧
      ∀ e, qmaSquareGrid.Adj
        (Q.position ((QuantumListSchedule.schedule (routedState c).1 hs).graph.left e))
        (Q.position ((QuantumListSchedule.schedule (routedState c).1 hs).graph.right e)) := by
  rw [routedState_actual c hc]
  obtain ⟨hs,Q,hQ,_,hgrid⟩ := QuantumFinalRoutingProgram.spatial_realization
    (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
      (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))
    finalDensity_pos (N := (precision c : ℚ))
    (by exact_mod_cast precision_pos c) (thresholds c).1 (thresholds c).2
  exact ⟨hs,Q,hQ,hgrid⟩

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.QuantumHistorySourceProgram.routed_realization_oai := @OAI.ContinuumCoulomb.QuantumHistorySourceProgram.routed_realization_oai
