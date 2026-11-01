-- Prove2me | solution 1 for OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.planar_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:44:47.040536+00:00
-- url     : https://prove2.me/submissions/d421b7cb-21ac-4b0f-8341-cf50324b5d00

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
import Definitions.Def_OAIQ092A010

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial rational programs for the crossing coefficients and penalty. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingCode
open ExactQuantumFactoring.BitStackProgram

theorem coefficients_spoke (x : Triple) (a : Fin 4) :
    (coefficients x ⟨a.val+1,by omega⟩ : ℝ) =
      qmaCrossingAmplitude (x.1:ℝ) (x.2.1:ℝ) (x.2.2:ℝ) a := by
  fin_cases a <;> simp [coefficients,qmaCrossingAmplitude]

theorem coefficients_perimeter (x : Triple) (a : Fin 4) :
    (coefficients x ⟨a.val+5,by omega⟩ : ℝ) = qmaCrossingWeight (x.2.1:ℝ) (x.2.2:ℝ) a := by
  fin_cases a <;> simp [coefficients,qmaCrossingWeight]

end ContinuumCoulomb.QuantumRoutingCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial coefficient program for both parities of a path gadget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathCode
open ExactQuantumFactoring.BitStackProgram QuantumRoutingCode

theorem coefficients_spoke (x : Input) (a : Fin 2) :
    (coefficients x ⟨a.val+1,by omega⟩ : ℝ) = qmaPathAmplitude x.1 (x.2.1:ℝ) (x.2.2:ℝ) a := by
  rcases x with ⟨b,r,j⟩
  cases b <;> fin_cases a <;> simp [coefficients,qmaPathAmplitude]

end ContinuumCoulomb.QuantumPathCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalPathStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational graph data for a selected path-subdivision layer. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

attribute [instance] QMARationalExchangeGraph.edgeFinite

namespace QMARationalExchangeGraph

theorem pathScale_cast (G : QMARationalExchangeGraph) (s : Finset G.Edge) (N : ℚ) :
    (G.pathScale s N : ℝ) = qmaPartialPathsScale (fun e => (G.weight e:ℝ)) G.constant s N := by
  simp only [pathScale,qmaPartialPathsScale,qmaRoutingScale]
  push_cast
  rfl

end QMARationalExchangeGraph
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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathWeightBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathSchedule.mem_active _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial coefficient bounds for one physical path-subdivision layer. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaPathOffset_abs_le {J L : ℝ} (hL : 1 ≤ L) (hJ : |J| ≤ L) :
    |qmaPathOffset J| ≤ 4*L^2 := by
  have hJ2 : J^2 ≤ L^2 := by nlinarith [sq_abs J,mul_self_le_mul_self (abs_nonneg J) hJ]
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  rw [abs_of_nonneg (by unfold qmaPathOffset; positivity)]
  unfold qmaPathOffset
  nlinarith

theorem qmaPathAmplitude_abs_le {R J L : ℝ} (hL : 1 ≤ L) (hR : |R| ≤ L) (hJ : |J| ≤ L)
    (even : Bool) (a : Fin 2) : |qmaPathAmplitude even R J a| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hL2 : L ≤ L^2 := by nlinarith
  have hp := mul_le_mul hR hJ (abs_nonneg J) hL0
  cases even <;> fin_cases a <;> simp [qmaPathAmplitude,abs_mul] <;> nlinarith

namespace QMARationalExchangeGraph

theorem subdivide_weight_abs_le (G : QMARationalExchangeGraph) (s : Finset G.Edge)
    (even : Fin s.card → Bool) (N : ℚ) {L : ℝ} (hL : 1 ≤ L)
    (hR : |(G.pathScale s N:ℝ)| ≤ L) (hw : ∀ e, |(G.weight e:ℝ)| ≤ L)
    (e : (G.subdivide s even N).Edge) : |((G.subdivide s even N).weight e:ℝ)| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hL2 : L ≤ L^2 := by nlinarith
  rcases e with e | (i | ⟨i,a⟩)
  · exact (hw e.val).trans (by nlinarith)
  · change |(((G.pathScale s N)^2:ℚ):ℝ)| ≤ _
    push_cast
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (G.pathScale s N:ℝ),mul_self_le_mul_self (abs_nonneg _) hR]
  · change |(QuantumPathCode.coefficients (even i,G.pathScale s N,G.weight (qmaSelectedIndex s i))
        ⟨a.val+1,by omega⟩:ℝ)| ≤ _
    rw [QuantumPathCode.coefficients_spoke]
    exact qmaPathAmplitude_abs_le hL hR (hw _) _ _

theorem subdivide_constant_abs_le (G : QMARationalExchangeGraph) (s : Finset G.Edge)
    (even : Fin s.card → Bool) (N : ℚ) {L : ℝ} (hL : 1 ≤ L)
    (hR : |(G.pathScale s N:ℝ)| ≤ L) (hw : ∀ e, |(G.weight e:ℝ)| ≤ L) :
    |((G.subdivide s even N).constant:ℝ)| ≤ |(G.constant:ℝ)|+7*(s.card:ℝ)*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hR2 : (G.pathScale s N:ℝ)^2 ≤ L^2 := by
    nlinarith [sq_abs (G.pathScale s N:ℝ),mul_self_le_mul_self (abs_nonneg _) hR]
  have hs : |∑ i : Fin s.card, qmaPathOffset (G.weight (qmaSelectedIndex s i):ℝ)| ≤
      (s.card:ℝ)*(4*L^2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _i : Fin s.card, 4*L^2 := Finset.sum_le_sum (fun i _ => qmaPathOffset_abs_le hL (hw _))
      _ = _ := by simp
  have hc := abs_add_le (G.constant:ℝ) (∑ i : Fin s.card, qmaPathOffset (G.weight (qmaSelectedIndex s i):ℝ))
  have hd := abs_add_le ((G.constant:ℝ)+∑ i : Fin s.card, qmaPathOffset (G.weight (qmaSelectedIndex s i):ℝ))
    (3*(s.card:ℝ)*(G.pathScale s N:ℝ)^2)
  rw [abs_of_nonneg (by positivity : 0 ≤ 3*(s.card:ℝ)*(G.pathScale s N:ℝ)^2)] at hd
  change |((((G.constant+∑ i : Fin s.card, (3/4+3*(G.weight (qmaSelectedIndex s i))^2))+
    3*(s.card:ℚ)*(G.pathScale s N)^2):ℚ):ℝ)| ≤ _
  push_cast
  change |((G.constant:ℝ)+∑ i : Fin s.card, qmaPathOffset (G.weight (qmaSelectedIndex s i):ℝ))+
    3*(s.card:ℝ)*(G.pathScale s N:ℝ)^2| ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hR2 (by positivity : 0 ≤ (s.card:ℝ))]

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathPolynomialBound
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumCoefficientPrograms.pathBudget_cast _root_.OAI.ContinuumCoulomb.QuantumCoefficientPrograms.pathRadius_cast _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial coefficient envelopes for the actual selected path
subdivision, uniform in the selected set and its parity choices. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph)

theorem pathScale_abs_bound (s : Finset G.Edge) {N : ℚ} (hN : 0 ≤ N)
    {m L T : ℝ} (hm : (Fintype.card G.Edge:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : G.CoefficientBound L) :
    |(G.pathScale s N:ℝ)| ≤ qmaPathRadiusBound m L T := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ (N:ℝ) := by exact_mod_cast hN
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hs0 : (s.card:ℝ) ≤ (Fintype.card G.Edge:ℝ) := by exact_mod_cast Finset.card_le_univ s
  have hs : (s.card:ℝ) ≤ m := hs0.trans hm
  have hr0 : (Fintype.card {e : G.Edge // e ∉ s}:ℝ) ≤ (Fintype.card G.Edge:ℝ) := by
    exact_mod_cast Fintype.card_subtype_le (fun e : G.Edge => e ∉ s)
  have hr : (Fintype.card {e : G.Edge // e ∉ s}:ℝ) ≤ m := hr0.trans hm
  have hret : (∑ e : {e : G.Edge // e ∉ s}, |(G.weight e.val:ℝ)|) ≤ m*L := by
    calc
      _ ≤ ∑ _e : {e : G.Edge // e ∉ s}, L := Finset.sum_le_sum (fun e _ => hc.2 e.val)
      _ = (Fintype.card {e : G.Edge // e ∉ s}:ℝ)*L := by simp
      _ ≤ m*L := mul_le_mul_of_nonneg_right hr hL0
  have ha : (∑ i : Fin s.card, (1+2*|(G.weight (qmaSelectedIndex s i):ℝ)|)) ≤ m*(1+2*L) := by
    calc
      _ ≤ ∑ _i : Fin s.card, (1+2*L) := Finset.sum_le_sum (fun i _ => by linarith [hc.2 (qmaSelectedIndex s i)])
      _ = (s.card:ℝ)*(1+2*L) := by simp [mul_add]
      _ ≤ m*(1+2*L) := mul_le_mul_of_nonneg_right hs (by positivity)
  have hd : (∑ i : Fin s.card, (1+|(G.weight (qmaSelectedIndex s i):ℝ)|)^2) ≤ m*(1+L)^2 := by
    calc
      _ ≤ ∑ _i : Fin s.card, (1+L)^2 := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (by positivity) (by linarith [hc.2 (qmaSelectedIndex s i)]) 2)
      _ = (s.card:ℝ)*(1+L)^2 := by simp
      _ ≤ m*(1+L)^2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  let A : ℝ := 3*∑ i : Fin s.card, (1+2*|(G.weight (qmaSelectedIndex s i):ℝ)|)
  let D : ℝ := 3*(∑ e : {e : G.Edge // e ∉ s}, |(G.weight e.val:ℝ)|)+
    |(G.constant:ℝ)|+4*∑ i : Fin s.card, (1+|(G.weight (qmaSelectedIndex s i):ℝ)|)^2
  have hAD0 : 0 ≤ A+D+1 := by dsimp [A,D]; positivity
  have hAD : A+D+1 ≤ qmaPathBudget m L := by dsimp [A,D,qmaPathBudget]; linarith [hc.1]
  have hcube := pow_le_pow_left₀ hAD0 hAD 3
  rw [G.pathScale_cast]
  change |16*(A+D+1)^3*(N:ℝ)+4*(A+D+1)+1| ≤ _
  rw [abs_of_nonneg (by positivity)]
  have hnT : (N:ℝ) ≤ T := by simpa only [abs_of_nonneg hn0] using hT
  have hprod := mul_le_mul hcube hnT
    hn0 (pow_nonneg (hAD0.trans hAD) 3)
  dsimp [qmaPathRadiusBound]
  nlinarith

theorem subdivide_coefficientBound (s : Finset G.Edge) (even : Fin s.card → Bool)
    {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ} (hm : (Fintype.card G.Edge:ℝ) ≤ m)
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : G.CoefficientBound L) :
    (G.subdivide s even N).CoefficientBound (qmaPathCoefficientBound m L T) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hb0 : 0 ≤ qmaPathBudget m L := by unfold qmaPathBudget; positivity
  have hrad : L ≤ qmaPathRadiusBound m L T := by
    unfold qmaPathRadiusBound
    have h : 0 ≤ 16*(qmaPathBudget m L)^3*T := by positivity
    linarith
  have hr1 : 1 ≤ qmaPathRadiusBound m L T := hL.trans hrad
  have hr := G.pathScale_abs_bound s hN hm hL hT hc
  have hw : ∀ e, |(G.weight e:ℝ)| ≤ qmaPathRadiusBound m L T :=
    fun e => (hc.2 e).trans hrad
  have hs0 : (s.card:ℝ) ≤ (Fintype.card G.Edge:ℝ) := by exact_mod_cast Finset.card_le_univ s
  have hs : (s.card:ℝ) ≤ m := hs0.trans hm
  constructor
  · have h := G.subdivide_constant_abs_le s even N hr1 hr hw
    have hm' := mul_le_mul_of_nonneg_right hs (sq_nonneg (qmaPathRadiusBound m L T))
    unfold qmaPathCoefficientBound
    nlinarith [hc.1]
  · intro e
    have h := G.subdivide_weight_abs_le s even N hr1 hr hw e
    unfold qmaPathCoefficientBound
    nlinarith [sq_nonneg (qmaPathRadiusBound m L T),
      mul_nonneg hm0 (sq_nonneg (qmaPathRadiusBound m L T))]

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous crossing-removal layer as exact rational ordinary-spin data. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph Matrix
open scoped BigOperators Classical

namespace QMARationalCrossingLayer
variable {r : ℕ}

theorem scale_cast (C : QMARationalCrossingLayer r) (N : ℚ) :
    (C.scale N:ℝ) =
      qmaRoutingScale (6*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|))
        (3*(∑ e, |(C.base.weight e:ℝ)|)+|(C.base.constant:ℝ)|+
          12*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)^2) N := by
  simp only [scale,qmaRoutingScale]
  push_cast
  rfl

end QMARationalCrossingLayer
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingCoefficientBound
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumCoefficientPrograms.crossingBudget_cast _root_.OAI.ContinuumCoulomb.QuantumCoefficientPrograms.crossingRadius_cast _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient envelopes for the actual rational crossing layer.
The bounds include its scalar counterterms. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaCrossingWeight_abs_le {J K L : ℝ} (hL : 1 ≤ L)
    (hJ : |J| ≤ L) (hK : |K| ≤ L) (a : Fin 4) :
    |qmaCrossingWeight J K a| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ L^2 := by nlinarith
  have hprod := mul_le_mul hJ hK (abs_nonneg K) hL0
  fin_cases a <;> simp [qmaCrossingWeight,abs_mul] <;> nlinarith

theorem qmaCrossingAmplitude_abs_le {R J K L : ℝ} (hL : 1 ≤ L)
    (hR : |R| ≤ L) (hJ : |J| ≤ L) (hK : |K| ≤ L) (a : Fin 4) :
    |qmaCrossingAmplitude R J K a| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ L^2 := by nlinarith
  have hprodJ := mul_le_mul hR hJ (abs_nonneg J) hL0
  have hprodK := mul_le_mul hR hK (abs_nonneg K) hL0
  fin_cases a <;> simp [qmaCrossingAmplitude,abs_mul] <;> nlinarith

theorem qmaCrossingOffset_abs_le {J K L : ℝ} (hL : 1 ≤ L)
    (hJ : |J| ≤ L) (hK : |K| ≤ L) :
    |qmaCrossingOffset J K| ≤ 8*L^2 := by
  have hJ2 : J^2 ≤ L^2 := by nlinarith [sq_abs J,mul_self_le_mul_self (abs_nonneg J) hJ]
  have hK2 : K^2 ≤ L^2 := by nlinarith [sq_abs K,mul_self_le_mul_self (abs_nonneg K) hK]
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  rw [abs_of_nonneg (by unfold qmaCrossingOffset; positivity)]
  unfold qmaCrossingOffset
  linarith

namespace QMARationalCrossingLayer
variable {r : ℕ} (C : QMARationalCrossingLayer r)

theorem scale_abs_bound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card C.base.Edge:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : C.base.CoefficientBound L)
    (hJ : ∀ i, |(C.J i:ℝ)| ≤ L) (hK : ∀ i, |(C.K i:ℝ)| ≤ L) :
    |(C.scale N:ℝ)| ≤ qmaCrossingRadiusBound m r L T := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ (N:ℝ) := by exact_mod_cast hN
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hret : (∑ e, |(C.base.weight e:ℝ)|) ≤ m*L := by
    calc
      _ ≤ ∑ _e : C.base.Edge, L := Finset.sum_le_sum (fun e _ => hc.2 e)
      _ = (Fintype.card C.base.Edge:ℝ)*L := by simp
      _ ≤ m*L := mul_le_mul_of_nonneg_right hm hL0
  have ha : (∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)) ≤ r*(1+2*L) := by
    calc
      _ ≤ ∑ _i : Fin r, (1+2*L) := Finset.sum_le_sum (fun i _ => by linarith [hJ i,hK i])
      _ = (r:ℝ)*(1+2*L) := by simp [mul_add]
  have hd : (∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)^2) ≤ r*(1+2*L)^2 := by
    calc
      _ ≤ ∑ _i : Fin r, (1+2*L)^2 := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (by positivity) (by linarith [hJ i,hK i]) 2)
      _ = (r:ℝ)*(1+2*L)^2 := by simp
  let A := 6*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)
  let D := 3*(∑ e, |(C.base.weight e:ℝ)|)+|(C.base.constant:ℝ)|+
    12*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)^2
  have hAD0 : 0 ≤ A+D+1 := by dsimp [A,D]; positivity
  have hAD : A+D+1 ≤ qmaCrossingBudget m r L := by
    dsimp [A,D,qmaCrossingBudget]
    linarith [hc.1]
  have hcube := pow_le_pow_left₀ hAD0 hAD 3
  have hnT : (N:ℝ) ≤ T := by simpa only [abs_of_nonneg hn0] using hT
  have hprod := mul_le_mul hcube hnT hn0 (pow_nonneg (hAD0.trans hAD) 3)
  rw [C.scale_cast]
  change |16*(A+D+1)^3*(N:ℝ)+4*(A+D+1)+1| ≤ _
  rw [abs_of_nonneg (by positivity)]
  dsimp [qmaCrossingRadiusBound]
  nlinarith

theorem output_weight_abs_le (N : ℚ) {L : ℝ} (hL : 1 ≤ L)
    (hR : |(C.scale N:ℝ)| ≤ L) (hw : ∀ e, |(C.base.weight e:ℝ)| ≤ L)
    (hJ : ∀ i, |(C.J i:ℝ)| ≤ L) (hK : ∀ i, |(C.K i:ℝ)| ≤ L)
    (e : (C.output N).Edge) : |((C.output N).weight e:ℝ)| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ L^2 := by nlinarith
  rcases e with (e | ⟨i,a⟩) | (i | ⟨i,a⟩)
  · exact (hw e).trans (by nlinarith)
  · change |(QuantumRoutingCode.coefficients (C.scale N,C.J i,C.K i) ⟨a.val+5,by omega⟩:ℝ)| ≤ _
    rw [QuantumRoutingCode.coefficients_perimeter]
    exact qmaCrossingWeight_abs_le hL (hJ i) (hK i) a
  · change |(((C.scale N)^2:ℚ):ℝ)| ≤ _
    push_cast
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (C.scale N:ℝ),mul_self_le_mul_self (abs_nonneg _) hR]
  · change |(QuantumRoutingCode.coefficients (C.scale N,C.J i,C.K i) ⟨a.val+1,by omega⟩:ℝ)| ≤ _
    rw [QuantumRoutingCode.coefficients_spoke]
    exact qmaCrossingAmplitude_abs_le hL hR (hJ i) (hK i) a

theorem output_constant_abs_le (N : ℚ) {L : ℝ} (hL : 1 ≤ L)
    (hR : |(C.scale N:ℝ)| ≤ L) (hJ : ∀ i, |(C.J i:ℝ)| ≤ L)
    (hK : ∀ i, |(C.K i:ℝ)| ≤ L) :
    |((C.output N).constant:ℝ)| ≤ |(C.base.constant:ℝ)|+11*(r:ℝ)*L^2 := by
  have hR2 : (C.scale N:ℝ)^2 ≤ L^2 := by
    nlinarith [sq_abs (C.scale N:ℝ),mul_self_le_mul_self (abs_nonneg _) hR]
  have hs : |∑ i, qmaCrossingOffset (C.J i:ℝ) (C.K i:ℝ)| ≤ (r:ℝ)*(8*L^2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _i : Fin r, 8*L^2 := Finset.sum_le_sum (fun i _ =>
        qmaCrossingOffset_abs_le hL (hJ i) (hK i))
      _ = _ := by simp
  have ha := abs_add_le (C.base.constant:ℝ) (∑ i, qmaCrossingOffset (C.J i:ℝ) (C.K i:ℝ))
  have hb := abs_add_le ((C.base.constant:ℝ)+∑ i, qmaCrossingOffset (C.J i:ℝ) (C.K i:ℝ))
    (3*(r:ℝ)*(C.scale N:ℝ)^2)
  rw [abs_of_nonneg (by positivity : 0 ≤ 3*(r:ℝ)*(C.scale N:ℝ)^2)] at hb
  change |((((C.base.constant+∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2))+
    3*(r:ℚ)*(C.scale N)^2):ℚ):ℝ)| ≤ _
  push_cast
  change |((C.base.constant:ℝ)+∑ i, qmaCrossingOffset (C.J i:ℝ) (C.K i:ℝ))+
    3*(r:ℝ)*(C.scale N:ℝ)^2| ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hR2 (by positivity : 0 ≤ (r:ℝ))]

theorem output_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card C.base.Edge:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : C.base.CoefficientBound L)
    (hJ : ∀ i, |(C.J i:ℝ)| ≤ L) (hK : ∀ i, |(C.K i:ℝ)| ≤ L) :
    (C.output N).CoefficientBound (qmaCrossingCoefficientBound m r L T) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hbudget : 0 ≤ qmaCrossingBudget m r L := by unfold qmaCrossingBudget; positivity
  have hrad : L ≤ qmaCrossingRadiusBound m r L T := by
    unfold qmaCrossingRadiusBound
    have h : 0 ≤ 16*(qmaCrossingBudget m r L)^3*T := by positivity
    linarith
  have hr1 : 1 ≤ qmaCrossingRadiusBound m r L T := hL.trans hrad
  have hr := C.scale_abs_bound hN hm hL hT hc hJ hK
  have hj : ∀ i, |(C.J i:ℝ)| ≤ qmaCrossingRadiusBound m r L T := fun i => (hJ i).trans hrad
  have hk : ∀ i, |(C.K i:ℝ)| ≤ qmaCrossingRadiusBound m r L T := fun i => (hK i).trans hrad
  constructor
  · have h := C.output_constant_abs_le N hr1 hr hj hk
    unfold qmaCrossingCoefficientBound
    nlinarith [hc.1,sq_nonneg (qmaCrossingRadiusBound m r L T)]
  · intro e
    have h := C.output_weight_abs_le N hr1 hr (fun e => (hc.2 e).trans hrad) hj hk e
    unfold qmaCrossingCoefficientBound
    nlinarith [sq_nonneg (qmaCrossingRadiusBound m r L T),
      mul_nonneg (Nat.cast_nonneg r : (0:ℝ) ≤ r) (sq_nonneg (qmaCrossingRadiusBound m r L T))]

end QMARationalCrossingLayer
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathIteratedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed number of routed subdivisions has an explicit polynomial envelope,
with edge counts tracked separately from coefficient magnitudes. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaPathCoefficientBound_one {m L T : ℝ} (hm : 0 ≤ m) (hL : 1 ≤ L) :
    1 ≤ qmaPathCoefficientBound m L T := by
  unfold qmaPathCoefficientBound
  have h : 0 ≤ (7*m+2)*(qmaPathRadiusBound m L T)^2 := by positivity
  linarith

theorem qmaPathIteratedBound_one {m L T : ℝ} (hm : 0 ≤ m) (hL : 1 ≤ L) (k : ℕ) :
    1 ≤ qmaPathIteratedBound m L T k := by
  induction k with
  | zero => exact hL
  | succ k ih => exact qmaPathCoefficientBound_one (by positivity) ih

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nine ordinary exchange interactions in a crossing gadget, serialized
in a fixed order. Every endpoint and rational coefficient is computed literally. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListBlock
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem block_length (x : Input) : (block x).length=9 := List.length_ofFn

end ContinuumCoulomb.QuantumCrossingListBlock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal simultaneous crossing layer: nine bonds and two fresh spins per
crossing, with every scalar correction retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListBlock
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem family_length (x : FamilyInput) : (family x).length=9*x.2.length := by
  simp only [family,List.length_flatten,List.map_map,Function.comp_def,block_length,
    List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul,Nat.mul_comm]
  norm_cast

end ContinuumCoulomb.QuantumCrossingListBlock

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

theorem constant_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    constant (actualInput C N labels)=(C.output N).constant := by
  unfold constant familyInput
  rw [parameters_actual]
  change C.base.constant+familyOffset ((C.base.n,C.scale N),List.ofFn (actualCrossing C)) = _
  simp only [familyOffset,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  change C.base.constant+(∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2+3*(C.scale N)^2)) =
    (C.base.constant+∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2))+3*(r:ℚ)*(C.scale N)^2
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumComputedCrossingBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient bounds for the literal endpoint scan, including
its retained background, selected couplings and merged output. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open MediatorListProgram
open scoped Classical

theorem weight_abs_le (xs : List Bond) (p : QuantumRouteCode.Pair) {L : ℝ}
    (hL : 0 ≤ L) (h : ∀ e ∈ xs, |(e.2.2 : ℝ)| ≤ L) :
    |(weight (xs,p) : ℝ)| ≤ xs.length*L := by
  induction xs with
  | nil => simp [weight]
  | cons e xs ih =>
    have he := h e List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have hc : |(contribution (e,p) : ℝ)| ≤ L := by
      unfold contribution
      split_ifs
      · exact he
      · simpa only [Rat.cast_zero,abs_zero] using hL
    change |((contribution (e,p)+weight (xs,p) : ℚ) : ℝ)| ≤ _
    rw [Rat.cast_add]
    have ha := abs_add_le (contribution (e,p) : ℝ) (weight (xs,p) : ℝ)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

variable {G : QMARationalExchangeGraph} {r k : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin k)

theorem packed_weight_bound {L : ℝ} (hc : G.CoefficientBound L) :
    ∀ e ∈ QuantumListGraph.packed G labels, |(e.2.2 : ℝ)| ≤ L := by
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact hc.2 (labels.symm i)

theorem retainedGraph_count : Fintype.card (retainedGraph S labels).Edge ≤ Fintype.card G.Edge := by
  change Fintype.card (Fin
    (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels)).length) ≤ _
  rw [Fintype.card_fin,Fintype.card_congr labels,Fintype.card_fin]
  simpa only [retained,QuantumListGraph.packed,List.length_ofFn] using
    (List.length_filter_le (fun e => keep (pairs (List.ofFn (encodedSites S.site)),e))
      (QuantumListGraph.packed G labels))

theorem retainedGraph_coefficientBound {L : ℝ} (hc : G.CoefficientBound L) :
    (retainedGraph S labels).CoefficientBound L := by
  refine ⟨hc.1,?_⟩
  intro e
  apply packed_weight_bound labels hc
  exact ((retained_mem _ _).mp
    (List.get_mem (retained (pairs (List.ofFn (encodedSites S.site)),
      QuantumListGraph.packed G labels)) e)).1

theorem computed_coupling_bound {m L : ℝ}
    (hm : (Fintype.card G.Edge : ℝ) ≤ m) (hL : 0 ≤ L) (hc : G.CoefficientBound L)
    (i : Fin r) (a : Fin 2) :
    |(weight (QuantumListGraph.packed G labels,terminalPair a (encodedSites S.site i)) : ℝ)| ≤ m*L := by
  have hk : ((QuantumListGraph.packed G labels).length : ℝ) ≤ m := by
    have hk' : k = Fintype.card G.Edge :=
      ((Fintype.card_congr labels).trans (Fintype.card_fin k)).symm
    simpa only [QuantumListGraph.packed,List.length_ofFn,hk'] using hm
  exact (weight_abs_le _ _ hL (packed_weight_bound labels hc)).trans
    (mul_le_mul_of_nonneg_right hk hL)

theorem computedLayer_output_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card G.Edge : ℝ) ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) :
    ((computedLayer S labels).output N).CoefficientBound
      (qmaCrossingCoefficientBound m r ((m+1)*L) T) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ (m+1)*L := by nlinarith
  have hcount : (Fintype.card (computedLayer S labels).base.Edge : ℝ) ≤ m := by
    exact (show (Fintype.card (retainedGraph S labels).Edge : ℝ) ≤
      (Fintype.card G.Edge : ℝ) by exact_mod_cast retainedGraph_count S labels).trans hm
  have hbase : (computedLayer S labels).base.CoefficientBound ((m+1)*L) := by
    have h := retainedGraph_coefficientBound S labels hc
    exact ⟨h.1.trans hLL,fun e => (h.2 e).trans hLL⟩
  apply (computedLayer S labels).output_coefficientBound hN hcount (hL.trans hLL) hT hbase
  · intro i
    exact (computed_coupling_bound S labels hm hL0 hc i 0).trans (by nlinarith)
  · intro i
    exact (computed_coupling_bound S labels hm hL0 hc i 1).trans (by nlinarith)

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPacketBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient bounds for the actual serialized crossing packet.  The
transfer uses the literal nine-bond blocks, including the scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open MediatorListProgram QuantumCrossingListBlock
open scoped Classical

variable {r m : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    (labels : C.base.Edge ≃ Fin m)

theorem actual_bonds_coefficientBound {L : ℝ}
    (hc : (C.output N).CoefficientBound L) :
    ∀ b ∈ bonds (actualInput C N labels), |(b.2.2 : ℝ)| ≤ L := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact hc.2 (.inl (.inl (labels.symm i)))
  · have hf : familyInput (actualInput C N labels) =
        ((C.base.n,C.scale N),List.ofFn (actualCrossing C)) := by
      unfold familyInput
      rw [parameters_actual]
      rfl
    rw [hf,family_ofFn] at hb
    obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hbs
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb
    rw [bond_actual]
    exact hc.2 (edgeTag C N i k)

theorem actualGraph_card :
    Fintype.card (actualGraph C N labels).Edge = Fintype.card C.base.Edge+9*r := by
  change Fintype.card (Fin (bonds (actualInput C N labels)).length) = _
  rw [Fintype.card_fin]
  simp only [bonds,List.length_append,family_length,familyInput,actualInput,
    QuantumListGraph.packed,List.length_ofFn]
  rw [Fintype.card_congr labels,Fintype.card_fin]

end ContinuumCoulomb.QuantumCrossingListLayer

namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open scoped Classical

variable {G : QMARationalExchangeGraph} {r k : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin k)

theorem compiled_graph_count {m : ℝ} (hm : (Fintype.card G.Edge : ℝ) ≤ m) (N : ℚ) :
    (Fintype.card
      (QuantumCrossingListLayer.actualGraph (computedLayer S labels) N (Equiv.refl _)).Edge : ℝ)
      ≤ m+9*r := by
  rw [QuantumCrossingListLayer.actualGraph_card (computedLayer S labels) N (Equiv.refl _),
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have h : (Fintype.card (retainedGraph S labels).Edge : ℝ) ≤ (Fintype.card G.Edge : ℝ) := by
    exact_mod_cast retainedGraph_count S labels
  exact add_le_add (h.trans hm) (le_refl (9*(r : ℝ)))

end ContinuumCoulomb.QuantumCrossingSelectProgram

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The specified physical lattice has a polynomial coefficient envelope,
including both crossing offsets and the final merge of parallel edges. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QuantumCoefficientPrograms

theorem pathCoefficient_one (m L T : ℕ) : 1 ≤ pathCoefficient m L T := by
  unfold pathCoefficient
  omega

theorem iterated_one {L : ℕ} (hL : 1 ≤ L) (m T D : ℕ) : 1 ≤ iterated m L T D := by
  cases D
  · exact hL
  · exact pathCoefficient_one _ _ _

end QuantumCoefficientPrograms

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListMergeProperties
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The merged tape has one strictly ordered edge per occurring vertex pair,
and its coefficients grow by at most the original edge count. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open MediatorListProgram

theorem weight_abs_le (xs : List Bond) (p : Pair) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ e ∈ xs, |(e.2.2:ℝ)| ≤ L) :
    |(weight xs p:ℝ)| ≤ xs.length*L := by
  induction xs with
  | nil => simp [weight]
  | cons e xs ih =>
    have he := h e List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have hone : |((if ordered e=p then e.2.2 else 0:ℚ):ℝ)| ≤ L := by
      by_cases hp : ordered e=p
      · simpa only [ite_eq_left hp] using he
      · simpa only [ite_eq_right hp,Rat.cast_zero,abs_zero] using hL
    change |(((if ordered e=p then e.2.2 else 0:ℚ)+weight xs p:ℚ):ℝ)| ≤ _
    rw [Rat.cast_add]
    have ha := abs_add_le ((if ordered e=p then e.2.2 else 0:ℚ):ℝ) (weight xs p:ℝ)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

end ContinuumCoulomb.QuantumListMerge

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Validity, fixed-round termination and full-space energy bounds for the
literal list-work routing compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open Matrix MediatorListProgram

theorem partition_lengths (xs : List Entry) :
    (partition false xs).length+(partition true xs).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    by_cases he : e.1=0 <;> simp [partition,selected,he] at ih ⊢ <;> omega

end ContinuumCoulomb.QuantumListSchedule

end

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

theorem iterate_state (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).1=QuantumListSchedule.iterate N k s.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change QuantumListSchedule.value (N,(iterate N k s).1)=_
    rw [ih]
    rfl

end ContinuumCoulomb.QuantumListRouteProgram

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact calibration equality between the literal selected-weight sums and
the finite graph's rational subdivision scale. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped BigOperators Classical

private theorem univ_eq {α : Type} (a b : Fintype α) :
    @Finset.univ α a = @Finset.univ α b :=
  congrArg (fun i : Fintype α => @Finset.univ α i) (Subsingleton.elim a b)

theorem partition_sum (b : Bool) (xs : List Entry) (f : Entry → ℚ) :
    ((partition b xs).map f).sum = ∑ i : Fin (partition b xs).length, f ((partition b xs).get i) := by
  have h : List.ofFn (fun i => f ((partition b xs).get i))=(partition b xs).map f := by
    simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map (partition b xs) f
  rw [← h,List.sum_ofFn]

theorem active_sum (s : State) (hs : Valid s) (f : Entry → ℚ) :
    (∑ i : Fin (partition true s.2.2).length, f ((partition true s.2.2).get i)) =
      ∑ j : Fin (schedule s hs).active.card,
        f (s.2.2.get (qmaSelectedIndex (schedule s hs).active j)) := by
  have h := (activePermutation s hs).sum_comp
    (fun j => f (s.2.2.get (qmaSelectedIndex (schedule s hs).active j)))
  simpa only [active_source] using h

theorem retained_sum (s : State) (hs : Valid s) (f : Entry → ℚ) :
    (∑ i : Fin (partition false s.2.2).length, f ((partition false s.2.2).get i)) =
      ∑ j : {j : (graph s hs).Edge // j ∉ (schedule s hs).active}, f (s.2.2.get j.val) := by
  have h := (retainedEquiv s hs).sum_comp (fun j => f (s.2.2.get j.val))
  simpa only [retained_source] using h

theorem scale_eq (N : ℚ) (s : State) (hs : Valid s) :
    (QuantumListPathStep.parameters (stepInput (N,s))).2.2 =
      (graph s hs).pathScale (schedule s hs).active N := by
  let S := (schedule s hs).active
  let p := QuantumListPathStep.scaleInput (stepInput (N,s))
  let A : ℚ := 3*(∑ j : Fin S.card, (1+2*|(graph s hs).weight (qmaSelectedIndex S j)|))
  let B : ℚ := 3*(∑ j : {j : (graph s hs).Edge // j ∉ S}, |(graph s hs).weight j.val|)+|(graph s hs).constant|
  let D : ℚ := B+4*(∑ j : Fin S.card, (1+|(graph s hs).weight (qmaSelectedIndex S j)|)^2)
  have ha : QuantumPathScaleProgram.active p=A := by
    have h := congrArg (fun z : ℚ => 3*z)
      ((partition_sum true s.2.2 (fun e => 1+2*|e.2.2.2|)).trans
        (active_sum s hs (fun e => 1+2*|e.2.2.2|)))
    simpa only [A,S,graph,QuantumPathScaleProgram.active,p,QuantumListPathStep.scaleInput,stepInput,
      erase,List.map_map,Function.comp_def,QuantumPathScaleProgram.linearCost] using h
  have hb : QuantumPathScaleProgram.base p=B := by
    have h := congrArg (fun z : ℚ => 3*z+|s.2.1|)
      ((partition_sum false s.2.2 (fun e => |e.2.2.2|)).trans
        (retained_sum s hs (fun e => |e.2.2.2|)))
    simpa only [B,S,graph,QuantumPathScaleProgram.base,p,QuantumListPathStep.scaleInput,stepInput,
      erase,List.map_map,Function.comp_def] using h
  have hsq : (p.2.2.map QuantumPathScaleProgram.squareCost).sum =
      ∑ j : Fin S.card, (1+|(graph s hs).weight (qmaSelectedIndex S j)|)^2 := by
    have h := (partition_sum true s.2.2 (fun e => (1+|e.2.2.2|)^2)).trans
      (active_sum s hs (fun e => (1+|e.2.2.2|)^2))
    simpa only [S,graph,p,QuantumListPathStep.scaleInput,stepInput,erase,List.map_map,
      Function.comp_def,QuantumPathScaleProgram.squareCost] using h
  have hd : QuantumPathScaleProgram.correction p=D := by
    change QuantumPathScaleProgram.base p+4*(p.2.2.map QuantumPathScaleProgram.squareCost).sum=D
    rw [hb,hsq]
  change QuantumPathScaleProgram.value p = _
  unfold QuantumPathScaleProgram.value
  rw [ha,hd]
  simp only [A,B,D,S,p,QuantumListPathStep.scaleInput,stepInput,
    QMARationalExchangeGraph.pathScale,graph]
  congr!
  all_goals first | (cases ‹HEq _ _›; rfl) | apply univ_eq

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coefficients and scalar offset of the literal scheduled subdivision.
The edge labels agree with the geometry relabeling. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped BigOperators Classical

private theorem selected_bond (x : Input) (i : Fin (partition true x.2.2.2).length) :
    blockBondInput (indexed (i.val,x)) =
      (QuantumListPathStep.parameters (stepInput x),i.val,((partition true x.2.2.2).get i).2) := by
  have h : (indexed (i.val,x)).2.2=(partition true x.2.2.2).get i := by
    change ((partition true x.2.2.2).drop i.val).headD zeroEntry = _
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem i.isLt]
    rfl
  change (QuantumListPathStep.parameters (stepInput x),i.val,(indexed (i.val,x)).2.2.2) = _
  rw [h]

theorem next_weight_tag (N : ℚ) (s : State) (hs : Valid s) (t : Tags (N,s)) :
    (graph (value (N,s)) (value_valid (N,s) hs)).weight ((tagEquiv (N,s)).symm t) =
      ((schedule s hs).next N).graph.weight (tagEdge (N,s) hs t) := by
  change ((value (N,s)).2.2.get ((tagEquiv (N,s)).symm t)).2.2.2 = _
  rw [tagEquiv_get,Equiv.apply_symm_apply]
  rcases t with i | ⟨i,k⟩
  · exact (congrArg (fun e : Entry => e.2.2.2) (retained_source s hs i)).symm
  · change QuantumListPathProgram.coefficient (blockBondInput (indexed (i.val,(N,s)))) k.castSucc = _
    unfold QuantumListPathProgram.coefficient
    rw [selected_bond]
    simp only [QuantumListPathStep.parameters,stepInput]
    change QuantumPathCode.coefficients (false,
      (QuantumListPathStep.parameters (stepInput (N,s))).2.2,
      ((partition true s.2.2).get i).2.2.2) k.castSucc = _
    rw [scale_eq N s hs]
    have he := congrArg (fun e : Entry => e.2.2.2) (active_source s hs i)
    rw [← he]
    fin_cases k <;> rfl

theorem next_weight (N : ℚ) (s : State) (hs : Valid s)
    (i : Fin (value (N,s)).2.2.length) :
    (graph (value (N,s)) (value_valid (N,s) hs)).weight i =
      ((schedule s hs).next N).graph.weight (nextEdge (N,s) hs i) := by
  have h := next_weight_tag N s hs (tagEquiv (N,s) i)
  have hi : (tagEquiv (N,s)).symm (tagEquiv (N,s) i)=i := Equiv.symm_apply_apply _ _
  have he := nextEdge_tag (N,s) hs (tagEquiv (N,s) i)
  exact (congrArg (graph (value (N,s)) (value_valid (N,s) hs)).weight hi).symm.trans
    (h.trans (congrArg ((schedule s hs).next N).graph.weight
      ((congrArg (nextEdge (N,s) hs) hi).symm.trans he).symm))

theorem next_constant (N : ℚ) (s : State) (hs : Valid s) :
    (graph (value (N,s)) (value_valid (N,s) hs)).constant =
      ((schedule s hs).next N).graph.constant := by
  let R := (graph s hs).pathScale (schedule s hs).active N
  have hsum := (partition_sum true s.2.2
    (fun e => (3/4:ℚ)+3*e.2.2.2^2+3*R^2)).trans
      (active_sum s hs (fun e => (3/4:ℚ)+3*e.2.2.2^2+3*R^2))
  change s.2.1+QuantumListPathProgram.familyOffset
      (QuantumListPathStep.parameters (stepInput (N,s)),erase (partition true s.2.2)) = _
  unfold QuantumListPathProgram.familyOffset QuantumListPathProgram.offset
    QuantumListPathProgram.coefficient
  simp only [erase,List.map_map,Function.comp_def]
  change s.2.1+((partition true s.2.2).map (fun e =>
      (3/4:ℚ)+3*e.2.2.2^2+3*(QuantumListPathStep.parameters (stepInput (N,s))).2.2^2)).sum = _
  rw [scale_eq N s hs]
  change s.2.1+((partition true s.2.2).map (fun e => (3/4:ℚ)+3*e.2.2.2^2+3*R^2)).sum = _
  rw [hsum,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change s.2.1+((∑ i : Fin (schedule s hs).active.card,
      ((3/4:ℚ)+3*(s.2.2.get (qmaSelectedIndex (schedule s hs).active i)).2.2.2^2))+
        (schedule s hs).active.card*(3*R^2)) = _
  change _ = (s.2.1+∑ i : Fin (schedule s hs).active.card,
      ((3/4:ℚ)+3*(s.2.2.get (qmaSelectedIndex (schedule s hs).active i)).2.2.2^2))+
        3*(schedule s hs).active.card*R^2
  ring

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient bounds for the actual finite output tape of the
fixed-round subdivision program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped Classical

theorem value_edge_count (x : Input) : (value x).2.2.length≤3*x.2.2.2.length := by
  rw [value_length]
  have h := partition_lengths x.2.2.2
  omega

theorem iterate_edge_count (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).2.2.length≤3^k*s.2.2.length := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    exact (value_edge_count (N,iterate N k s)).trans
      ((Nat.mul_le_mul_left 3 ih).trans_eq (by rw [pow_succ]; ac_rfl))

theorem value_coefficientBound {N : ℚ} (hN : 0 ≤ N) (s : State) (hs : Valid s)
    {m L T : ℝ} (hm : (s.2.2.length:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : (graph s hs).CoefficientBound L) :
    (graph (value (N,s)) (value_valid (N,s) hs)).CoefficientBound
      (qmaPathCoefficientBound m L T) := by
  have hm' : (Fintype.card (graph s hs).Edge:ℝ) ≤ m := by
    have hcard : Fintype.card (graph s hs).Edge=s.2.2.length :=
      (Fintype.card_congr (α := (graph s hs).Edge) (β := Fin s.2.2.length)
        (Equiv.refl _)).trans (Fintype.card_fin _)
    exact (congrArg (fun n : ℕ => (n:ℝ)) hcard).le.trans hm
  have h := (graph s hs).subdivide_coefficientBound (schedule s hs).active
    (fun _ => false) hN hm' hL hT hc
  constructor
  · exact (congrArg (fun q : ℚ => |(q:ℝ)|) (next_constant N s hs)).le.trans h.1
  · intro e
    exact (congrArg (fun q : ℚ => |(q:ℝ)|) (next_weight N s hs e)).le.trans (h.2 _)

theorem iterate_coefficientBound {N : ℚ} (hN : 0 ≤ N) (s : State) (hs : Valid s)
    {m L T : ℝ} (hm : (s.2.2.length:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : (graph s hs).CoefficientBound L) (k : ℕ) :
    (graph (iterate N k s) (iterate_valid N s hs k)).CoefficientBound
      (qmaPathIteratedBound m L T k) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  induction k with
  | zero => exact hc
  | succ k ih =>
    have hcount : ((iterate N k s).2.2.length:ℝ) ≤ 3^k*m := by
      have hcast : ((iterate N k s).2.2.length:ℝ) ≤ 3^k*(s.2.2.length:ℝ) := by
        exact_mod_cast iterate_edge_count N s k
      exact hcast.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    exact value_coefficientBound hN (iterate N k s) (iterate_valid N s hs k)
      hcount (qmaPathIteratedBound_one hm0 hL k) hT ih

end ContinuumCoulomb.QuantumListSchedule

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

theorem valid : QuantumListSchedule.Valid
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1 := by
  rw [state_eq I hA]
  exact QuantumPackedSchedule.valid I.model.exchangeGraph (Equiv.refl _)
    (I.model.coarseLength I.model_degree)

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMergedCoefficientBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Merging the actual bond tape reduces its length and increases each
coefficient by at most the input length. These bounds apply directly to the
numeric graph used by the final route compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open MediatorListProgram

theorem value_length_le_input (n : ℕ) (xs : List Bond) :
    (value n xs).length ≤ xs.length := by
  have hs : support n xs ⊆ xs.map ordered := by
    intro p hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  have h := (support_nodup n xs).length_le_of_subset hs
  simpa only [value,List.length_map] using h

theorem value_coefficient_bound (n : ℕ) (xs : List Bond) {L : ℝ}
    (hL : 0 ≤ L) (hw : ∀ e ∈ xs, |(e.2.2 : ℝ)| ≤ L) :
    ∀ e ∈ value n xs, |(e.2.2 : ℝ)| ≤ xs.length*L := by
  intro e he
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp he
  exact weight_abs_le xs p hL hw

end ContinuumCoulomb.QuantumListMerge

namespace ContinuumCoulomb.QuantumPlanarTapeGeometry
open QuantumPlanarTapeProgram
open scoped Classical

theorem graph_count (x : Input) (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    Fintype.card (graph x hn).Edge ≤ x.1.1.2.1.length := by
  change Fintype.card (Fin (merged x).length) ≤ _
  rw [Fintype.card_fin]
  exact QuantumListMerge.value_length_le_input _ _

theorem graph_coefficientBound (x : Input)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) {m L : ℝ}
    (hm : (x.1.1.2.1.length : ℝ) ≤ m) (hL : 0 ≤ L)
    (hc : |(x.1.1.2.2 : ℝ)| ≤ L)
    (hw : ∀ e ∈ x.1.1.2.1, |(e.2.2 : ℝ)| ≤ L) :
    (graph x hn).CoefficientBound ((m+1)*L) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  constructor
  · change |(x.1.1.2.2 : ℝ)| ≤ _
    nlinarith
  · intro e
    have h := QuantumListMerge.value_coefficient_bound x.1.1.1 x.1.1.2.1 hL hw
      _ (List.get_mem (merged x) e)
    change |(((merged x).get e).2.2 : ℝ)| ≤ _
    exact h.trans ((mul_le_mul_of_nonneg_right hm hL).trans (by nlinarith))

end ContinuumCoulomb.QuantumPlanarTapeGeometry

namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumPlanarTapeProgram
open scoped Classical

variable {G : QMARationalExchangeGraph} {r k : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin k)

theorem compiled_planar_bounds {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card G.Edge : ℝ) ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) (x : QuantumPlanarTapeProgram.Input)
    (hx : x.1.1 = QuantumCrossingListLayer.value
      (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _)))
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    (QuantumPlanarTapeGeometry.graph x hn).CoefficientBound
      ((m+9*r+1)*qmaCrossingCoefficientBound m r ((m+1)*L) T) ∧
    (Fintype.card (QuantumPlanarTapeGeometry.graph x hn).Edge : ℝ) ≤ m+9*r := by
  let E := qmaCrossingCoefficientBound m r ((m+1)*L) T
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hE : 0 ≤ E := by
    dsimp [E,qmaCrossingCoefficientBound]
    positivity
  have hout := computedLayer_output_coefficientBound S labels hN hm hL hT hc
  have hlen : (x.1.1.2.1.length : ℝ) ≤ m+9*r := by
    rw [hx]
    change ((QuantumCrossingListLayer.bonds
      (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _))).length : ℝ)
      ≤ m+9*r
    have h := compiled_graph_count S labels hm N
    change (Fintype.card (Fin (QuantumCrossingListLayer.bonds
      (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _))).length) : ℝ)
      ≤ m+9*r at h
    simpa only [Fintype.card_fin] using h
  constructor
  · apply QuantumPlanarTapeGeometry.graph_coefficientBound x hn hlen hE
    · rw [hx]
      change |(QuantumCrossingListLayer.constant
        (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _)) : ℝ)| ≤ E
      rw [QuantumCrossingListLayer.constant_actual (computedLayer S labels) N (Equiv.refl _)]
      exact hout.1
    · intro e he
      rw [hx] at he
      exact QuantumCrossingListLayer.actual_bonds_coefficientBound _ _ _ hout e he
  · have h : (Fintype.card (QuantumPlanarTapeGeometry.graph x hn).Edge : ℝ) ≤
        (x.1.1.2.1.length : ℝ) := by
      exact_mod_cast QuantumPlanarTapeGeometry.graph_count x hn
    exact h.trans hlen

theorem compiled_planar_nat {N : ℚ} (hN : 0 ≤ N) {m L T : ℕ}
    (hm : Fintype.card G.Edge ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) (x : QuantumPlanarTapeProgram.Input)
    (hx : x.1.1 = QuantumCrossingListLayer.value
      (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _)))
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    (QuantumPlanarTapeGeometry.graph x hn).CoefficientBound
      ((m+9*r+1)*QuantumCoefficientPrograms.crossingCoefficient m r ((m+1)*L) T) ∧
    Fintype.card (QuantumPlanarTapeGeometry.graph x hn).Edge ≤ m+9*r := by
  have hm' : (Fintype.card G.Edge : ℝ) ≤ m := by exact_mod_cast hm
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h := compiled_planar_bounds S labels hN hm' hL' hT hc x hx hn
  constructor
  · simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
      QuantumCoefficientPrograms.crossingCoefficient_cast] using h.1
  · exact_mod_cast h.2

end ContinuumCoulomb.QuantumCrossingSelectProgram

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

theorem old_positions_order :
    ∃ σ : Fin (oldPacket A D (N,QuantumSpatialInputTape.input I)).1 ≃
      Fin ((I.model.portRouteData hA I.model_degree).finishedGraph N
        (QuantumSpatialPortProgram.rounds A D)).n,
      oldPositions A D (N,QuantumSpatialInputTape.input I) =
        List.ofFn (fun v => (I.model.portRouteData hA I.model_degree).finishedPosition N
          (QuantumSpatialPortProgram.rounds A D) (σ v)) := by
  obtain ⟨hk,Pk,Ek,hrep,hpos,_⟩ := QuantumSpatialPortProgram.value_matches I hA N
  refine ⟨Ek.vertex,hrep.1.trans ?_⟩
  apply congrArg List.ofFn
  funext v
  exact (hpos v).symm

theorem sites_positions_order :
    ∃ (σ : Fin (oldPacket A D (N,QuantumSpatialInputTape.input I)).1 ≃
      Fin ((I.model.portRouteData hA I.model_degree).finishedGraph N
        (QuantumSpatialPortProgram.rounds A D)).n)
      (τ : Fin (cells A D (N,QuantumSpatialInputTape.input I)).length ≃
        Fin (I.model.portRouteData hA I.model_degree).crossingCells.card),
      sites A D (N,QuantumSpatialInputTape.input I) =
        List.ofFn (QuantumCrossingSelectProgram.encodedSites
          (fun i a => σ.symm ((I.model.portRouteData hA I.model_degree).crossingSiteFin N
            (length_bound I hA) (τ i) a))) ∧
      positions A D (N,QuantumSpatialInputTape.input I) =
        List.ofFn (fun v => (I.model.portRouteData hA I.model_degree).crossingPosition N
          (QuantumSpatialPortProgram.rounds A D)
          (QuantumCrossingPositionProgram.extend _ _ _ σ τ v)) := by
  obtain ⟨σ,hσ⟩ := old_positions_order I hA N
  obtain ⟨τ,hτ⟩ := cells_order I hA N
  refine ⟨σ,τ,?_,?_⟩
  · unfold sites
    apply (congrArg QuantumCrossingSiteProgram.allSites
      (congrArg₂ Prod.mk hσ hτ)).trans
    exact QuantumCrossingSiteProgram.allSites_reordered _ N (length_bound I hA) σ
      (fun v => (I.model.portRouteData hA I.model_degree).finishedPosition N
        (QuantumSpatialPortProgram.rounds A D) (σ v)) (fun _ => rfl) τ
  · unfold positions
    apply (congrArg QuantumCrossingPositionProgram.positions
      (congrArg₂ Prod.mk hτ hσ)).trans
    exact QuantumCrossingPositionProgram.positions_reordered _ _ _ σ τ

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialPortBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient and edge-count bounds for the actual port schedule tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPackedSchedule
open QuantumListSchedule

theorem state_coefficientBound (G : QMARationalExchangeGraph) {m : ℕ}
    (labels : G.Edge ≃ Fin m) (work : G.Edge → ℕ) {L : ℝ}
    (hc : G.CoefficientBound L) :
    (graph (state G labels work) (valid G labels work)).CoefficientBound L := by
  constructor
  · exact hc.1
  · intro i
    change |(((List.ofFn (fun j : Fin m => (work (labels.symm j),
      (G.left (labels.symm j)).val,(G.right (labels.symm j)).val,G.weight (labels.symm j)))).get i).2.2.2:ℝ)| ≤ L
    have he := List.get_ofFn (fun j : Fin m => (work (labels.symm j),
      (G.left (labels.symm j)).val,(G.right (labels.symm j)).val,G.weight (labels.symm j))) i
    exact (congrArg (fun e : QuantumListSchedule.Entry => |(e.2.2.2:ℝ)|) he).le.trans (hc.2 _)

end ContinuumCoulomb.QuantumPackedSchedule

namespace ContinuumCoulomb.QuantumSpatialPortProgram
open QuantumForkList QuantumListSchedule
open scoped Classical

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D)
include hA

theorem initial_count : (initial A D (QuantumSpatialInputTape.input I)).1.2.2.length =
    Fintype.card I.model.Term := by
  have h := congrArg (fun s : QuantumListSchedule.State => s.2.2.length)
    (QuantumPortSchedulePacking.state_eq I hA)
  have hc : Fintype.card I.model.Term = (QuantumForkList.fullList I.state).length :=
    Fintype.card_fin _
  exact (h.trans (List.length_ofFn)).trans hc.symm

theorem initial_coefficientBound (hs : Valid (initial A D (QuantumSpatialInputTape.input I)).1)
    {L : ℝ} (hc : I.model.exchangeGraph.CoefficientBound L) :
    (graph (initial A D (QuantumSpatialInputTape.input I)).1 hs).CoefficientBound L := by
  have he := QuantumPortSchedulePacking.state_eq I hA
  have h := QuantumPackedSchedule.state_coefficientBound I.model.exchangeGraph (Equiv.refl _)
    (I.model.coarseLength I.model_degree) hc
  have transfer (t : QuantumListSchedule.State) (ht : Valid t)
      (e : t = QuantumPackedSchedule.state I.model.exchangeGraph (Equiv.refl _)
        (I.model.coarseLength I.model_degree)) : (graph t ht).CoefficientBound L := by
    subst t
    exact h
  exact transfer _ hs he

theorem value_bounds {N : ℚ} (hN : 0 ≤ N) {L T : ℕ} (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : I.model.exchangeGraph.CoefficientBound L) :
    ∃ hs : Valid (value A D (N,QuantumSpatialInputTape.input I)).1,
      (graph (value A D (N,QuantumSpatialInputTape.input I)).1 hs).CoefficientBound
        (QuantumCoefficientPrograms.iterated (Fintype.card I.model.Term) L T (rounds A D)) ∧
      (value A D (N,QuantumSpatialInputTape.input I)).1.2.2.length ≤
        3^(rounds A D)*Fintype.card I.model.Term := by
  let s := (initial A D (QuantumSpatialInputTape.input I)).1
  have hs : Valid s := QuantumPortSchedulePacking.valid I hA
  have hm : (s.2.2.length:ℝ) ≤ Fintype.card I.model.Term := by
    exact_mod_cast (initial_count I hA).le
  have hbound := iterate_coefficientBound hN s hs (L := (L:ℝ)) (T := (T:ℝ)) hm (by exact_mod_cast hL) hT
    (initial_coefficientBound I hA hs hc) (rounds A D)
  have hlen := iterate_edge_count N s (rounds A D)
  change (QuantumListSchedule.iterate N (rounds A D) s).2.2.length ≤
    3^(rounds A D)*(initial A D (QuantumSpatialInputTape.input I)).1.2.2.length at hlen
  rw [initial_count I hA] at hlen
  have he : (value A D (N,QuantumSpatialInputTape.input I)).1 =
      QuantumListSchedule.iterate N (rounds A D) s :=
    QuantumListRouteProgram.iterate_state N (initial A D (QuantumSpatialInputTape.input I)) (rounds A D)
  refine ⟨he.symm ▸ iterate_valid N s hs (rounds A D),?_,?_⟩
  · have transfer (t : QuantumListSchedule.State) (ht : Valid t)
        (e : t = QuantumListSchedule.iterate N (rounds A D) s) :
        (graph t ht).CoefficientBound
          (QuantumCoefficientPrograms.iterated (Fintype.card I.model.Term) L T (rounds A D)) := by
      subst t
      simpa only [QuantumCoefficientPrograms.iterated_cast] using hbound
    exact transfer _ _ he
  · exact (congrArg (fun t : QuantumListSchedule.State => t.2.2.length) he).le.trans hlen

end ContinuumCoulomb.QuantumSpatialPortProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialPlanarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual merged crossing packet satisfies the same polynomial
envelope as the physical construction, including parallel-edge sums. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open QuantumForkList QuantumCrossingSelectProgram QuantumCoefficientPrograms
open scoped Classical

theorem planar_bounds_oai {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 ≤ N) {L T : ℕ}
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : I.model.exchangeGraph.CoefficientBound L)
    (hn : ∀ e ∈ (value A D (N,QuantumSpatialInputTape.input I)).1.1.2.1, e.1 ≠ e.2.1) :
    let K := QuantumSpatialPortProgram.rounds A D
    let m := 3^K*Fintype.card I.model.Term
    let r := (I.model.portRouteData hA I.model_degree).crossingCells.card
    let B := iterated (Fintype.card I.model.Term) L T K
    (QuantumPlanarTapeGeometry.graph (value A D (N,QuantumSpatialInputTape.input I)) hn).CoefficientBound
      ((m+9*r+1)*crossingCoefficient m r ((m+1)*B) T) ∧
    Fintype.card (QuantumPlanarTapeGeometry.graph
      (value A D (N,QuantumSpatialInputTape.input I)) hn).Edge ≤ m+9*r := by
  let P := I.model.portRouteData hA I.model_degree
  let s := (QuantumSpatialPortProgram.value A D (N,QuantumSpatialInputTape.input I)).1
  obtain ⟨hs,hC,hcount⟩ := QuantumSpatialPortProgram.value_bounds I hA hN hL hT hc
  obtain ⟨σ,τ,hsite,_⟩ := sites_positions_order I hA N
  let site := fun i a => σ.symm (P.crossingSiteFin N (length_bound I hA) (τ i) a)
  have hsi (i) : Function.Injective (site i) := by
    intro a b hab
    exact P.crossingSiteFin_injective N (length_bound I hA) (τ i) (σ.symm.injective hab)
  let H := QuantumListSchedule.graph s hs
  let S := H.crossingSelection site hsi
  have hx : (value A D (N,QuantumSpatialInputTape.input I)).1.1 =
      QuantumCrossingListLayer.value
        (QuantumCrossingListLayer.actualInput (computedLayer S (Equiv.refl _)) N (Equiv.refl _)) := by
    have hp := QuantumListSchedule.graph_packed s hs
    have h := compiled_packet S (Equiv.refl _) N
    have hh := congrArg (fun bs => QuantumCrossingSelectProgram.value
      (N,(s.1,bs,s.2.1),List.ofFn (encodedSites site))) hp.symm
    have hv := congrArg QuantumCrossingListLayer.value (hh.trans h)
    change QuantumCrossingListLayer.value (QuantumCrossingSelectProgram.value
      (N,oldPacket A D (N,QuantumSpatialInputTape.input I),
        sites A D (N,QuantumSpatialInputTape.input I))) = _
    rw [hsite]
    exact hv
  have hm : Fintype.card H.Edge ≤ 3^(QuantumSpatialPortProgram.rounds A D)*Fintype.card I.model.Term := by
    simpa only [H,QuantumListSchedule.graph,Fintype.card_fin] using hcount
  have hB : 1 ≤ iterated (Fintype.card I.model.Term) L T (QuantumSpatialPortProgram.rounds A D) :=
    iterated_one hL _ _ _
  have h := compiled_planar_nat S (Equiv.refl _) hN hm hB hT hC
    (value A D (N,QuantumSpatialInputTape.input I)) hx hn
  have hr : (cells A D (N,QuantumSpatialInputTape.input I)).length = P.crossingCells.card :=
    (Fintype.card_fin _).symm.trans ((Fintype.card_congr τ).trans (Fintype.card_fin _))
  simpa only [hr] using h

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.planar_bounds_oai := @OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.planar_bounds_oai
