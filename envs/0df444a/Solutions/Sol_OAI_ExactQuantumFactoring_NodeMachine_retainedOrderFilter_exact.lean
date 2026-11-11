-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter_exact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:12:12.79548+00:00
-- url     : https://prove2.me/submissions/7fa1239d-afa7-4f84-a9e6-2e1934875fcd

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_ExactQuantumFactoring
import Definitions.Def_OAIQ222A004

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanNetwork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring

namespace BoolNode

lemma eval_map {n m : ℕ} (f : Fin n → Fin m) (o : BoolNode n) (x : Fin m → Bool) :
    (o.map f).eval x = o.eval (x ∘ f) := by cases o <;> rfl

end BoolNode

namespace BoolNet

lemma eval_input {n k : ℕ} (p : BoolNet n k) (x : Fin n → Bool) (i : Fin n) :
    p.eval x (i.castLE p.input_le) = x i := by
  induction p with
  | input => rfl
  | add p o ih =>
    have he : i.castLE (p.add o).input_le = (i.castLE p.input_le).castSucc := rfl
    rw [he, eval_add_castSucc, ih]

lemma attach_eval {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l)
    (x : Fin n → Bool) :
    (a.attach ρ b).2.1.eval x ∘ (a.attach ρ b).2.2 = b.eval (a.eval x ∘ ρ) := by
  induction b with
  | input => rfl
  | @add l b o ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [attach, Function.comp_apply, Fin.snoc_last, eval_add_last, BoolNode.eval_map]
      rw [ih]
    · simp only [attach, Function.comp_apply, Fin.snoc_castSucc, eval_add_castSucc]
      exact congrFun ih j

lemma attach_preserve {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l)
    (x : Fin n → Bool) (i : Fin k) :
    (a.attach ρ b).2.1.eval x (i.castLE (a.attach_le ρ b)) = a.eval x i := by
  induction b with
  | input => rfl
  | add b o ih =>
    change ((a.attach ρ b).2.1.add (o.map (a.attach ρ b).2.2)).eval x
      (i.castLE (a.attach_le ρ b)).castSucc = _
    rw [eval_add_castSucc, ih]

end BoolNet


end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanNetworkFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring

namespace BooleanNetwork

lemma eval_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l)
    (x : Fin n → Bool) : (a.comp b).eval x = b.eval (a.eval x) := by
  change ((a.net.attach a.output b.net).2.1.eval x ∘ (a.net.attach a.output b.net).2.2) ∘
    b.output = _
  rw [BoolNet.attach_eval]
  rfl

lemma eval_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l)
    (x : Fin n → Bool) : (a.pair b).eval x = Fin.append (a.eval x) (b.eval x) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [pair, eval, Function.comp_apply, Fin.append_left]
    exact BoolNet.attach_preserve _ _ _ _ _
  · simp only [pair, eval, Function.comp_apply, Fin.append_right]
    have he := congrFun (BoolNet.attach_eval a.net (fun i => i.castLE a.net.input_le) b.net x) (b.output j)
    have hi : a.net.eval x ∘ (fun i : Fin n => i.castLE a.net.input_le) = x := by
      funext j
      exact BoolNet.eval_input _ _ _
    rw [hi] at he
    exact he

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanAlgebra
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.BooleanNetwork

@[simp] lemma eval_bnot {n : ℕ} (a : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    a.bnot.eval x j = !(a.eval x 0) := by simp [bnot, eval_comp, BoolNode.eval]

@[simp] lemma eval_band {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.band b).eval x j = (a.eval x 0 && b.eval x 0) := by
  simp only [band, eval_comp, eval_node, BoolNode.eval, eval_pair]
  rfl

@[simp] lemma eval_bor {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.bor b).eval x j = (a.eval x 0 || b.eval x 0) := by
  simp [bor]

@[simp] lemma eval_bxor {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.bxor b).eval x j = Bool.xor (a.eval x 0) (b.eval x 0) := by
  simp only [bxor, eval_bor, eval_band, eval_bnot]
  cases a.eval x 0 <;> cases b.eval x 0 <;> rfl

@[simp] lemma eval_mux {n : ℕ} (c a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (mux c a b).eval x j = if c.eval x 0 then a.eval x 0 else b.eval x 0 := by
  simp only [mux, eval_bor, eval_band, eval_bnot]
  cases c.eval x 0 <;> simp

lemma eval_assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) (x : Fin n → Bool) :
    (assign i v).eval x = Function.update x i (v.eval x 0) := by
  funext j
  simp only [assign, eval_rewire, Function.comp_apply, eval_pair, eval_select]
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanVector
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


open scoped BigOperators
namespace ExactQuantumFactoring.BooleanNetwork

@[simp] lemma eval_vector {n m : ℕ} (f : Fin m → BooleanNetwork n 1)
    (x : Fin n → Bool) (i : Fin m) : (vector f).eval x i = (f i).eval x 0 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [vector, eval_pair, Fin.append_right_eq_snoc]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc]
      exact ih _ j

lemma eval_padRight (n m : ℕ) (x : Fin n → Bool) :
    (padRight n m).eval x = Fin.append x (fun _ => false) := by
  funext i
  rw [padRight, eval_vector]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [j.isLt]
  · simp

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGCompiler
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

open BooleanNetwork Std.Sat

namespace AIGCompiler

variable {n : ℕ} (g : AIG (Fin n))

lemma fanin_eval (f : AIG.Fanin) (h : f.gate < g.decls.size) (x : Fin (n+g.decls.size) → Bool) :
    (faninNet g f).eval x 0 = Bool.xor (x (graphWire g ⟨f.gate,h⟩)) f.invert := by
  simp only [faninNet, dite_eq_left h]
  cases f.invert <;> simp

lemma node_eval (i : Fin g.decls.size) (x : Fin n → Bool)
    (y : Fin (n+g.decls.size) → Bool)
    (hi : ∀ j, y (j.castAdd g.decls.size) = x j)
    (hg : ∀ j : Fin g.decls.size, j.val < i.val → y (graphWire g j) = nodeDenote g x j) :
    (nodeNet g i).eval y 0 = nodeDenote g x i := by
  unfold nodeNet nodeDenote
  cases h : g.decls[i.val] with
  | false => simpa only [eval_constant] using (AIG.denote_idx_false (assign := x) (invert := false) h).symm
  | atom v => simpa only [eval_bit, hi, Bool.xor_false] using (AIG.denote_idx_atom (assign := x) (invert := false) h).symm
  | gate a b =>
    have hab := g.hdag i.isLt h
    dsimp only
    rw [eval_band, fanin_eval g a (by omega), fanin_eval g b (by omega),
      hg ⟨a.gate, by omega⟩ hab.1, hg ⟨b.gate, by omega⟩ hab.2]
    have he := (AIG.denote_idx_gate (assign := x) (invert := false) h).symm
    simpa only [AIG.denote, nodeDenote, Bool.xor_false] using he

lemma graph_input (k : ℕ) (h : k ≤ g.decls.size) (x : Fin (n+g.decls.size) → Bool) (j : Fin n) :
    (partialGraph g k h).eval x (j.castAdd g.decls.size) = x (j.castAdd g.decls.size) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [partialGraph, eval_comp, nodeStep, eval_assign, Function.update_of_ne, ih]
    intro he
    have := congrArg Fin.val he
    simp [graphWire] at this
    omega

lemma graph_value (k : ℕ) (h : k ≤ g.decls.size) (x : Fin (n+g.decls.size) → Bool)
    (j : Fin g.decls.size) (hj : j.val < k) :
    (partialGraph g k h).eval x (graphWire g j) =
      nodeDenote g (fun i => x (i.castAdd g.decls.size)) j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [partialGraph, eval_comp, nodeStep, eval_assign]
    by_cases hjk : j.val = k
    · have hj' : j = ⟨k, by omega⟩ := Fin.ext hjk
      rw [hj', Function.update_self]
      apply node_eval g
      · exact fun i => graph_input g k (by omega) x i
      · exact fun i hi => ih (by omega) i (by simpa using hi)
    · rw [Function.update_of_ne]
      · exact ih (by omega) j (by omega)
      · intro he
        have := congrArg Fin.val he
        simp [graphWire] at this
        omega

/-- The circuit interpreter's own, already verified, AIG semantics is preserved
by a retained-trace network of at most five nodes per AIG declaration. -/
theorem graph_correct (x : Fin (n+g.decls.size) → Bool) (j : Fin g.decls.size) :
    (partialGraph g g.decls.size le_rfl).eval x (graphWire g j) =
      nodeDenote g (fun i => x (i.castAdd g.decls.size)) j :=
  graph_value g _ le_rfl x j j.isLt

lemma compile_correct {m : ℕ} (refs : Fin m → AIG.Ref g) (x : Fin n → Bool) (i : Fin m) :
    (compile g refs).eval x i = AIG.denote x ⟨g, refs i⟩ := by
  rw [compile, eval_comp, eval_comp, eval_vector, fanin_eval g _ (by simpa using (refs i).hgate),
    graph_correct, eval_padRight]
  have he : (fun j : Fin n => Fin.append x (fun _ : Fin g.decls.size => false)
      (j.castAdd g.decls.size)) = x := by funext j; exact Fin.append_left ..
  rw [he]
  simp only [nodeDenote, AIG.denote, Bool.xor_false, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

lemma compileVec_correct {w : ℕ} (refs : AIG.RefVec g w) (x : Fin n → Bool) (i : Fin w) :
    (compileVec g refs).eval x i = AIG.denote x ⟨g, refs.get i.val i.isLt⟩ :=
  compile_correct ..

end AIGCompiler
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGInputs
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGCompiler
open Std.Sat

lemma inputsPrefix_correct (n k : ℕ) (h : k ≤ n) (x : Fin n → Bool) (i : Fin k) :
    AIG.denote x ⟨(inputsPrefix n k h).1, (inputsPrefix n k h).2 i⟩ = x (i.castLE h) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [inputsPrefix, Fin.snoc_last]
      change AIG.denote x ((inputsPrefix n k (by omega)).1.mkAtom ⟨k, by omega⟩) = _
      rw [AIG.denote_mkAtom]
      rfl
    · simp only [inputsPrefix, Fin.snoc_castSucc]
      rw [AIG.LawfulOperator.denote_cast_entry (f := @AIG.mkAtom (Fin n) _ _)
        (entry := ⟨(inputsPrefix n k (by omega)).1, (inputsPrefix n k (by omega)).2 j⟩)]
      exact ih (by omega) j

lemma inputs_correct (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    AIG.denote x ⟨(inputs n).1, (inputs n).2 i⟩ = x i := inputsPrefix_correct ..

lemma refVector_get {α : Type} [Hashable α] [DecidableEq α] {g : AIG α} {w : ℕ}
    (f : Fin w → AIG.Ref g) (i : ℕ) (hi : i < w) :
    (refVector f).get i hi = f ⟨i,hi⟩ := by
  simp [refVector, AIG.RefVec.get, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

end ExactQuantumFactoring.AIGCompiler


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

lemma binaryInputs_left (w : ℕ) (x : Fin (w+w) → Bool) (i : ℕ) (hi : i < w) :
    AIG.denote x ⟨(inputs (w+w)).1, (binaryInputs w).lhs.get i hi⟩ =
      (leftWord x).getLsbD i := by
  rw [binaryInputs, refVector_get, inputs_correct]
  exact (bitsValue_bit (fun j => x (j.castAdd w)) ⟨i,hi⟩).symm

lemma binaryInputs_right (w : ℕ) (x : Fin (w+w) → Bool) (i : ℕ) (hi : i < w) :
    AIG.denote x ⟨(inputs (w+w)).1, (binaryInputs w).rhs.get i hi⟩ =
      (rightWord x).getLsbD i := by
  rw [binaryInputs, refVector_get, inputs_correct]
  exact (bitsValue_bit (fun j => x (Fin.natAdd w j)) ⟨i,hi⟩).symm

lemma add_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (add w).eval x i = (leftWord x + rightWord x).getLsbD i.val := by
  rw [add, compileVec_correct]
  exact denote_blastAdd _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma mul_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (mul w).eval x i = (leftWord x * rightWord x).getLsbD i.val := by
  rw [mul, compileVec_correct]
  exact denote_blastMul _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitArithmeticDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

lemma sub_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (sub w).eval x i = (leftWord x - rightWord x).getLsbD i.val := by
  rw [sub, compileVec_correct]
  exact denote_blastSub _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma div_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (div w).eval x i = (leftWord x / rightWord x).getLsbD i.val := by
  rw [div, compileVec_correct]
  exact denote_blastUdiv _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma mod_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (mod w).eval x i = (leftWord x % rightWord x).getLsbD i.val := by
  rw [mod, compileVec_correct]
  exact denote_blastUmod _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordNetworks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
namespace BitArithmetic
open BooleanNetwork

lemma leftWord_append {w : ℕ} (a b : Basis w) : leftWord (Fin.append a b) = bitsValue a := by
  simp [leftWord]
lemma rightWord_append {w : ℕ} (a b : Basis w) : rightWord (Fin.append a b) = bitsValue b := by
  simp only [rightWord, Fin.append_right]

lemma mul_word (w : ℕ) (a b : Basis w) :
    bitsValue ((mul w).eval (Fin.append a b)) = bitsValue a * bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((mul w).eval (Fin.append a b))).getLsbD i =
    (mul w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    mul_correct, leftWord_append, rightWord_append]

lemma mod_word (w : ℕ) (a b : Basis w) :
    bitsValue ((mod w).eval (Fin.append a b)) = bitsValue a % bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((mod w).eval (Fin.append a b))).getLsbD i =
    (mod w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    mod_correct, leftWord_append, rightWord_append]

lemma add_word (w : ℕ) (a b : Basis w) :
    bitsValue ((add w).eval (Fin.append a b)) = bitsValue a + bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((add w).eval (Fin.append a b))).getLsbD i =
    (add w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    add_correct, leftWord_append, rightWord_append]

lemma bitsValue_append_zero {w t : ℕ} (x : Basis w) :
    bitsValue (Fin.append x (fun _ : Fin t => false)) = (bitsValue x).setWidth (w+t) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue (Fin.append x (fun _ : Fin t => false))).getLsbD i =
    Fin.append x (fun _ => false) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hw : i < w
  · have he : (⟨i,hi⟩ : Fin (w+t)) = (⟨i,hw⟩ : Fin w).castAdd t := Fin.ext rfl
    rw [he, Fin.append_left]
    exact (bitsValue_bit x ⟨i,hw⟩).symm
  · have he : (⟨i,hi⟩ : Fin (w+t)) = Fin.natAdd w (⟨i-w,by omega⟩ : Fin t) := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    rw [he, Fin.append_right, BitVec.getLsbD_of_ge _ _ (by omega)]

lemma padRight_word (w t : ℕ) (x : Basis w) :
    bitsValue ((padRight w t).eval x) = (bitsValue x).setWidth (w+t) := by
  rw [eval_padRight, bitsValue_append_zero]

lemma bitsValue_take {w t : ℕ} (x : Basis (w+t)) :
    bitsValue (x ∘ (Fin.castAdd t)) = (bitsValue x).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue (x ∘ Fin.castAdd t)).getLsbD i = x ((⟨i,hi⟩ : Fin w).castAdd t) from
    bitsValue_bit _ ⟨i,hi⟩, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  exact (bitsValue_bit x ((⟨i,hi⟩ : Fin w).castAdd t)).symm

lemma setWidth_toNat_of_le {w t : ℕ} (h : w ≤ t) (x : BitVec w) :
    (x.setWidth t).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)

lemma wordConstant_eval {n w : ℕ} (v : BitVec w) (x : Basis n) :
    bitsValue ((wordConstant v).eval x) = v := by
  have he : (wordConstant (n := n) v).eval x = fun i => v.getLsbD i.val := by
    funext i
    simp [wordConstant]
  rw [he, bitsValue_bits]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ArithmeticPredicates
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide
open AIGCompiler BooleanNetwork

lemma ult_correct (w : ℕ) (a b : Basis w) :
    (ult w).eval (Fin.append a b) 0 =
      decide ((bitsValue a).toNat < (bitsValue b).toNat) := by
  rw [ult,compile_correct]
  have h := BVPred.mkUlt_denote_eq (inputs (w+w)).1
    (leftWord (Fin.append a b)) (rightWord (Fin.append a b))
    (binaryInputs w) (Fin.append a b) (binaryInputs_left w _) (binaryInputs_right w _)
  simpa only [leftWord_append,rightWord_append,BitVec.ult] using h

lemma wordLt_eval {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (wordLt a b).eval x 0 = decide ((bitsValue (a.eval x)).toNat < (bitsValue (b.eval x)).toNat) := by
  rw [wordLt,eval_comp,eval_pair,ult_correct]

lemma wordLe_eval {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (wordLe a b).eval x 0 = decide ((bitsValue (a.eval x)).toNat ≤ (bitsValue (b.eval x)).toNat) := by
  rw [wordLe,eval_bnot,wordLt_eval]
  by_cases h : (bitsValue (a.eval x)).toNat ≤ (bitsValue (b.eval x)).toNat
  · simp [h,Nat.not_lt.mpr h]
  · simp [h,Nat.lt_of_not_ge h]

lemma wordEq_eval (w : ℕ) (a b : Basis w) :
    (wordEq w).eval (Fin.append a b) 0 = decide (bitsValue a = bitsValue b) := by
  have he : (select (Fin.addCases (Fin.natAdd w) (Fin.castAdd w))).eval (Fin.append a b) =
      Fin.append b a := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [eval_select,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right]
  rw [wordEq,eval_bnot,eval_bor,eval_comp,he,ult_correct,ult_correct]
  have hh : bitsValue a = bitsValue b ↔ (bitsValue a).toNat=(bitsValue b).toNat := by
    constructor
    · exact congrArg BitVec.toNat
    · exact BitVec.eq_of_toNat_eq
  simp only [hh]
  cases h₁ : decide ((bitsValue a).toNat < (bitsValue b).toNat) <;>
    cases h₂ : decide ((bitsValue b).toNat < (bitsValue a).toNat) <;>
    simp_all <;> omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ModularMultiply
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma mulMod_word {n w : ℕ} (a b m : BooleanNetwork n w) (x : Basis n)
    (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((mulMod a b m).eval x)).toNat =
      (bitsValue (a.eval x)).toNat * (bitsValue (b.eval x)).toNat %
        (bitsValue (m.eval x)).toNat := by
  simp only [mulMod, eval_rewire, eval_comp, eval_pair]
  rw [bitsValue_take, mod_word, BitVec.toNat_setWidth, BitVec.toNat_umod,
    mul_word, BitVec.toNat_mul]
  simp only [padRight_word, setWidth_toNat_of_le (by omega : w ≤ w+w)]
  have hp : (bitsValue (a.eval x)).toNat * (bitsValue (b.eval x)).toNat < 2^(w+w) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (bitsValue (a.eval x)).isLt
      (bitsValue (b.eval x)).isLt
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt]
  exact (Nat.mod_lt _ hm).trans (bitsValue (m.eval x)).isLt

lemma wordMux_eval {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w)
    (x : Basis n) :
    (wordMux c a b).eval x = if c.eval x 0 then a.eval x else b.eval x := by
  funext i
  simp only [wordMux, eval_comp, eval_vector, eval_mux, eval_bit, eval_pair]
  have h₀ : (⟨0,by omega⟩ : Fin (1+w+w)) = (Fin.castAdd w ((0 : Fin 1).castAdd w)) := rfl
  have h₁ : (⟨1+i.val,by omega⟩ : Fin (1+w+w)) = (Fin.natAdd 1 i).castAdd w := rfl
  have h₂ : (⟨1+w+i.val,by omega⟩ : Fin (1+w+w)) = Fin.natAdd (1+w) i := rfl
  simp only [h₀,h₁,h₂,Fin.append_left,Fin.append_right]
  split <;> rfl

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ModularPower
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

lemma powerStep_pack {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b) :
    (powerStep w i).eval (powerPack a m e z) =
      powerPack a m e ((powerNew w i).eval (powerPack a m e z)) := by
  simp only [powerStep, eval_pair, eval_select, powerPack]
  congr 1
  funext j
  exact Fin.append_left _ _ j

lemma powerNew_value {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b)
    (hm : 0 < (bitsValue m).toNat) :
    (bitsValue ((powerNew w i).eval (powerPack a m e z))).toNat =
      (if e i then ((bitsValue z).toNat^2 % (bitsValue m).toNat)*
        (bitsValue a).toNat % (bitsValue m).toNat
      else (bitsValue z).toNat^2 % (bitsValue m).toNat) := by
  rw [powerNew, wordMux_eval, powerBit_eval]
  have hm' : 0 < (bitsValue ((powerModulus w b).eval (powerPack a m e z))).toNat := by
    simpa only [powerModulus_eval] using hm
  split <;> rw [mulMod_word _ _ _ _ hm']
  · rw [mulMod_word _ _ _ _ hm']
    simp only [powerAcc_eval, powerBase_eval, powerModulus_eval, pow_two]
  · simp only [powerAcc_eval, powerModulus_eval, pow_two]

lemma horner_pow_step (a m v : ℕ) (b : Bool) :
    (if b then ((a^v % m)^2 % m)*a % m else (a^v % m)^2 % m) =
      a^(2*v+b.toNat) % m := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero]
    rw [← Nat.pow_mod, ← pow_mul]
    congr 2
    omega
  · simp only [↓reduceIte, Bool.toNat_true]
    rw [← Nat.pow_mod, Nat.mod_mul_mod, ← pow_mul, pow_succ, Nat.mul_comm v 2]

lemma powerPrefix_value {w b : ℕ} (a m : Basis w) (e : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) (k : ℕ) (hk : k ≤ b) :
    ∃ z : Basis w,
      (powerPrefix w b k hk).eval
        (powerPack a m e (fun i => (BitVec.ofNat w 1).getLsbD i.val)) = powerPack a m e z ∧
      (bitsValue z).toNat = (bitsValue a).toNat ^ horner e k hk % (bitsValue m).toNat := by
  induction k with
  | zero =>
    refine ⟨(fun i => (BitVec.ofNat w 1).getLsbD i.val),?_,?_⟩
    · simp only [powerPrefix, eval_select, Function.comp_id]
    · rw [bitsValue_bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      · simp [horner, Nat.mod_eq_of_lt (by omega : 1 < (bitsValue m).toNat)]
      · have h := (bitsValue m).isLt
        omega
  | succ k ih =>
    obtain ⟨z,hz,hv⟩ := ih (by omega)
    refine ⟨(powerNew w ⟨k,by omega⟩).eval (powerPack a m e z),?_,?_⟩
    · rw [powerPrefix,eval_comp,hz,powerStep_pack]
    · rw [powerNew_value _ _ _ _ _ (by omega), hv, horner_pow_step]
      rfl

lemma modularPower_value {w b : ℕ} (a m : Basis w) (e : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (bitsValue ((modularPower w b).eval (Fin.append (Fin.append a m) e))).toNat =
      (bitsValue a).toNat ^ horner e b le_rfl % (bitsValue m).toNat := by
  obtain ⟨z,hz,hv⟩ := powerPrefix_value a m e hm b le_rfl
  have hc : (wordConstant (n := (w+w)+b) (BitVec.ofNat w 1)).eval
      (Fin.append (Fin.append a m) e) =
        (fun i => (BitVec.ofNat w 1).getLsbD i.val) := by
    funext i
    simp [wordConstant]
  simp only [modularPower,eval_comp,eval_rewire,eval_pair,eval_select,
    Function.comp_id,hc]
  change (bitsValue (((powerPrefix w b b le_rfl).eval
    (powerPack a m e (fun i => (BitVec.ofNat w 1).getLsbD i.val))) ∘
      Fin.natAdd ((w+w)+b))).toNat = _
  rw [hz]
  have he : powerPack a m e z ∘ Fin.natAdd ((w+w)+b) = z := by
    funext i
    exact Fin.append_right _ _ i
  rw [he,hv]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_HornerEncoding
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

namespace BitArithmetic

lemma horner_sum {b : ℕ} (e : Basis b) (k : ℕ) (hk : k ≤ b) :
    horner e k hk = ∑ i : Fin k, 2^(k-1-i.val)*(e (i.castLE hk)).toNat := by
  induction k with
  | zero => simp [horner]
  | succ k ih =>
    rw [horner,ih (by omega),Fin.sum_univ_castSucc,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have he : k+1-1-i.val = (k-1-i.val)+1 := by have := i.isLt; omega
      rw [show (i.castSucc : Fin (k+1)).val = i.val from rfl,he,pow_succ]
      have hi : ((i.castSucc).castLE hk) = i.castLE (by omega : k ≤ b) := Fin.ext rfl
      rw [hi]
      ring
    · simp only [Fin.val_last,Nat.add_sub_cancel,Nat.sub_self,pow_zero,one_mul]
      rfl

lemma horner_full {b : ℕ} (e : Basis b) :
    horner e b le_rfl = Triangular.inputNumber e := by
  rw [horner_sum]
  rfl

end BitArithmetic

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_StaticPredicates
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma equalOn_value {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (equalOn a b).eval x 0=true ↔ (bitsValue (a.eval x)).toNat=(bitsValue (b.eval x)).toNat := by
  rw [equalOn,eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  exact ⟨congrArg BitVec.toNat,BitVec.eq_of_toNat_eq⟩

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AKSNetworks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma bnot_value {n : ℕ} (c : BooleanNetwork n 1) (x : Basis n) :
    c.bnot.eval x 0=true ↔ ¬ c.eval x 0=true := by simp

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AuxiliaryTree
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Occurrence-preserving bounds for the canonical p−1 auxiliary tree in
Section5. Equal labels under different parents remain separate list entries. -/
namespace ExactQuantumFactoring.AuxiliaryTree
open scoped BigOperators

lemma prod_flatMap (f : ℕ→List ℕ) (xs : List ℕ) :
    (xs.flatMap f).prod=(xs.map (fun x => (f x).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AuxiliaryData
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalTree.rowData_label
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

lemma trueData_eq (m : ℕ) : trueData m =
    .node m m.factorization ((children m).map trueData) := by
  rw [trueData]
  congr 1
  simp only [List.attach_map_val]

@[simp] lemma trueData_label (m : ℕ) : (trueData m).label=m := by
  rw [trueData_eq]; rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QuantumCore
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Exact integer arithmetic for the prescribed-mass order trial.
These are dependencies of the actual main theorem, not assumptions about an
unknown order and not a replacement target. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators

lemma lt_sampleCount_iff {Q d t i : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    i < sampleCount Q d t ↔ t+i*d < Q := by
  have htQ : t < Q := lt_of_lt_of_le ht hdQ
  unfold sampleCount
  rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
  omega

lemma sum_progression {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    (∑ i ∈ Finset.range (sampleCount Q d t), f (t+i*d)) =
      ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t), f x := by
  apply Finset.sum_bij (fun i _ => t+i*d)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at *
    refine ⟨(lt_sampleCount_iff hd hdQ ht).mp hi, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  · intro i hi j hj heq
    exact Nat.mul_right_cancel hd (Nat.add_left_cancel heq)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have heq : t+(x/d)*d=x := by
      have h := Nat.mod_add_div x d
      rw [hx.2] at h
      simpa only [Nat.mul_comm] using h
    refine ⟨x/d, ?_, heq⟩
    rw [Finset.mem_range, lt_sampleCount_iff hd hdQ ht, heq]
    exact hx.1
  · intro i hi
    rfl

lemma binError_bound {Q d j : ℕ} (hd : 0 < d) : |binError Q d j| ≤ 1/2 := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have h₁ : bin Q d j*(2*d) ≤ 2*j*Q+d := Nat.div_mul_le_self _ _
  have h₂ : 2*j*Q+d < (bin Q d j+1)*(2*d) := by
    have hr := Nat.mod_lt (2*j*Q+d) (by omega : 0 < 2*d)
    have heq := Nat.mod_add_div (2*j*Q+d) (2*d)
    change (2*j*Q+d)%(2*d) + (2*d)*bin Q d j = 2*j*Q+d at heq
    nlinarith
  have h₁' : (bin Q d j:ℝ)*(2*d) ≤ 2*j*Q+d := by exact_mod_cast h₁
  have h₂' : (2:ℝ)*j*Q+d < ((bin Q d j:ℝ)+1)*(2*d) := by exact_mod_cast h₂
  have heq : binError Q d j*(d:ℝ) = (bin Q d j:ℝ)*d-(j:ℝ)*Q := by
    rw [binError, sub_mul, div_mul_cancel₀ _ hd'.ne']
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_left₀ hd').mp
    nlinarith
  · apply (mul_le_mul_iff_left₀ hd').mp
    nlinarith

end ExactQuantumFactoring.OrderTrial



/-! Dependencies for the actual prescribed-probability order trial.
The phase below is proved to be exactly the quarter-linear interpolant in
sections/03-order-transform.tex. No oracle/order information is input. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators
open MeasureTheory intervalIntegral

lemma triangle_local {x : ℝ} (h : |x| ≤ 1/2) : triangle x = 1 - 4 * |x| := by
  unfold triangle
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by simpa using h)]

lemma triangle_add_int (x : ℝ) (k : ℤ) : triangle (x + k) = triangle x := by
  simp only [triangle, UnitAddCircle.norm_eq, round_add_intCast, Int.cast_add]
  congr 2
  ring_nf

lemma triangle_half (x : ℝ) : triangle (x + 1/2) = -triangle x := by
  let y : ℝ := x - round x
  have hy : |y| ≤ 1/2 := abs_sub_round x
  have hx : x = y + round x := by dsimp [y] <;> ring
  rw [hx]
  rw [show y + (round x : ℝ) + 1/2 = (y+1/2) + round x by ring,
    triangle_add_int, triangle_add_int]
  rcases le_total y 0 with hneg | hpos
  · have hy' : |y + 1/2| ≤ 1/2 := by rw [abs_le] at hy ⊢; constructor <;> linarith
    rw [triangle_local hy, triangle_local hy', abs_of_nonpos hneg,
      abs_of_nonneg (by have := (abs_le.mp hy).1; linarith : 0 ≤ y+1/2)]
    ring
  · have hy' : |y - 1/2| ≤ 1/2 := by rw [abs_le] at hy ⊢; constructor <;> linarith
    rw [show y+1/2 = (y-1/2) + (1 : ℤ) by norm_num; ring,
      triangle_add_int, triangle_local hy, triangle_local hy', abs_of_nonneg hpos,
      abs_of_nonpos (by have := (abs_le.mp hy).2; linarith : y-1/2 ≤ 0)]
    ring

lemma phase_quarter (x : ℝ) : phase (x + 1/4) = -Complex.I * phase x := by
  have h := triangle_half (x - 1/4)
  rw [show x-1/4+1/2 = x+1/4 by ring] at h
  apply Complex.ext
  · simpa only [phase, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] using h
  · simp only [phase, neg_mul, Complex.neg_im, Complex.I_mul_im]
    congr 2
    ring

lemma phase_add_int (x : ℝ) (k : ℤ) : phase (x + k) = phase x := by
  apply Complex.ext
  · exact triangle_add_int _ _
  · change -triangle (x + k - 1/4) = -triangle (x-1/4)
    rw [show x + k - 1/4 = (x-1/4)+k by ring, triangle_add_int]

lemma phase_zero_quarter {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phase (t/4) = (1-t : ℂ) + (t : ℂ) * (-Complex.I) := by
  have ha : |t/4| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  have hb : |t/4-1/4| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  apply Complex.ext
  · change triangle (t/4) = _
    rw [triangle_local ha, abs_of_nonneg (by positivity : 0 ≤ t/4)]
    simp
    ring
  · change -triangle (t/4-1/4) = _
    rw [triangle_local hb, abs_of_nonpos (by linarith : t/4-1/4 ≤ 0)]
    simp
    ring

lemma phase_add_quarters (x : ℝ) (q : ℤ) :
    phase (x + (q : ℝ)/4) = (-Complex.I)^q * phase x := by
  have hi : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  induction q using Int.induction_on with
  | zero => simp
  | succ q ih =>
      simp only [Int.cast_natCast] at ih
      rw [Int.cast_add, Int.cast_natCast, Int.cast_one,
        show x + ((q : ℝ) + 1)/4 = (x + (q : ℝ)/4) + 1/4 by ring,
        phase_quarter, ih, zpow_add₀ hi]
      simp only [zpow_one]
      ring
  | pred q ih =>
      have h := phase_quarter (x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4)
      rw [show x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4 + 1/4 =
          x + ((-(q : ℤ) : ℤ) : ℝ)/4 by push_cast; ring, ih] at h
      calc
        phase (x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4) =
            (-Complex.I)⁻¹ * ((-Complex.I)^(-(q : ℤ)) * phase x) := by
          rw [h, ← mul_assoc, inv_mul_cancel₀ hi, one_mul]
        _ = (-Complex.I)^(-(q : ℤ)-1) * phase x := by
          rw [show -(q : ℤ)-1 = -(q : ℤ)+(-1) by ring,
            zpow_add₀ hi, zpow_neg_one]
          ring

lemma phase_interpolates (q : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phase (((q : ℝ)+t)/4) = (1-t : ℂ)*(-Complex.I)^q +
      (t : ℂ)*(-Complex.I)^(q+1) := by
  rw [show ((q : ℝ)+t)/4 = t/4 + (q : ℝ)/4 by ring,
    phase_add_quarters, phase_zero_quarter ht0 ht1,
    zpow_add₀ (neg_ne_zero.mpr Complex.I_ne_zero)]
  simp only [zpow_one]
  ring

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded Euclidean recovery of the manuscript's nearest-bin labels.
The denominator bound is logarithmic, never a search through B labels. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Two Euclidean steps halve the denominator; the zero remainder is treated
separately, since natural remainder by zero is not zero. -/
lemma euclid_two_halving {b r : ℕ} (hr : 0 < r) (hrb : r<b) : 2*(b%r)<b := by
  by_cases h : 2*r ≤ b
  · have hm := Nat.mod_lt b hr
    omega
  · have hb : b<2*r := by omega
    have hmod : b%r=b-r := by
      apply Nat.mod_eq_sub_mod hrb.le |>.trans
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionPairs
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial

lemma convergentPair_reduced (a b k : ℕ) :
    0<(convergentPair a b k).2 ∧
      Nat.Coprime (convergentPair a b k).1 (convergentPair a b k).2 := by
  induction k generalizing a b with
  | zero => simp [convergentPair]
  | succ k ih =>
    have hh := ih b (a%b)
    simp only [convergentPair]
    split_ifs with h
    · simp
    · constructor
      · exact Nat.pos_of_ne_zero h
      · simpa [Nat.coprime_add_mul_left_left] using hh.2.symm

/-- Linear bit growth, rather than syntactic nested rational inverses. -/
lemma convergentPair_bound {s a b : ℕ} (ha : a<2^s) (hb : b<2^s) (k : ℕ) :
    (convergentPair a b k).1<2^(s*(k+1)+1) ∧
      (convergentPair a b k).2<2^(s*(k+1)+1) := by
  induction k generalizing a b with
  | zero =>
    have hp : 2^s ≤ 2^(s*1+1) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hone : 1<2^(s*1+1) := Nat.one_lt_two_pow (by omega)
    exact ⟨(Nat.div_le_self a b).trans_lt (ha.trans_le hp),hone⟩
  | succ k ih =>
    have hm : a%b<2^s := (Nat.mod_le a b).trans_lt ha
    obtain ⟨hn,hd⟩ := ih hb hm
    have hdiv : a/b<2^s := (Nat.div_le_self a b).trans_lt ha
    have hpow : 2^(s*(k+1)+1) ≤ 2^(s*(k+1+1)+1) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)
    have ha' : a/b<2^(s*(k+1+1)+1) := hdiv.trans_le
      (Nat.pow_le_pow_right (by omega) (by nlinarith))
    have hone : 1<2^(s*(k+1+1)+1) := Nat.one_lt_two_pow (by omega)
    simp only [convergentPair]
    split_ifs
    · exact ⟨ha',hone⟩
    · refine ⟨?_,hn.trans_le hpow⟩
      have hs : a/b+1 ≤ 2^s := hdiv
      have h₁ : (a/b)*(convergentPair b (a%b) k).1+(convergentPair b (a%b) k).2 <
          (a/b+1)*2^(s*(k+1)+1) := by
        have hx := Nat.mul_le_mul_left (a/b) hn.le
        nlinarith
      have h₂ := Nat.mul_le_mul_right (2^(s*(k+1)+1)) hs
      apply h₁.trans_le
      apply h₂.trans_eq
      rw [← pow_add]
      congr 1
      ring

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RootCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma rootModulus_eval (w : ℕ) (m g : Basis w) :
    (rootModulus w).eval (Fin.append m g)=m := by
  funext i
  exact Fin.append_left m g i
lemma rootGuess_eval (w : ℕ) (m g : Basis w) :
    (rootGuess w).eval (Fin.append m g)=g := by
  funext i
  exact Fin.append_right m g i

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_GcdCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Clocked Euclidean arithmetic, including zero operands.  The clock is
linear in bit width, and every step is an actual Boolean modular divider. -/
namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma euclidRun_zero (k a : ℕ) : euclidRun k a 0=(a,0) := by
  cases k <;> simp [euclidRun]

lemma euclidRun_terminal (s a b h : ℕ) (hb : b < 2^s) :
    euclidRun (2*s+h) a b=(Nat.gcd a b,0) := by
  induction s generalizing a b h with
  | zero =>
    have : b=0 := by simpa using hb
    subst b
    simp [euclidRun_zero]
  | succ s ih =>
    by_cases hb0 : b=0
    · subst b; simp [euclidRun_zero]
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    have he : 2*(s+1)+h=(2*s+h+1)+1 := by omega
    by_cases hr0 : a%b=0
    · rw [he,euclidRun,ite_eq_right hb0,hr0,euclidRun_zero]
      rw [Nat.gcd_comm a b,Nat.gcd_rec b a,hr0,Nat.gcd_zero_left]
    · have hr := Nat.pos_of_ne_zero hr0
      have hh := OrderTrial.euclid_two_halving hr (Nat.mod_lt a hbpos)
      have hb' : b%(a%b) < 2^s := by rw [pow_succ] at hb; omega
      rw [he,euclidRun,ite_eq_right hb0,euclidRun,ite_eq_right hr0,ih _ _ h hb']
      congr 1
      calc
        Nat.gcd (a%b) (b%(a%b)) = Nat.gcd b (a%b) := by
          rw [Nat.gcd_comm (a%b) (b%(a%b)),← Nat.gcd_rec (a%b) b,Nat.gcd_comm]
        _ = Nat.gcd a b := by rw [Nat.gcd_comm b (a%b),← Nat.gcd_rec b a,Nat.gcd_comm]

lemma euclidStep_semantics (w : ℕ) (a b : Basis w) :
    ∃ a' b' : Basis w,
      (euclidStep w).eval (Fin.append a b)=Fin.append a' b' ∧
      (bitsValue a').toNat=(if (bitsValue b).toNat=0 then (bitsValue a).toNat else (bitsValue b).toNat) ∧
      (bitsValue b').toNat=(if (bitsValue b).toNat=0 then 0 else (bitsValue a).toNat%(bitsValue b).toNat) := by
  let z := (wordConstant (n:=w+w) (BitVec.ofNat w 0)).eval (Fin.append a b)
  have hz : (bitsValue z).toNat=0 := by simp [z,wordConstant_eval]
  have hc : (equalOn (rootGuess w) (wordConstant (BitVec.ofNat w 0))).eval (Fin.append a b) 0=true ↔
      (bitsValue b).toNat=0 := by
    rw [equalOn_value,rootGuess_eval,wordConstant_eval]
    simp
  by_cases hb : (bitsValue b).toNat=0
  · refine ⟨a,z,?_,by simp [hb],by simpa [hb] using hz⟩
    rw [euclidStep,eval_pair,wordMux_eval,wordMux_eval,ite_eq_left (hc.mpr hb),ite_eq_left (hc.mpr hb),rootModulus_eval]
  · refine ⟨b,(mod w).eval (Fin.append a b),?_,by simp [hb],?_⟩
    · rw [euclidStep,eval_pair,wordMux_eval,wordMux_eval,ite_eq_right (fun condition => hb (hc.mp condition)),ite_eq_right (fun condition => hb (hc.mp condition)),rootGuess_eval]
    · rw [mod_word,BitVec.toNat_umod,ite_eq_right hb]

lemma euclidPrefix_semantics (w k : ℕ) (a b : Basis w) :
    ∃ a' b' : Basis w,
      (euclidPrefix w k).eval (Fin.append a b)=Fin.append a' b' ∧
      ((bitsValue a').toNat,(bitsValue b').toNat)=euclidRun k (bitsValue a).toNat (bitsValue b).toNat := by
  induction k generalizing a b with
  | zero => exact ⟨a,b,rfl,rfl⟩
  | succ k ih =>
    obtain ⟨a₁,b₁,he,ha,hb⟩ := euclidStep_semantics w a b
    obtain ⟨a',b',he',hv⟩ := ih a₁ b₁
    refine ⟨a',b',by rw [euclidPrefix,eval_comp,he,he'],?_⟩
    rw [hv,ha,hb,euclidRun]
    split_ifs with hb0
    · exact euclidRun_zero k _
    · rfl

lemma gcdNet_value (w : ℕ) (a b : Basis w) :
    (bitsValue ((gcdNet w).eval (Fin.append a b))).toNat=
      Nat.gcd (bitsValue a).toNat (bitsValue b).toNat := by
  obtain ⟨a',b',he,hv⟩ := euclidPrefix_semantics w (2*w) a b
  have ht := euclidRun_terminal w (bitsValue a).toNat (bitsValue b).toNat 0 (bitsValue b).isLt
  rw [Nat.add_zero] at ht
  rw [ht] at hv
  rw [gcdNet,eval_comp,he,rootModulus_eval]
  exact congrArg Prod.fst hv

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SplitCandidate
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace BitArithmetic

lemma div_word (w : ℕ) (a b : Basis w) :
    bitsValue ((div w).eval (Fin.append a b))=bitsValue a/bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((div w).eval (Fin.append a b))).getLsbD i =
    (div w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    div_correct,leftWord_append,rightWord_append]

lemma sub_word (w : ℕ) (a b : Basis w) :
    bitsValue ((sub w).eval (Fin.append a b))=bitsValue a-bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((sub w).eval (Fin.append a b))).getLsbD i =
    (sub w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    sub_correct,leftWord_append,rightWord_append]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open OrderTrial

lemma cfHead_eval (w : ℕ) (h p q : Basis w) :
    (cfHead w).eval (Fin.append h (Fin.append p q))=h := by
  funext i
  exact Fin.append_left h (Fin.append p q) i
lemma cfTail_eval (w : ℕ) (h : Basis w) (pq : Basis (w+w)) :
    (cfTail w).eval (Fin.append h pq)=pq := by
  funext i
  exact Fin.append_right h pq i
lemma cfP_eval (w : ℕ) (h p q : Basis w) :
    (cfP w).eval (Fin.append h (Fin.append p q))=p := by
  rw [cfP,eval_comp,cfTail_eval,rootModulus_eval]
lemma cfQ_eval (w : ℕ) (h p q : Basis w) :
    (cfQ w).eval (Fin.append h (Fin.append p q))=q := by
  rw [cfQ,eval_comp,cfTail_eval,rootGuess_eval]

lemma cfProduct_value (w : ℕ) (h p q : Basis w) :
    (bitsValue ((cfProduct w).eval (Fin.append h (Fin.append p q)))).toNat=
      ((bitsValue h).toNat*(bitsValue p).toNat+(bitsValue q).toNat)%2^w := by
  simp only [cfProduct,eval_comp,eval_pair,add_word,mul_word,cfHead_eval,cfP_eval,cfQ_eval,
    BitVec.toNat_add,BitVec.toNat_mul,Nat.mod_add_mod]

lemma cfCombine_value {w : ℕ} (hw : 0<w) (h p q : Basis w)
    (hn : (bitsValue h).toNat*(bitsValue p).toNat+(bitsValue q).toNat<2^w) :
    ∃ u v : Basis w,
      (cfCombine w).eval (Fin.append h (Fin.append p q))=Fin.append u v ∧
      (bitsValue u).toNat=(if (bitsValue p).toNat=0 then (bitsValue h).toNat
        else (bitsValue h).toNat*(bitsValue p).toNat+(bitsValue q).toNat) ∧
      (bitsValue v).toNat=(if (bitsValue p).toNat=0 then 1 else (bitsValue p).toNat) := by
  have hc : (equalOn (cfP w) (wordConstant (BitVec.ofNat w 0))).eval
      (Fin.append h (Fin.append p q)) 0=true ↔ (bitsValue p).toNat=0 := by
    rw [equalOn_value,cfP_eval,wordConstant_eval]
    simp
  by_cases hp : (bitsValue p).toNat=0
  · refine ⟨h,(wordConstant (n:=w+(w+w)) (BitVec.ofNat w 1)).eval
      (Fin.append h (Fin.append p q)),?_,by simp [hp],?_⟩
    · rw [cfCombine,eval_pair,wordMux_eval,wordMux_eval,ite_eq_left (hc.mpr hp),ite_eq_left (hc.mpr hp),cfHead_eval]
    · simp [wordConstant_eval,hp,Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')]
  · refine ⟨(cfProduct w).eval (Fin.append h (Fin.append p q)),p,?_,?_,by simp [hp]⟩
    · rw [cfCombine,eval_pair,wordMux_eval,wordMux_eval,
        ite_eq_right (fun hh => hp (hc.mp hh)),ite_eq_right (fun hh => hp (hc.mp hh)),cfP_eval]
    · rw [ite_eq_right hp,cfProduct_value,Nat.mod_eq_of_lt hn]

/-- One recursive circuit is used once per Euclidean level; no exponential
syntax duplication of earlier convergents. -/
lemma convergentNet_value {s w : ℕ} (k : ℕ) (hw : cfWidth s k ≤ w)
    (a b : Basis w) (ha : (bitsValue a).toNat<2^s) (hb : (bitsValue b).toNat<2^s) :
    ∃ p q : Basis w,
      (convergentNet w k).eval (Fin.append a b)=Fin.append p q ∧
      ((bitsValue p).toNat,(bitsValue q).toNat)=convergentPair (bitsValue a).toNat (bitsValue b).toNat k := by
  induction k generalizing a b with
  | zero =>
    refine ⟨(div w).eval (Fin.append a b),(wordConstant (n:=w+w) (BitVec.ofNat w 1)).eval
      (Fin.append a b),eval_pair _ _ _,?_⟩
    simp only [div_word,BitVec.toNat_udiv,wordConstant_eval,BitVec.toNat_ofNat,convergentPair]
    rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by dsimp [cfWidth] at hw; omega))]
  | succ k ih =>
    let r := (mod w).eval (Fin.append a b)
    let d := (div w).eval (Fin.append a b)
    have hr : (bitsValue r).toNat=(bitsValue a).toNat%(bitsValue b).toNat := by
      
      change (bitsValue ((mod w).eval (Fin.append a b))).toNat=_
      rw [mod_word,BitVec.toNat_umod]
    have hd : (bitsValue d).toNat=(bitsValue a).toNat/(bitsValue b).toNat := by
      
      change (bitsValue ((div w).eval (Fin.append a b))).toNat=_
      rw [div_word,BitVec.toNat_udiv]
    have hwk : cfWidth s k ≤ w := by dsimp [cfWidth] at * <;> nlinarith
    have hrb : (bitsValue r).toNat<2^s := by rw [hr]; exact (Nat.mod_le _ _).trans_lt ha
    obtain ⟨p,q,hpq,he⟩ := ih hwk b r hb hrb
    have hep := congrArg Prod.fst he
    have heq := congrArg Prod.snd he
    simp only [hr] at hep heq
    have hn : (bitsValue d).toNat*(bitsValue p).toNat+(bitsValue q).toNat<2^w := by
      rw [hd,hep,heq]
      by_cases hp : (convergentPair (bitsValue b).toNat ((bitsValue a).toNat%(bitsValue b).toNat) k).1=0
      · rw [hp,mul_zero,zero_add]
        have hh := (convergentPair_bound hb ((Nat.mod_le (bitsValue a).toNat (bitsValue b).toNat).trans_lt ha) k).2
        exact hh.trans_le (Nat.pow_le_pow_right (by omega) hwk)
      · have hh := (convergentPair_bound ha hb (k+1)).1
        simp only [convergentPair,ite_eq_right hp] at hh
        exact hh.trans_le (Nat.pow_le_pow_right (by omega) hw)
    obtain ⟨u,v,huv,hun,hvn⟩ := cfCombine_value (by dsimp [cfWidth] at hw; omega) d p q hn
    refine ⟨u,v,?_,?_⟩
    · simp only [convergentNet,eval_comp,eval_pair,rootGuess_eval,cfTail_eval]
      change (cfCombine w).eval (Fin.append ((cfHead w).eval (Fin.append d (Fin.append b r)))
        ((convergentNet w k).eval (Fin.append b r)))=Fin.append u v
      rw [cfHead_eval,hpq,huv]
    · simp only [hun,hvn,hd,hep,heq,convergentPair]
      split_ifs <;> rfl

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NaturalExpressions
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_iteLe _root_.OAI.ExactQuantumFactoring.IntExpr.eval_natAbs _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ofNat _root_.OAI.ExactQuantumFactoring.IntExpr.eval_scale _root_.OAI.ExactQuantumFactoring.IntExpr.eval_toNat _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ofNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! A finite straight-line expression language for the exact rational formulas
in the manuscript. All values are natural numbers, not unit-cost hidden gates.
The following compiler will realize these operations with actual bit networks. -/
namespace ExactQuantumFactoring

namespace NatExpr
variable {v : Type*}

lemma size_pos (e : NatExpr v) : 0 < e.size := by cases e <;> simp [size]

lemma value_bound (B : ℕ) (hB : 2 ≤ B) (x : v → ℕ) (hx : ∀ i, x i < B)
    (e : NatExpr v) (hc : e.constOK B) : e.eval x < B^e.size := by
  induction e with
  | var i => simpa [eval,size] using hx i
  | const c => simpa [eval,size,constOK] using hc
  | add a b ia ib =>
    have ha := ia hc.1
    have hb := ib hc.2
    have h₁ : a.eval x+b.eval x+1 ≤ (a.eval x+1)*(b.eval x+1) := by nlinarith
    have h₂ := Nat.mul_le_mul (Nat.succ_le_of_lt ha) (Nat.succ_le_of_lt hb)
    have h₃ : B^(a.size+b.size) ≤ B^(a.size+b.size+1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [eval,size]
    rw [← pow_add] at h₂
    simp only [Nat.succ_eq_add_one] at h₂
    omega
  | mul a b ia ib =>
    have ha := ia hc.1
    have hb := ib hc.2
    have h₁ : a.eval x*b.eval x+1 ≤ (a.eval x+1)*(b.eval x+1) := by nlinarith
    have h₂ := Nat.mul_le_mul (Nat.succ_le_of_lt ha) (Nat.succ_le_of_lt hb)
    have h₃ : B^(a.size+b.size) ≤ B^(a.size+b.size+1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [eval,size]
    rw [← pow_add] at h₂
    simp only [Nat.succ_eq_add_one] at h₂
    omega
  | sub a b ia _ =>
    exact (Nat.sub_le _ _).trans_lt ((ia hc.1).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [size]; omega)))
  | div a b ia _ =>
    exact (Nat.div_le_self _ _).trans_lt ((ia hc.1).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [size]; omega)))
  | mod a b ia _ =>
    exact (Nat.mod_le _ _).trans_lt ((ia hc.1).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [size]; omega)))
  | iteLe a b c d _ _ ic id =>
    simp only [eval]
    split_ifs
    · exact (ic hc.2.2.1).trans_le (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (id hc.2.2.2).trans_le (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))

lemma Fits.mono {B C : ℕ} (hBC : B ≤ C) {x : v → ℕ} {e : NatExpr v}
    (h : Fits B x e) : Fits C x e := by
  induction e with
  | var _ | const _ => exact ⟨h.1.trans_le hBC,trivial⟩
  | add a b ia ib | mul a b ia ib | sub a b ia ib | div a b ia ib | mod a b ia ib =>
    exact ⟨h.1.trans_le hBC,ia h.2.1,ib h.2.2⟩
  | iteLe a b c d ia ib ic id =>
    exact ⟨h.1.trans_le hBC,ia h.2.1,ib h.2.2.1,ic h.2.2.2.1,id h.2.2.2.2⟩

lemma fits_bound (B : ℕ) (hB : 2 ≤ B) (x : v → ℕ) (hx : ∀ i, x i < B)
    (e : NatExpr v) (hc : e.constOK B) : Fits (B^e.size) x e := by
  induction e with
  | var i | const i => exact ⟨value_bound B hB x hx _ hc,trivial⟩
  | add a b ia ib | mul a b ia ib | sub a b ia ib | div a b ia ib | mod a b ia ib =>
    refine ⟨value_bound B hB x hx _ hc,?_,?_⟩
    · exact (ia hc.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (ib hc.2).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
  | iteLe a b c d ia ib ic id =>
    refine ⟨value_bound B hB x hx _ hc,?_,?_,?_,?_⟩
    · exact (ia hc.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (ib hc.2.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (ic hc.2.2.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (id hc.2.2.2).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))

lemma fits_bits {b : ℕ} (hb : 1 ≤ b) (x : v → ℕ) (hx : ∀ i, x i < 2^b)
    (e : NatExpr v) (hc : e.constOK (2^b)) : Fits (2^(b*e.size)) x e := by
  rw [pow_mul]
  exact fits_bound (2^b) (Nat.one_lt_two_pow (by omega)) x hx e hc

end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NaturalExpressionCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace BitArithmetic

lemma natSubOn_value {k w : ℕ} (a b : BooleanNetwork k w) (x : Basis k) :
    (bitsValue ((natSubOn a b).eval x)).toNat=
      (bitsValue (a.eval x)).toNat-(bitsValue (b.eval x)).toNat := by
  rw [natSubOn,wordMux_eval,wordLe_eval]
  by_cases h : (bitsValue (b.eval x)).toNat ≤ (bitsValue (a.eval x)).toNat
  · rw [ite_eq_left (by simpa using h),eval_comp,eval_pair,sub_word,BitVec.toNat_sub]
    have hb := (bitsValue (b.eval x)).isLt
    have ha := (bitsValue (a.eval x)).isLt
    have he : 2^w-(bitsValue (b.eval x)).toNat+(bitsValue (a.eval x)).toNat=
        2^w+((bitsValue (a.eval x)).toNat-(bitsValue (b.eval x)).toNat) := by omega
    rw [he,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using h),wordConstant_eval]
    simp only [BitVec.toNat_ofNat,Nat.zero_mod]
    omega

end BitArithmetic
namespace NatExpr
variable {v : Type*} {k w : ℕ}

lemma compile_value (vars : v → BooleanNetwork k w) (x : Basis k)
    (e : NatExpr v) (he : Fits (2^w) (fun i => (bitsValue ((vars i).eval x)).toNat) e) :
    (bitsValue ((e.compile vars).eval x)).toNat=
      e.eval (fun i => (bitsValue ((vars i).eval x)).toNat) := by
  induction e with
  | var i => rfl
  | const c =>
    rw [compile,wordConstant_eval,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt he.1
  | add a b ia ib =>
    rw [compile,eval_comp,eval_pair,add_word,BitVec.toNat_add,ia he.2.1,ib he.2.2]
    exact Nat.mod_eq_of_lt he.1
  | mul a b ia ib =>
    rw [compile,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,ia he.2.1,ib he.2.2]
    exact Nat.mod_eq_of_lt he.1
  | sub a b ia ib =>
    rw [compile,natSubOn_value,ia he.2.1,ib he.2.2]
    rfl
  | div a b ia ib =>
    rw [compile,eval_comp,eval_pair,div_word,BitVec.toNat_udiv,ia he.2.1,ib he.2.2]
    rfl
  | mod a b ia ib =>
    rw [compile,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,ia he.2.1,ib he.2.2]
    rfl
  | iteLe a b c d ia ib ic id =>
    rw [compile,wordMux_eval,wordLe_eval,ia he.2.1,ib he.2.2.1]
    simp only [eval,decide_eq_true_eq]
    split_ifs
    · exact ic he.2.2.2.1
    · exact id he.2.2.2.2

end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordResize
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma resizeWord_value (u w : ℕ) (x : Basis u) :
    bitsValue ((resizeWord u w).eval x)=(bitsValue x).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((resizeWord u w).eval x)).getLsbD i =
    (resizeWord u w).eval x ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    BitVec.getLsbD_setWidth]
  simp only [hi,decide_true,Bool.true_and,resizeWord,eval_vector]
  by_cases hu : i<u
  · rw [dite_eq_left hu,eval_bit]
    exact (bitsValue_bit x ⟨i,hu⟩).symm
  · rw [dite_eq_right hu]
    simpa only [eval_constant] using (BitVec.getLsbD_of_ge (bitsValue x) i (by omega)).symm

lemma resizeWord_toNat {u w : ℕ} (h : u≤w) (x : Basis u) :
    (bitsValue ((resizeWord u w).eval x)).toNat=(bitsValue x).toNat := by
  rw [resizeWord_value,setWidth_toNat_of_le h]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionTemplateCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_iteLe _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ofNat _root_.OAI.ExactQuantumFactoring.IntExpr.eval_scale _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ofNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

lemma constOK_of_maxConst_lt (e : NatExpr v) {B : ℕ} (h : e.maxConst < B) : e.constOK B := by
  induction e with
  | var i => trivial
  | const c => exact h
  | add a b ia ib | mul a b ia ib | sub a b ia ib | div a b ia ib | mod a b ia ib =>
    exact ⟨ia (lt_of_le_of_lt (le_max_left _ _) h),ib (lt_of_le_of_lt (le_max_right _ _) h)⟩
  | iteLe a b c d ia ib ic id =>
    have h₁ : _root_.Max.max a.maxConst b.maxConst < B := lt_of_le_of_lt (le_max_left _ _) h
    have h₂ : _root_.Max.max c.maxConst d.maxConst < B := lt_of_le_of_lt (le_max_right _ _) h
    exact ⟨ia (lt_of_le_of_lt (le_max_left _ _) h₁),ib (lt_of_le_of_lt (le_max_right _ _) h₁),
      ic (lt_of_le_of_lt (le_max_left _ _) h₂),id (lt_of_le_of_lt (le_max_right _ _) h₂)⟩

lemma le_templateWidth (e : NatExpr v) (b : ℕ) : b ≤ e.templateWidth b := by
  have h := Nat.le_mul_of_pos_right (b+e.maxConst.size+1) e.size_pos
  dsimp [templateWidth]
  omega

lemma template_value {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) (x : Basis k) :
    (bitsValue ((e.template vars).eval x)).toNat =
      e.eval (fun i => (bitsValue ((vars i).eval x)).toNat) := by
  have hv : (fun i => (bitsValue (((vars i).comp (resizeWord b (e.templateWidth b))).eval x)).toNat)=
      (fun i => (bitsValue ((vars i).eval x)).toNat) := by
    funext i
    rw [eval_comp,resizeWord_toNat (le_templateWidth e b)]
  unfold template
  rw [compile_value,hv]
  rw [hv]
  apply fits_bits (by omega : 1 ≤ b+e.maxConst.size+1)
  · intro i
    exact (bitsValue ((vars i).eval x)).isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  · apply e.constOK_of_maxConst_lt
    exact (Nat.lt_size_self e.maxConst).trans_le
      (Nat.pow_le_pow_right (by omega) (by omega))

end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionPredicates
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

lemma eval_testEq (x : v → ℕ) (a b yes no : NatExpr v) :
    (testEq a b yes no).eval x=if a.eval x=b.eval x then yes.eval x else no.eval x := by
  simp only [testEq,eval]
  split_ifs <;> omega

lemma isOne_eval {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) (x : Basis k) :
    (e.isOne vars).eval x 0=true ↔ e.eval (fun i => (bitsValue ((vars i).eval x)).toNat)=1 := by
  rw [isOne,equalOn_value,template_value,wordConstant_eval,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  apply Nat.one_lt_two_pow
  have hh := Nat.mul_pos (show 0<b+e.maxConst.size+1 by omega) e.size_pos
  exact hh.ne'
end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BinLabelCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.IntExpr.eval_iteLe _root_.OAI.ExactQuantumFactoring.IntExpr.eval_natAbs _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ofNat _root_.OAI.ExactQuantumFactoring.IntExpr.eval_scale _root_.OAI.ExactQuantumFactoring.IntExpr.eval_toNat _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ofNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma binCheckExpr_eval (x : Fin 5 → ℕ) :
    binCheckExpr.eval x=1 ↔ 0<x 3 ∧ x 3<x 1 ∧ x 4<x 3 ∧ bin (x 0) (x 3) (x 4)=x 2 := by
  unfold bin
  by_cases hd : 1≤x 3 <;> by_cases hB : x 3+1≤x 1 <;>
    by_cases hj : x 4+1≤x 3 <;>
    by_cases he : (2*x 4*x 0+x 3)/(2*x 3)=x 2 <;>
    simp [binCheckExpr,NatExpr.eval_testEq,NatExpr.eval,hd,hB,hj,he] <;> omega

lemma checkedConvergent_value {n s w : ℕ} (i : ℕ) (hw : cfWidth s i ≤ w)
    (Q B k : BooleanNetwork n w) (x : Basis n)
    (hQ : (bitsValue (Q.eval x)).toNat<2^s) (hk : (bitsValue (k.eval x)).toNat<2^s) :
    ∃ d j : Basis w,
      (checkedConvergent i Q B k).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=checkedPair
        (bitsValue (Q.eval x)).toNat (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat i := by
  obtain ⟨p,q,hpq,he⟩ := convergentNet_value i hw (k.eval x) (Q.eval x) hk hQ
  let cv := (k.pair Q).comp (convergentNet w i)
  have hv : cv.eval x=Fin.append p q := by rw [eval_comp,eval_pair,hpq]
  let den := cv.comp (rootGuess w)
  let num := cv.comp (rootModulus w)
  have hd : den.eval x=q := by rw [eval_comp,hv,rootGuess_eval]
  have hj : num.eval x=p := by rw [eval_comp,hv,rootModulus_eval]
  let pass := binCheckExpr.isOne ![Q,B,k,den,num]
  have hc : pass.eval x 0=true ↔ IsBinLabel (bitsValue (Q.eval x)).toNat
      (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat
      ((bitsValue q).toNat,(bitsValue p).toNat) := by
    rw [NatExpr.isOne_eval,binCheckExpr_eval]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Matrix.cons_val_succ,hd,hj]
    have hr := convergentPair_reduced (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i
    have hpv : (bitsValue p).toNat = (convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).1 := congrArg Prod.fst he
    have hqv : (bitsValue q).toNat = (convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).2 := congrArg Prod.snd he
    change 0<(bitsValue q).toNat ∧ (bitsValue q).toNat<(bitsValue (B.eval x)).toNat ∧
      (bitsValue p).toNat<(bitsValue q).toNat ∧
      bin (bitsValue (Q.eval x)).toNat (bitsValue q).toNat (bitsValue p).toNat=(bitsValue (k.eval x)).toNat ↔ _
    have hcop : Nat.Coprime (bitsValue p).toNat (bitsValue q).toNat := by
      rw [hpv,hqv]
      exact hr.2
    exact ⟨fun ⟨a,b,c,e⟩ => ⟨a,b,c,hcop,e⟩,fun ⟨a,b,c,_,e⟩ => ⟨a,b,c,e⟩⟩
  have he' : ((bitsValue q).toNat,(bitsValue p).toNat)=
      ((convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).2,
        (convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).1) :=
    congrArg Prod.swap he
  let zero := (wordConstant (n:=n) (BitVec.ofNat w 0)).eval x
  have hz : (bitsValue zero).toNat=0 := by simp [zero,wordConstant_eval]
  by_cases hh : IsBinLabel (bitsValue (Q.eval x)).toNat (bitsValue (B.eval x)).toNat
      (bitsValue (k.eval x)).toNat ((bitsValue q).toNat,(bitsValue p).toNat)
  · refine ⟨q,p,?_,?_⟩
    · rw [checkedConvergent,eval_pair]
      change Fin.append ((wordMux pass den _).eval x) ((wordMux pass num _).eval x)=_
      rw [wordMux_eval,wordMux_eval,ite_eq_left (hc.mpr hh),ite_eq_left (hc.mpr hh),hd,hj]
    · rw [checkedPair,← he',ite_eq_left hh]
  · refine ⟨zero,zero,?_,?_⟩
    · rw [checkedConvergent,eval_pair]
      change Fin.append ((wordMux pass den _).eval x) ((wordMux pass num _).eval x)=_
      rw [wordMux_eval,wordMux_eval,ite_eq_right (fun h => hh (hc.mp h)),ite_eq_right (fun h => hh (hc.mp h))]
    · rw [checkedPair,← he',ite_eq_right hh,hz]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrial
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.OrderTrial.binErrorRat_cast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open MeasureTheory intervalIntegral

lemma phase_bin_progression {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) (j t i : ℕ) :
    phase ((bin Q d j : ℝ)*(t+i*d)/Q) =
      phase (((j*t)%d : ℕ)/ (d:ℝ) + binError Q d j*((t+i*d : ℕ):ℝ)/Q) := by
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hr : (((j*t)%d : ℕ):ℝ) + (d:ℝ)*(((j*t)/d : ℕ):ℝ) = (j:ℝ)*t := by
    exact_mod_cast Nat.mod_add_div (j*t) d
  have hjt : (j:ℝ)*t/d = (((j*t)%d : ℕ):ℝ)/d + (((j*t)/d : ℕ):ℝ) := by
    rw [← hr, add_div, mul_div_cancel_left₀ _ hd']
  have heq : (bin Q d j : ℝ)*(t+i*d)/Q =
      (((j*t)%d : ℕ):ℝ)/d + binError Q d j*((t+i*d : ℕ):ℝ)/Q +
      (((j*t/d+j*i : ℕ):ℤ):ℝ) := by
    calc
      _ = (j:ℝ)*t/d+(j:ℝ)*i + binError Q d j*((t+i*d : ℕ):ℝ)/Q := by
        unfold binError
        push_cast
        field_simp
        ring
      _ = _ := by
        rw [hjt]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_mul]
        ring
  rw [heq, phase_add_int]

lemma residueAmplitude_samples {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    residueAmplitude Q d j t = (Q:ℂ)⁻¹ *
      ∑ i ∈ Finset.range (sampleCount Q d t),
        phase (((j*t)%d : ℕ)/(d:ℝ) +
          binError Q d j*((t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q))) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  unfold residueAmplitude
  rw [← sum_progression (fun x => phase ((bin Q d j:ℝ)*x/Q)) hd hdQ ht]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_add, Nat.cast_mul, phase_bin_progression hQ hd]
  congr 1
  push_cast
  ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open MeasureTheory intervalIntegral

lemma splineReDeriv_eq {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    splineReDeriv x = triangle x := by
  unfold splineReDeriv
  by_cases h₀ : x ≤ 0
  · rw [max_eq_left h₀, max_eq_left (by linarith : x-1/2 ≤ 0),
      max_eq_left (by linarith : x-1 ≤ 0), triangle_local (by rw [abs_le]; constructor <;> linarith),
      abs_of_nonpos h₀]
    ring
  · have h₀' := le_of_not_ge h₀
    rw [max_eq_right h₀']
    by_cases h₁ : x ≤ 1/2
    · rw [max_eq_left (by linarith : x-1/2 ≤ 0), max_eq_left (by linarith : x-1 ≤ 0),
        triangle_local (by rw [abs_le]; constructor <;> linarith), abs_of_nonneg h₀']
      ring
    · have ht : triangle x = triangle (x-1) := by
        convert triangle_add_int (x-1) 1 using 1
        all_goals try with_reducible_and_instances rfl
        norm_num
      rw [ht, triangle_local (by rw [abs_le]; constructor <;> linarith),
        max_eq_right (by linarith : 0 ≤ x-1/2)]
      by_cases h₂ : x ≤ 1
      · rw [max_eq_left (by linarith : x-1 ≤ 0), abs_of_nonpos (by linarith : x-1 ≤ 0)]
        ring
      · rw [max_eq_right (by linarith : 0 ≤ x-1), abs_of_nonneg (by linarith : 0 ≤ x-1)]
        ring

lemma splineImDeriv_eq {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    splineImDeriv x = -triangle (x-1/4) := by
  unfold splineImDeriv
  by_cases h₀ : x ≤ -(1/4)
  · have ht : triangle (x-1/4) = triangle (x+3/4) := by
      symm
      convert triangle_add_int (x-1/4) 1 using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
      congr 1
      ring
    rw [max_eq_left (by linarith : x+1/4 ≤ 0),
      max_eq_left (by linarith : x-1/4 ≤ 0), max_eq_left (by linarith : x-3/4 ≤ 0),
      max_eq_left (by linarith : x-5/4 ≤ 0), ht,
      triangle_local (by rw [abs_le]; constructor <;> linarith),
      abs_of_nonneg (by linarith : 0 ≤ x+3/4)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ x+1/4)]
    by_cases h₁ : x ≤ 1/4
    · rw [max_eq_left (by linarith : x-1/4 ≤ 0), max_eq_left (by linarith : x-3/4 ≤ 0),
        max_eq_left (by linarith : x-5/4 ≤ 0),
        triangle_local (by rw [abs_le]; constructor <;> linarith),
        abs_of_nonpos (by linarith : x-1/4 ≤ 0)]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ x-1/4)]
      by_cases h₂ : x ≤ 3/4
      · rw [max_eq_left (by linarith : x-3/4 ≤ 0), max_eq_left (by linarith : x-5/4 ≤ 0),
          triangle_local (by rw [abs_le]; constructor <;> linarith),
          abs_of_nonneg (by linarith : 0 ≤ x-1/4)]
        ring
      · have ht : triangle (x-1/4) = triangle (x-5/4) := by
          convert triangle_add_int (x-5/4) 1 using 1
          all_goals try with_reducible_and_instances rfl
          norm_num
          congr 1
          ring
        rw [max_eq_right (by linarith : 0 ≤ x-3/4), ht,
          triangle_local (by rw [abs_le]; constructor <;> linarith)]
        by_cases h₃ : x ≤ 5/4
        · rw [max_eq_left (by linarith : x-5/4 ≤ 0), abs_of_nonpos (by linarith : x-5/4 ≤ 0)]
          ring
        · rw [max_eq_right (by linarith : 0 ≤ x-5/4), abs_of_nonneg (by linarith : 0 ≤ x-5/4)]
          ring

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrialFurther2
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma powerSumValue_correct (q : ℕ) (hq : q ≤ 4) (M : ℕ) :
    powerSumValue q M = ∑ u ∈ Finset.range M, (u:ℚ)^q := by
  induction M with
  | zero => interval_cases q <;> norm_num [powerSumValue]
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih]
    push_cast
    interval_cases q <;> simp only [powerSumValue] <;> ring

lemma powerSumValue_sub {lo hi : ℕ} (h : lo ≤ hi) {q : ℕ} (hq : q ≤ 4) :
    powerSumValue q hi-powerSumValue q lo = ∑ u ∈ Finset.Ico lo hi, (u:ℚ)^q := by
  rw [Finset.sum_Ico_eq_sub _ h, powerSumValue_correct q hq, powerSumValue_correct q hq]

lemma fiveTermSum_correct (a : ℕ → ℚ) (lo hi : ℕ) :
    fiveTermSum a lo hi = ∑ u ∈ Finset.Ico lo hi, ∑ q ∈ Finset.range 5, a q*(u:ℚ)^q := by
  unfold fiveTermSum
  split_ifs with h
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [powerSumValue_sub h (by simp only [Finset.mem_range] at hq; omega), Finset.mul_sum]
  · simp [Finset.Ico_eq_empty (by omega : ¬ lo < hi)]

lemma interval_mem_iff (d u : ℕ) (a b c e : ℚ) :
    u ∈ Finset.Ico (intervalLo a c) (intervalHi d b e) ↔
      u < d ∧ a ≤ (u:ℚ) ∧ (u:ℚ) < b ∧ c ≤ (u:ℚ) ∧ (u:ℚ) < e := by
  simp only [Finset.mem_Ico, intervalLo, intervalHi, max_le_iff, lt_min_iff,
    Int.toNat_le, Int.lt_toNat, Int.ceil_le, Int.lt_ceil, Int.cast_natCast]
  tauto

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

lemma quarterIndex_eq (x : ℚ) (q : ℤ) :
    quarterIndex x=q ↔ (q:ℚ)/4 ≤ x ∧ x < ((q:ℚ)+1)/4 := by
  unfold quarterIndex
  rw [Int.floor_eq_iff]
  constructor <;> rintro ⟨hl,hu⟩ <;> constructor <;> linarith

lemma shiftedQuarter_eq {d : ℕ} (hd : 0 < d) (u : ℕ) (η : ℚ) (q : ℤ) :
    quarterIndex ((u:ℚ)/d+η)=q ↔
      (d:ℚ)*((q:ℚ)/4-η) ≤ u ∧ (u:ℚ) < d*(((q:ℚ)+1)/4-η) := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  rw [quarterIndex_eq, ← sub_le_iff_le_add, ← lt_sub_iff_add_lt,
    le_div_iff₀ hd', div_lt_iff₀ hd']
  simp only [mul_comm]

lemma pieceLabel_mem {d : ℕ} (hd : 0 < d) {η : ℚ} (hη : |η| ≤ 1/2)
    {u : ℕ} (hu : u < d) : pieceLabel d η u ∈ quarterPairs := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have hu₀ : (0:ℚ) ≤ (u:ℚ)/d := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hu₁ : (u:ℚ)/d < 1 := (div_lt_one hd').mpr (by exact_mod_cast hu)
  rcases abs_le.mp hη with ⟨hη₀,hη₁⟩
  simp only [pieceLabel, quarterPairs, Finset.mem_product, Finset.mem_Ico,
    quarterIndex, Int.le_floor, Int.floor_lt, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
  constructor <;> constructor <;> linarith

lemma piece_fiber {d : ℕ} (hd : 0 < d) (η : ℚ) (q : ℤ × ℤ) :
    (Finset.range d).filter (fun u => pieceLabel d η u=q) =
      Finset.Ico (pieceLo d η q) (pieceHi d η q) := by
  ext u
  rw [Finset.mem_filter]
  simp only [Finset.mem_range, pieceLo, pieceHi, interval_mem_iff]
  rw [Prod.ext_iff]
  simp only [pieceLabel]
  have h₀ := shiftedQuarter_eq hd u 0 q.1
  simp only [add_zero, sub_zero] at h₀
  rw [h₀, shiftedQuarter_eq hd u η q.2]
  simp only [mul_div_assoc]
  tauto

lemma packedPieceSum_correct {Q B d : ℕ} (hd : 0 < d) (j : ℕ) (q : ℤ × ℤ) :
    packedPieceSum Q B d j q =
      ∑ u ∈ (Finset.range d).filter (fun u => pieceLabel d (binErrorRat Q d j) u=q),
        majorant Q B d j u := by
  let η := binErrorRat Q d j
  have hf := piece_fiber hd η q
  have he : ∀ u ∈ (Finset.range d).filter (fun u => pieceLabel d η u=q),
      majorant Q B d j u = roundedValue (Q*B^8) (massPiece d η q.1 q.2) u+64/(Q:ℚ) := by
    intro u hu
    have h := (Finset.mem_filter.mp hu).2
    have h₀ := congrArg Prod.fst h
    have h₁ := congrArg Prod.snd h
    simp only [pieceLabel] at h₀ h₁
    simp only [majorant, selectedMass, h₀, h₁, η]
  change packedPieceSum Q B d j q = ∑ u ∈ (Finset.range d).filter (fun u => pieceLabel d η u=q), _
  rw [Finset.sum_congr rfl he, hf, Finset.sum_add_distrib]
  simp only [packedPieceSum, fiveTermSum_correct, roundedValue, η,
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

lemma packedMajorantSum_correct {Q B d : ℕ} (hd : 0 < d) (j : ℕ) :
    packedMajorantSum Q B d j = majorantSum Q B d j := by
  unfold packedMajorantSum majorantSum
  congr 1
  simp only [packedPieceSum_correct hd]
  apply Finset.sum_fiberwise_of_maps_to
  intro u hu
  apply pieceLabel_mem hd
  · have h := binError_bound (Q:=Q) (j:=j) hd
    rw [← binErrorRat_cast] at h
    have h' : ((|binErrorRat Q d j|:ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := by simpa using h
    exact Rat.cast_le.mp h'
  · exact Finset.mem_range.mp hu

end ExactQuantumFactoring.OrderTrial



end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_Exactness
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma minusI_cast : (minusI:ℂ) = -Complex.I := by
  simp [minusI, GaussianInt.toComplex_def]

lemma phase_grid_numerator {Q : ℕ} (hQ : 0 < Q) (y : ℕ) :
    phase ((y:ℝ)/Q) = (gridPhaseNumerator Q y:ℂ)/(Q:ℂ) := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hQc : (Q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hr : (4*y)%Q < Q := Nat.mod_lt _ hQ
  have hr' : (0:ℝ) ≤ ((4*y)%Q:ℕ) := Nat.cast_nonneg _
  have hle : (((4*y)%Q:ℕ):ℝ) ≤ Q := by exact_mod_cast hr.le
  have ht₀ : 0 ≤ (((4*y)%Q:ℕ):ℝ)/Q := div_nonneg hr' hQ'.le
  have ht₁ : (((4*y)%Q:ℕ):ℝ)/Q ≤ 1 := (div_le_one hQ').mpr hle
  have he : ((((4*y)/Q:ℕ):ℝ)+(((4*y)%Q:ℕ):ℝ)/Q)/4 = (y:ℝ)/Q := by
    have h := Nat.mod_add_div (4*y) Q
    have h' : (((4*y)%Q:ℕ):ℝ)+(Q:ℝ)*((4*y)/Q:ℕ) = 4*y := by exact_mod_cast h
    field_simp
    nlinarith
  have hg := phase_interpolates (((4*y)/Q:ℕ):ℤ) ht₀ ht₁
  rw [show (((4*y)/Q:ℕ):ℤ)+1 = (((4*y)/Q+1:ℕ):ℤ) by simp] at hg
  simp only [Int.cast_natCast, zpow_natCast] at hg
  rw [he] at hg
  rw [hg]
  simp only [gridPhaseNumerator, map_add, map_sub, map_mul, map_pow, map_natCast,
    minusI_cast, Nat.cast_sub hr.le, Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp

lemma residueAmplitude_gaussian {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    residueAmplitude Q d j t = (residueGaussianNumerator Q d j t:ℂ)/(Q:ℂ)^2 := by
  have hph : ∀ x : ℕ, phase ((bin Q d j:ℝ)*x/Q) =
      (gridPhaseNumerator Q (bin Q d j*x):ℂ)/(Q:ℂ) := by
    intro x
    simpa only [Nat.cast_mul] using phase_grid_numerator hQ (bin Q d j*x)
  unfold residueAmplitude
  simp_rw [hph]
  rw [← Finset.sum_div]
  simp only [residueGaussianNumerator, map_sum]
  ring

lemma residueProbabilityRat_cast {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    (residueProbabilityRat Q d j t:ℝ) = residueProbability Q d j t := by
  rw [residueProbability, residueAmplitude_gaussian hQ, norm_div, norm_pow,
    Complex.norm_natCast, div_pow, ← Complex.normSq_eq_norm_sq,
    ← GaussianInt.intCast_real_norm]
  simp only [residueProbabilityRat, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_intCast]
  ring

end ExactQuantumFactoring.OrderTrial



end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitResidue
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

lemma finEquiv_val {n : ℕ} [NeZero n] (z : Fin n) :
    (ZMod.finEquiv n z).val = z.val := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n => rfl

lemma basisResidue_val (b : ℕ) (x : Basis b) :
    (basisResidue b x).val = (bitsValue x).toNat := by
  exact finEquiv_val _

lemma basisResidue_eq (b : ℕ) (x : Basis b) :
    basisResidue b x = ((bitsValue x).toNat : ZMod (2^b)) := by
  rw [← basisResidue_val, ZMod.natCast_zmod_val]

lemma basisResidue_zero (b : ℕ) : basisResidue b (fun _ => false) = 0 := by
  rw [basisResidue_eq]
  have h : bitsValue (fun _ : Fin b => false) = (0 : BitVec b) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (bitsValue (fun _ : Fin b => false)).getLsbD i = false from bitsValue_bit _ ⟨i,hi⟩]
    simp
  rw [h]
  simp

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorVerifier
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

lemma zeroWord_value {k n : ℕ} (a : BooleanNetwork k n) (x : Basis k) :
    (zeroWord a).eval x 0=true ↔ (bitsValue (a.eval x)).toNat=0 := by
  rw [zeroWord,equalOn_value,wordConstant_eval]
  simp

lemma productNet_nat {k w : ℕ} (as : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((productNet as).eval x)).toNat=
      (as.map (fun a => (bitsValue (a.eval x)).toNat)).prod % 2^w := by
  induction as with
  | nil => simp [productNet,wordConstant_eval]
  | cons a as ih =>
    simp only [productNet,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,ih,
      List.map_cons,List.prod_cons,Nat.mul_mod_mod]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OracleLayout
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma packed_input {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin n) :
    packed r x y ⟨i.val,by omega⟩ = x i := by simp [packed, i.isLt]

lemma packed_target {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin m) :
    packed r x y ⟨n+i.val,by omega⟩ = y i := by simp [packed, i.isLt]

lemma packed_work {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin (n+m+r))
    (hi : n+m ≤ i.val) : packed r x y i = false := by
  simp [packed, show ¬ i.val<n by omega, show ¬ i.val<n+m by omega]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PackedPrograms
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma packed_first {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y ∘ firstRegister n m r = x := by
  funext i
  exact packed_input x y i

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSamplerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness
namespace OrderTrial

lemma natBasis_value (w z : ℕ) : (bitsValue (natBasis w z)).toNat=z%2^w := by
  change (bitsValue (fun i : Fin w => (BitVec.ofNat w z).getLsbD i.val)).toNat=z%2^w
  exact congrArg BitVec.toNat (bitsValue_bits (BitVec.ofNat w z))

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalExpressions
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ifLe _root_.OAI.ExactQuantumFactoring.IntExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifIntLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_inv _root_.OAI.ExactQuantumFactoring.RatExpr.eval_neg _root_.OAI.ExactQuantumFactoring.RatExpr.eval_num _root_.OAI.ExactQuantumFactoring.RatExpr.eval_over _root_.OAI.ExactQuantumFactoring.RatExpr.eval_power _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.RatExpr.eval_times
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace RatExpr
variable {v : Type*}

lemma normalize_den_pos (x : v → ℕ) (a : RatExpr v) : 0 < a.normalize.den.eval x := by
  change 0 < if a.den.eval x ≤ 0 then 1 else a.den.eval x
  split_ifs <;> omega
@[simp] lemma eval_add (x : v → ℕ) (a b : RatExpr v) : (add a b).eval x=a.eval x+b.eval x := by
  have ha : (a.normalize.den.eval x : ℚ) ≠ 0 := by exact_mod_cast (normalize_den_pos x a).ne'
  have hb : (b.normalize.den.eval x : ℚ) ≠ 0 := by exact_mod_cast (normalize_den_pos x b).ne'
  rw [← eval_normalize x a,← eval_normalize x b]
  simp only [add,eval,IntExpr.eval_add,IntExpr.eval_scale,NatExpr.eval,Int.cast_add,
    Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
  field_simp
@[simp] lemma eval_sub (x : v → ℕ) (a b : RatExpr v) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,sub_eq_add_neg]

end RatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolynomialExpressions
attribute [-instance] _root_.OAI.ExactQuantumFactoring.PolyExpr.instAdd _root_.OAI.ExactQuantumFactoring.PolyExpr.instMul _root_.OAI.ExactQuantumFactoring.PolyExpr.instNeg _root_.OAI.ExactQuantumFactoring.PolyExpr.instOfNat _root_.OAI.ExactQuantumFactoring.PolyExpr.instPowNat _root_.OAI.ExactQuantumFactoring.PolyExpr.instSub _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PolyExpr.eval_minus _root_.OAI.ExactQuantumFactoring.PolyExpr.eval_neg _root_.OAI.ExactQuantumFactoring.PolyExpr.eval_num _root_.OAI.ExactQuantumFactoring.PolyExpr.eval_plus _root_.OAI.ExactQuantumFactoring.PolyExpr.eval_power _root_.OAI.ExactQuantumFactoring.PolyExpr.eval_times _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifIntLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_inv _root_.OAI.ExactQuantumFactoring.RatExpr.eval_neg _root_.OAI.ExactQuantumFactoring.RatExpr.eval_num _root_.OAI.ExactQuantumFactoring.RatExpr.eval_over _root_.OAI.ExactQuantumFactoring.RatExpr.eval_power _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.RatExpr.eval_times
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace RatExpr
variable {v : Type*}
@[simp] lemma eval_sum (x : v → ℕ) (f : ℕ → RatExpr v) (n : ℕ) :
    (sum f n).eval x=∑ i ∈ Finset.range n, (f i).eval x := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp [sum,ih,Finset.sum_range_succ]
end RatExpr

namespace PolyExpr
variable {v : Type*}
open Polynomial

lemma coeff_correct (x : v → ℕ) (p : PolyExpr v) (k : ℕ) :
    (p.coeff k).eval x=(p.eval x).coeff k := by
  induction p generalizing k with
  | C c =>
    by_cases h : k=0 <;> simp [coeff,eval,Polynomial.coeff_C,h]
  | X =>
    by_cases h : k=1 <;> simp [coeff,eval,Polynomial.coeff_X,h,eq_comm]
  | add a b ia ib => simp [coeff,eval,ia,ib]
  | negation a ia => simp [coeff,eval,ia]
  | mul a b ia ib =>
    simp only [coeff,RatExpr.eval_sum,RatExpr.eval_mul,ia,ib,eval,Polynomial.coeff_mul]
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (a.eval x).coeff i*(b.eval x).coeff j) k).symm

end PolyExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FilterExpressionSyntax
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifIntLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace RatExpr
variable {v : Type*}
@[simp] lemma eval_plus (x : v → ℕ) (a b : RatExpr v) : (a+b).eval x=a.eval x+b.eval x := eval_add x a b
@[simp] lemma eval_minus (x : v → ℕ) (a b : RatExpr v) : (a-b).eval x=a.eval x-b.eval x := eval_sub x a b
end RatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalRounding
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ifLe _root_.OAI.ExactQuantumFactoring.IntExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifIntLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_inv _root_.OAI.ExactQuantumFactoring.RatExpr.eval_minus _root_.OAI.ExactQuantumFactoring.RatExpr.eval_neg _root_.OAI.ExactQuantumFactoring.RatExpr.eval_num _root_.OAI.ExactQuantumFactoring.RatExpr.eval_over _root_.OAI.ExactQuantumFactoring.RatExpr.eval_plus _root_.OAI.ExactQuantumFactoring.RatExpr.eval_power _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.RatExpr.eval_sum _root_.OAI.ExactQuantumFactoring.RatExpr.eval_times
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace IntExpr
variable {v : Type*}

lemma ceil_ratio_nat (z : ℤ) (d : ℕ) :
    (Int.ceil ((z:ℚ)/d)).toNat=(z.toNat+d-1)/d := by
  by_cases hd : d=0
  · simp [hd]
  have hd' : (0:ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  apply eq_of_forall_ge_iff
  intro k
  rw [Int.toNat_le,Int.ceil_le,Int.cast_natCast,div_le_iff₀ hd',
    ← Nat.ceilDiv_eq_add_pred_div,ceilDiv_le_iff_le_mul (Nat.pos_of_ne_zero hd),
    Int.toNat_le]
  push_cast
  rw [mul_comm]
  norm_cast

@[simp] lemma eval_ceilRatioNat (x : v → ℕ) (a : IntExpr v) (b : NatExpr v) :
    (ceilRatioNat a b).eval x=(Int.ceil ((a.eval x:ℚ)/(b.eval x:ℚ))).toNat := by
  simp only [ceilRatioNat,NatExpr.eval,eval_toNat,ceil_ratio_nat]

@[simp] lemma eval_floorRatio (x : v → ℕ) (a : IntExpr v) (b : NatExpr v) :
    (floorRatio a b).eval x=Int.floor ((a.eval x:ℚ)/(b.eval x:ℚ)) := by
  simp only [floorRatio,eval_sub,eval_ofNat,NatExpr.eval,eval_toNat,eval_ceilRatioNat,
    eval_negation]
  by_cases hz : 0 ≤ a.eval x
  · have hc : Int.ceil (((-a.eval x:ℤ):ℚ)/(b.eval x:ℚ)) ≤ 0 := by
      rw [Int.ceil_le,Int.cast_zero]
      exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast neg_nonpos.mpr hz) (by positivity)
    rw [Int.toNat_of_nonpos hc,Int.natCast_zero,sub_zero]
    rw [Int.natCast_ediv,← Rat.floor_natCast_div_natCast]
    congr 2
    exact_mod_cast Int.toNat_of_nonneg hz
  · have hp : (a.eval x).toNat=0 := by omega
    rw [hp,Nat.zero_div,Int.natCast_zero,zero_sub]
    have hc : 0 ≤ Int.ceil (((-a.eval x:ℤ):ℚ)/(b.eval x:ℚ)) :=
      Int.ceil_nonneg (div_nonneg (by exact_mod_cast (show 0 ≤ -a.eval x by omega)) (by positivity))
    rw [Int.toNat_of_nonneg hc,Int.cast_neg,neg_div,Int.ceil_neg,neg_neg]

end IntExpr

namespace RatExpr
variable {v : Type*}
@[simp] lemma eval_ceilNat (x : v → ℕ) (a : RatExpr v) :
    a.ceilNat.eval x=(Int.ceil (a.eval x)).toNat := by
  simp [ceilNat,eval]
@[simp] lemma eval_floor (x : v → ℕ) (a : RatExpr v) : a.floor.eval x=Int.floor (a.eval x) := by
  simp [floor,eval]
@[simp] lemma eval_ceil (x : v → ℕ) (a : RatExpr v) : a.ceil.eval x=Int.ceil (a.eval x) := by
  simp [ceil,Int.floor_neg]
end RatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ThresholdRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Exact threshold thinning by a FIXED (not rejection-sampled) block of fair
bits. The complete block is retained in the physical history. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BooleanNetwork BitArithmetic

lemma thresholdExpr_eval {v : Type*} (x : v→ℕ) (T : ℕ) (p : RatExpr v) (coin : NatExpr v) :
    (thresholdExpr T p coin).eval x=1 ↔
      coin.eval x<(Int.floor (p.eval x*(2:ℚ)^T)).toNat := by
  simp only [thresholdExpr,NatExpr.eval,IntExpr.eval_toNat,RatExpr.eval_floor,RatExpr.eval_times,
    RatExpr.eval_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  split_ifs with h
  · exact ⟨fun _ => Nat.lt_of_succ_le h,fun _ => rfl⟩
  · exact ⟨False.elim,fun hh => h (Nat.succ_le_of_lt hh)⟩

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialRawPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma productLayout_apply {α β : Type*} {p q : ℕ} (e : α≃Basis p) (f : β≃Basis q) (xy : α×β) :
    productLayout e f xy=Fin.append (e xy.1) (f xy.2) := rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProgressionEvaluation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Constant-length exact evaluation of the selected arithmetic progression.
The exponentially many progression points are replaced by seven truncated
arithmetic sums. This is the explicit arithmetic behind source Lemma 4.1. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma linearSum_correct (a b : ℚ) (lo hi : ℕ) :
    linearSum a b lo hi = ∑ i ∈ Finset.Ico lo hi, (a+b*i) := by
  rw [linearSum,fiveTermSum_correct]
  apply Finset.sum_congr rfl
  intro i _
  norm_num [Finset.sum_range_succ]

lemma sum_ramp_filter_nonneg (a b : ℚ) (M : ℕ) :
    (∑ i ∈ Finset.range M, max 0 (a+b*i)) =
      ∑ i ∈ (Finset.range M).filter (fun i : ℕ => 0 ≤ a+b*(i:ℚ)), (a+b*i) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ a+b*i
  · rw [ite_eq_left h,max_eq_right h]
  · rw [ite_eq_right h,max_eq_left (le_of_not_ge h)]

lemma sum_ramp_filter_pos (a b : ℚ) (M : ℕ) :
    (∑ i ∈ Finset.range M, max 0 (a+b*i)) =
      ∑ i ∈ (Finset.range M).filter (fun i : ℕ => 0 < a+b*(i:ℚ)), (a+b*i) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < a+b*i
  · rw [ite_eq_left h,max_eq_right h.le]
  · rw [ite_eq_right h,max_eq_left (le_of_not_gt h)]

lemma rampSum_correct (a b : ℚ) (M : ℕ) :
    rampSum a b M = ∑ i ∈ Finset.range M, max 0 (a+b*i) := by
  unfold rampSum
  split_ifs with hp hn
  · rw [linearSum_correct,sum_ramp_filter_nonneg]
    congr 1
    ext i
    simp only [Finset.mem_Ico,Finset.mem_filter,Finset.mem_range,
      Int.toNat_le,Int.ceil_le,Int.cast_natCast,div_le_iff₀ hp]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  · rw [linearSum_correct,sum_ramp_filter_pos]
    congr 1
    ext i
    simp only [Finset.mem_Ico,Finset.mem_filter,Finset.mem_range,
      zero_le, true_and,lt_min_iff,Int.lt_toNat,Int.lt_ceil,Int.cast_natCast,
      lt_div_iff_of_neg hn]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  · have hb : b=0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    simp [hb]

lemma phaseSumRe_correct (a b : ℚ) (M : ℕ) :
    (phaseSumRe a b M : ℝ) =
      ∑ i ∈ Finset.range M, splineReDeriv ((a:ℝ)+(b:ℝ)*i) := by
  simp only [phaseSumRe,linearSum_correct,rampSum_correct,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,Rat.cast_natCast,
    Rat.cast_ofNat,Rat.cast_div,Rat.cast_one,Rat.cast_sum,Rat.cast_max,Rat.cast_zero,
    Nat.Ico_zero_eq_range,splineReDeriv,sub_add_eq_add_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_neg_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

lemma phaseSumIm_correct (a b : ℚ) (M : ℕ) :
    (phaseSumIm a b M : ℝ) =
      ∑ i ∈ Finset.range M, splineImDeriv ((a:ℝ)+(b:ℝ)*i) := by
  have hh' (i : ℕ) : (a:ℝ)+1/4+(b:ℝ)*i = (a:ℝ)+(b:ℝ)*i+1/4 := by ring
  simp only [phaseSumIm,linearSum_correct,rampSum_correct,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,
    Rat.cast_ofNat,Rat.cast_div,Rat.cast_one,Rat.cast_sum,Rat.cast_max,Rat.cast_zero,
    Nat.Ico_zero_eq_range,splineImDeriv,hh',sub_add_eq_add_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

lemma phaseSum_correct (a b : ℚ) (M : ℕ)
    (h : ∀ i < M, -(1/2:ℝ) ≤ (a:ℝ)+(b:ℝ)*i ∧ (a:ℝ)+(b:ℝ)*i ≤ 3/2) :
    ((phaseSumRe a b M : ℚ):ℂ)+((phaseSumIm a b M : ℚ):ℂ)*Complex.I =
      ∑ i ∈ Finset.range M, phase ((a:ℝ)+(b:ℝ)*i) := by
  apply Complex.ext
  · simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ratCast_re,Complex.ratCast_im,mul_zero,zero_mul,sub_self,add_zero,
      Complex.re_sum,phase]
    rw [phaseSumRe_correct]
    apply Finset.sum_congr rfl
    intro i hi
    exact splineReDeriv_eq (h i (Finset.mem_range.mp hi)).1 (h i (Finset.mem_range.mp hi)).2
  · simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ratCast_re,Complex.ratCast_im,mul_zero,mul_one,add_zero,zero_add,
      Complex.im_sum,phase]
    rw [phaseSumIm_correct]
    apply Finset.sum_congr rfl
    intro i hi
    exact splineImDeriv_eq (h i (Finset.mem_range.mp hi)).1 (h i (Finset.mem_range.mp hi)).2

lemma sampleLine_cast (Q d j t i : ℕ) :
    (sampleOffset Q d j t:ℝ)+(sampleSlope Q d j:ℝ)*i =
      ((j*t)%d:ℕ)/(d:ℝ)+binError Q d j*((t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q)) := by
  simp only [sampleOffset,sampleSlope,Rat.cast_add,Rat.cast_div,Rat.cast_mul,
    Rat.cast_natCast,binErrorRat_cast]
  ring

lemma sampleLine_bounds {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j i : ℕ) (hi : i < sampleCount Q d t) :
    -(1/2:ℝ) ≤ (sampleOffset Q d j t:ℝ)+(sampleSlope Q d j:ℝ)*i ∧
      (sampleOffset Q d j t:ℝ)+(sampleSlope Q d j:ℝ)*i ≤ 3/2 := by
  rw [sampleLine_cast]
  have hQ : (0:ℝ) < Q := by exact_mod_cast lt_of_lt_of_le hd hdQ
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hu : (0:ℝ) ≤ ((j*t)%d:ℕ)/(d:ℝ) := by positivity
  have hu' : ((j*t)%d:ℕ)/(d:ℝ) < 1 := by
    rw [div_lt_one hd']
    exact_mod_cast Nat.mod_lt (j*t) hd
  have hv : (0:ℝ) ≤ (t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q) := by positivity
  have hv' : (t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q) ≤ 1 := by
    have h := (lt_sampleCount_iff hd hdQ ht).mp hi
    have h' : (t:ℝ)+i*d ≤ Q := by exact_mod_cast h.le
    have he : (t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q) = ((t:ℝ)+i*d)/Q := by ring
    rw [he,div_le_one hQ]
    exact h'
  rcases abs_le.mp (binError_bound (Q:=Q) (j:=j) hd) with ⟨he₀,he₁⟩
  have hm₀ := mul_le_mul_of_nonneg_right he₀ hv
  have hm₁ := mul_le_mul_of_nonneg_right he₁ hv
  constructor <;> nlinarith

lemma residueAmplitude_fast {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    residueAmplitude Q d j t = (Q:ℂ)⁻¹ *
      ((phaseSumRe (sampleOffset Q d j t) (sampleSlope Q d j) (sampleCount Q d t):ℂ)+
        (phaseSumIm (sampleOffset Q d j t) (sampleSlope Q d j) (sampleCount Q d t):ℂ)*Complex.I) := by
  rw [phaseSum_correct _ _ _ (fun i hi => sampleLine_bounds hd hdQ ht j i hi),
    residueAmplitude_samples hd hdQ ht]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [sampleLine_cast]

lemma fastResidueProbability_correct {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    (fastResidueProbability Q d j t:ℝ) = residueProbability Q d j t := by
  rw [residueProbability,residueAmplitude_fast hd hdQ ht]
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_mul,Complex.normSq_inv]
  simp [fastResidueProbability,Complex.normSq_apply,div_eq_mul_inv,pow_two]
  ring

lemma fastResidueProbability_eq {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    fastResidueProbability Q d j t = residueProbabilityRat Q d j t := by
  apply Rat.cast_injective (α:=ℝ)
  rw [fastResidueProbability_correct hd hdQ ht,
    residueProbabilityRat_cast (lt_of_lt_of_le hd hdQ)]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalConditionals
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ceilRatioNat _root_.OAI.ExactQuantumFactoring.IntExpr.eval_floorRatio _root_.OAI.ExactQuantumFactoring.IntExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ceil _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ceilNat _root_.OAI.ExactQuantumFactoring.RatExpr.eval_floor _root_.OAI.ExactQuantumFactoring.RatExpr.eval_inv _root_.OAI.ExactQuantumFactoring.RatExpr.eval_minus _root_.OAI.ExactQuantumFactoring.RatExpr.eval_neg _root_.OAI.ExactQuantumFactoring.RatExpr.eval_num _root_.OAI.ExactQuantumFactoring.RatExpr.eval_over _root_.OAI.ExactQuantumFactoring.RatExpr.eval_plus _root_.OAI.ExactQuantumFactoring.RatExpr.eval_power _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.RatExpr.eval_sum _root_.OAI.ExactQuantumFactoring.RatExpr.eval_times
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace RatExpr
variable {v : Type*}

@[simp] lemma eval_ifLe (x : v → ℕ) (a b c d : RatExpr v) :
    (ifLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  rw [ifLe,eval_ifIntLe]
  simp only [IntExpr.eval_scale]
  have ha : (0 : ℚ) < a.normalize.den.eval x := by exact_mod_cast normalize_den_pos x a
  have hb : (0 : ℚ) < b.normalize.den.eval x := by exact_mod_cast normalize_den_pos x b
  have he : a.normalize.num.eval x * b.normalize.den.eval x ≤
      b.normalize.num.eval x * a.normalize.den.eval x ↔ a.eval x ≤ b.eval x := by
    rw [← eval_normalize x a,← eval_normalize x b,eval,eval,div_le_div_iff₀ ha hb]
    norm_cast
  simp only [he]

@[simp] lemma eval_ifLt (x : v → ℕ) (a b c d : RatExpr v) :
    (ifLt a b c d).eval x = if a.eval x < b.eval x then c.eval x else d.eval x := by
  simp only [ifLt,eval_ifLe]
  by_cases h : a.eval x < b.eval x
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]
@[simp] lemma eval_ifEq (x : v → ℕ) (a b c d : RatExpr v) :
    (ifEq a b c d).eval x = if a.eval x = b.eval x then c.eval x else d.eval x := by
  simp only [ifEq,eval_ifLe]
  by_cases h : a.eval x = b.eval x
  · simp [h]
  · by_cases h₁ : a.eval x ≤ b.eval x
    · have h₂ : ¬b.eval x ≤ a.eval x := fun hh => h (le_antisymm h₁ hh)
      simp [h,h₁,h₂]
    · simp [h,h₁]
@[simp] lemma eval_max (x : v → ℕ) (a b : RatExpr v) : (max a b).eval x=Max.max (a.eval x) (b.eval x) := by
  simp [max,_root_.max_def]
@[simp] lemma eval_min (x : v → ℕ) (a b : RatExpr v) : (min a b).eval x=Min.min (a.eval x) (b.eval x) := by
  simp [min,_root_.min_def]
end RatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProgressionExpressions
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace OrderTrial.Expressions
variable {v : Type*}
open RatExpr

lemma powerSum_correct (x : v → ℕ) (q : ℕ) (M : RatExpr v) :
    (powerSum q M).eval x=powerSumValue q (M.eval x) := by
  rcases q with _|_|_|_|_|q <;> simp [powerSum,powerSumValue]

lemma fiveTerm_correct (x : v → ℕ) (a : ℕ → RatExpr v) (lo hi : NatExpr v) :
    (fiveTerm a lo hi).eval x=fiveTermSum (fun q => (a q).eval x) (lo.eval x) (hi.eval x) := by
  simp [fiveTerm,fiveTermSum,powerSum_correct]

lemma linear_correct (x : v → ℕ) (a b : RatExpr v) (lo hi : NatExpr v) :
    (linear a b lo hi).eval x=linearSum (a.eval x) (b.eval x) (lo.eval x) (hi.eval x) := by
  rw [linear,fiveTerm_correct,linearSum]
  congr 1
  funext q
  split_ifs <;> simp

lemma ramp_correct (x : v → ℕ) (a b : RatExpr v) (M : NatExpr v) :
    (ramp a b M).eval x=rampSum (a.eval x) (b.eval x) (M.eval x) := by
  simp [ramp,rampSum,linear_correct,NatExpr.eval]

lemma phaseRe_correct (x : v → ℕ) (a b : RatExpr v) (M : NatExpr v) :
    (phaseRe a b M).eval x=phaseSumRe (a.eval x) (b.eval x) (M.eval x) := by
  simp [phaseRe,phaseSumRe,linear_correct,ramp_correct,NatExpr.eval]

lemma phaseIm_correct (x : v → ℕ) (a b : RatExpr v) (M : NatExpr v) :
    (phaseIm a b M).eval x=phaseSumIm (a.eval x) (b.eval x) (M.eval x) := by
  simp [phaseIm,phaseSumIm,linear_correct,ramp_correct,NatExpr.eval]

lemma binE_correct (x : v → ℕ) (Q d j : NatExpr v) :
    (binE Q d j).eval x=bin (Q.eval x) (d.eval x) (j.eval x) := rfl

lemma error_correct (x : v → ℕ) (Q d j : NatExpr v) :
    (error Q d j).eval x=binErrorRat (Q.eval x) (d.eval x) (j.eval x) := by
  simp [error,binErrorRat,binE_correct]

lemma offset_correct (x : v → ℕ) (Q d j t : NatExpr v) :
    (offset Q d j t).eval x=sampleOffset (Q.eval x) (d.eval x) (j.eval x) (t.eval x) := by
  simp [offset,sampleOffset,error_correct,NatExpr.eval]

lemma slope_correct (x : v → ℕ) (Q d j : NatExpr v) :
    (slope Q d j).eval x=sampleSlope (Q.eval x) (d.eval x) (j.eval x) := by
  simp [slope,sampleSlope,error_correct]

lemma count_correct (x : v → ℕ) (Q d t : NatExpr v) :
    (count Q d t).eval x=sampleCount (Q.eval x) (d.eval x) (t.eval x) := rfl

lemma probability_correct (x : v → ℕ) (Q d j t : NatExpr v) :
    (probability Q d j t).eval x=fastResidueProbability (Q.eval x) (d.eval x) (j.eval x) (t.eval x) := by
  simp [probability,fastResidueProbability,phaseRe_correct,phaseIm_correct,
    offset_correct,slope_correct,count_correct]
end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolynomialFilterExpressions
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace RatExpr
variable {v : Type*}
@[simp] lemma eval_sumList {α : Type*} (x : v → ℕ) (f : α → RatExpr v) (as : List α) :
    (sumList f as).eval x=(as.map (fun a => (f a).eval x)).sum := by
  induction as with
  | nil => simp [sumList]
  | cons a as ih => simp [sumList,ih]
end RatExpr

namespace OrderTrial.Expressions
variable {v : Type*}
open RatExpr

lemma rampPoly_correct (x : v → ℕ) (q a : ℤ) :
    (rampPoly q a).eval x=rampPiece q a := by
  by_cases h : a ≤ q <;> simp [rampPoly,rampPiece,h,PolyExpr.eval]
lemma rampLin_correct (x : v → ℕ) (q a : ℤ) :
    (rampLin q a).eval x=rampLinear q a := by
  by_cases h : a ≤ q <;> simp [rampLin,rampLinear,h,PolyExpr.eval]

lemma splineRePoly_correct (x : v → ℕ) (q : ℤ) :
    (splineRePoly q).eval x=splineRePiece q := by
  simp [splineRePoly,splineRePiece,rampPoly_correct,PolyExpr.eval]
lemma splineImPoly_correct (x : v → ℕ) (q : ℤ) :
    (splineImPoly q).eval x=splineImPiece q := by
  simp [splineImPoly,splineImPiece,rampPoly_correct,PolyExpr.eval]
lemma phaseRePoly_correct (x : v → ℕ) (q : ℤ) :
    (phaseRePoly q).eval x=phaseRePiece q := by
  simp [phaseRePoly,phaseRePiece,rampLin_correct,PolyExpr.eval]
lemma phaseImPoly_correct (x : v → ℕ) (q : ℤ) :
    (phaseImPoly q).eval x=phaseImPiece q := by
  simp [phaseImPoly,phaseImPiece,rampLin_correct,PolyExpr.eval]

lemma linearPoly_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) :
    (linearPoly d η).eval x=linearArg (d.eval x) (η.eval x) := by
  simp [linearPoly,linearArg,PolyExpr.eval]

lemma massCoeff_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : ℤ) (k : ℕ) :
    (massCoeff d η q₀ q₁ k).eval x=(massPiece (d.eval x) (η.eval x) q₀ q₁).coeff k := by
  by_cases h : η.eval x=0 <;>
    simp [massCoeff,RatExpr.eval_ifEq,PolyExpr.coeff_correct,h,massPiece,integralPiece,
      massZero,massSlope,integralZero,integralSlope,linearPoly_correct,
      phaseRePoly_correct,phaseImPoly_correct,splineRePoly_correct,splineImPoly_correct,
      PolyExpr.eval]

lemma rounded_correct (x : v → ℕ) (D : NatExpr v) (a : RatExpr v) :
    (rounded D a).eval x=roundCoeff (D.eval x) (a.eval x) := by
  simp [rounded,roundCoeff]

lemma roundingDen_correct (x : v → ℕ) (Q B : NatExpr v) :
    (roundingDen Q B).eval x=Q.eval x*(B.eval x)^8 := by
  simp [roundingDen,NatExpr.eval]

lemma low_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) :
    (low d η q).eval x=pieceLo (d.eval x) (η.eval x) q := by
  simp [low,pieceLo,intervalLo]
lemma high_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) :
    (high d η q).eval x=pieceHi (d.eval x) (η.eval x) q := by
  simp [high,pieceHi,intervalHi]

lemma pieceSum_correct (x : v → ℕ) (Q B d j : NatExpr v) (q : ℤ×ℤ) :
    (pieceSum Q B d j q).eval x=packedPieceSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x) q := by
  simp [pieceSum,packedPieceSum,fiveTerm_correct,rounded_correct,roundingDen_correct,
    massCoeff_correct,error_correct,low_correct,high_correct,NatExpr.eval]

lemma quarterList_nodup : quarterList.Nodup := by decide
lemma quarterList_finset : quarterList.toFinset=quarterPairs := by decide

lemma majorantSumE_correct (x : v → ℕ) (Q B d j : NatExpr v) :
    (majorantSumE Q B d j).eval x=packedMajorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x) := by
  simp only [majorantSumE,RatExpr.eval_over,RatExpr.eval_num,RatExpr.eval_sumList,
    pieceSum_correct,packedMajorantSum]
  rw [← List.sum_toFinset _ quarterList_nodup,quarterList_finset]
  norm_num

end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DynamicMajorantExpressions
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : Type*}
open RatExpr

lemma dynamicRamp_correct (x : v → ℕ) (q : IntExpr v) (a : ℤ) :
    (dynamicRamp q a).eval x=rampPiece (q.eval x) a := by
  by_cases h : a ≤ q.eval x <;> simp [dynamicRamp,rampPiece,h,PolyExpr.eval]
lemma dynamicRampLin_correct (x : v → ℕ) (q : IntExpr v) (a : ℤ) :
    (dynamicRampLin q a).eval x=rampLinear (q.eval x) a := by
  by_cases h : a ≤ q.eval x <;> simp [dynamicRampLin,rampLinear,h,PolyExpr.eval]

lemma dynamicSplineRe_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicSplineRe q).eval x=splineRePiece (q.eval x) := by
  simp [dynamicSplineRe,splineRePiece,dynamicRamp_correct,PolyExpr.eval]
lemma dynamicSplineIm_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicSplineIm q).eval x=splineImPiece (q.eval x) := by
  simp [dynamicSplineIm,splineImPiece,dynamicRamp_correct,PolyExpr.eval]
lemma dynamicPhaseRe_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicPhaseRe q).eval x=phaseRePiece (q.eval x) := by
  simp [dynamicPhaseRe,phaseRePiece,dynamicRampLin_correct,PolyExpr.eval]
lemma dynamicPhaseIm_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicPhaseIm q).eval x=phaseImPiece (q.eval x) := by
  simp [dynamicPhaseIm,phaseImPiece,dynamicRampLin_correct,PolyExpr.eval]


lemma dynamicMassCoeff_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v)
    (q₀ q₁ : IntExpr v) (k : ℕ) :
    (dynamicMassCoeff d η q₀ q₁ k).eval x=
      (massPiece (d.eval x) (η.eval x) (q₀.eval x) (q₁.eval x)).coeff k := by
  by_cases h : η.eval x=0 <;>
    simp [dynamicMassCoeff,RatExpr.eval_ifEq,PolyExpr.coeff_correct,h,massPiece,integralPiece,
      dynamicMassZero,dynamicMassSlope,integralZero,integralSlope,linearPoly_correct,
      dynamicPhaseRe_correct,dynamicPhaseIm_correct,dynamicSplineRe_correct,dynamicSplineIm_correct,
      PolyExpr.eval]

lemma quarter_correct (x : v → ℕ) (a : RatExpr v) :
    (quarter a).eval x=quarterIndex (a.eval x) := by simp [quarter,quarterIndex]

lemma majorantE_correct (x : v → ℕ) (Q B d j u : NatExpr v) :
    (majorantE Q B d j u).eval x=
      majorant (Q.eval x) (B.eval x) (d.eval x) (j.eval x) (u.eval x) := by
  simp [majorantE,majorant,roundedValue,selectedMass,rounded_correct,roundingDen_correct,
    dynamicMassCoeff_correct,error_correct,quarter_correct]

end ExactQuantumFactoring.OrderTrial.Expressions


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetentionExpressions
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial.Expressions
open RatExpr
variable {v : Type*}

lemma coveringPow_correct (x : v → ℕ) (d : NatExpr v) (n : ℕ)
    (hd : d.eval x≤2^n) : (coveringPow d n).eval x=2^(Nat.clog 2 (d.eval x)) := by
  induction n with
  | zero =>
    have hc : Nat.clog 2 (d.eval x)=0 := Nat.eq_zero_of_le_zero (Nat.clog_le_of_le_pow hd)
    simp [coveringPow,NatExpr.eval,hc]
  | succ n ih =>
    change (if d.eval x≤2^n then (coveringPow d n).eval x else 2^(n+1))=_
    by_cases h : d.eval x≤2^n
    · rw [ite_eq_left h]; exact ih h
    · have hc : Nat.clog 2 (d.eval x)=n+1 := by
        have h₁ := Nat.clog_le_of_le_pow hd
        have h₂ := (Nat.lt_clog_iff_pow_lt (by omega : 1<2)).mpr (Nat.lt_of_not_ge h)
        omega
      rw [ite_eq_right h,hc]

lemma lambdaE_correct (x : v → ℕ) (n : ℕ) (d : NatExpr v) (hd : d.eval x≤2^n) :
    (lambdaE n d).eval x=prescribedMass (d.eval x) := by
  simp [lambdaE,coveringPow_correct x d n hd,prescribedMass,NatExpr.eval,pow_add]
  ring

lemma coefficientE_correct (x : v → ℕ) (n : ℕ) (Q B d j : NatExpr v) (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (coefficientE n Q B d j).eval x=
      modeCoeff n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [coefficientE,lambdaE_correct x n d hd,majorantSumE_correct,packedMajorantSum_correct hpos,modeCoeff,NatExpr.eval,mul_div_assoc]

lemma remainderE_correct (x : v → ℕ) (n : ℕ) (Q B d j : NatExpr v) (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (remainderE n Q B d j).eval x=
      modeRemainder n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [remainderE,lambdaE_correct x n d hd,coefficientE_correct x n Q B d j hd hpos,
    majorantSumE_correct,packedMajorantSum_correct hpos,modeRemainder]

lemma discrepancyE_correct (x : v → ℕ) (n : ℕ) (Q B d j t : NatExpr v) (hd : d.eval x≤2^n)
    (hdt : 0<d.eval x) (ht : t.eval x<d.eval x) (hdQ : d.eval x≤Q.eval x) :
    (discrepancyE n Q B d j t).eval x =
      2*(B.eval x:ℚ)^3*(majorant (Q.eval x) (B.eval x) (d.eval x) (j.eval x)
        ((j.eval x*t.eval x)%d.eval x)-residueProbabilityRat (Q.eval x) (d.eval x) (j.eval x) (t.eval x))*
        modeCoeff n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [discrepancyE,majorantE_correct,coefficientE_correct x n Q B d j hd hdt,NatExpr.eval,
    probability_correct,fastResidueProbability_eq hdt hdQ ht]

lemma thirdRetentionE_correct (x : v → ℕ) (n : ℕ) (Q B d j : NatExpr v) (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (thirdRetentionE n Q B d j).eval x=4*(B.eval x:ℚ)^2*
      modeRemainder n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [thirdRetentionE,remainderE_correct x n Q B d j hd hpos]

end ExactQuantumFactoring.OrderTrial.Expressions


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetentionCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
lemma retentionNet_value {v : Type*} {k b : ℕ} (T : ℕ) (p : RatExpr v) (coin : NatExpr v)
    (vars : v → BooleanNetwork k b) (x : Basis k) :
    (retentionNet T p coin vars).eval x 0=true ↔
      coin.eval (fun i => (bitsValue ((vars i).eval x)).toNat)<
        (Int.floor (p.eval (fun i => (bitsValue ((vars i).eval x)).toNat)*(2:ℚ)^T)).toNat := by
  rw [retentionNet,NatExpr.isOne_eval,thresholdExpr_eval]

namespace OrderTrial.Expressions
variable {v : Type*}

lemma firstE_value (x : v→ℕ) (n : ℕ) (d j : NatExpr v)
    (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (firstE n d j).eval x=firstRetention n (d.eval x) (j.eval x) := by
  exact coefficientE_correct x n _ _ d j hd hpos
lemma secondE_value (x : v→ℕ) (n : ℕ) (d j t : NatExpr v)
    (hd : d.eval x≤2^n) (hpos : 0<d.eval x) (ht : t.eval x<d.eval x) :
    (secondE n d j t).eval x=discrepancyRetention n (d.eval x) (j.eval x) (t.eval x) := by
  have hQ : d.eval x≤((2^n)^16) := hd.trans
    (Nat.le_self_pow (by decide : 16≠0) (2^n))
  have h := discrepancyE_correct x n (.const ((2^n)^16)) (.const (2^n)) d j t hd hpos ht hQ
  simpa only [NatExpr.eval,Nat.cast_pow,Nat.cast_ofNat,secondE,discrepancyRetention] using h
lemma lastE_value (x : v→ℕ) (n : ℕ) (d j : NatExpr v)
    (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (lastE n d j).eval x=remainderRetention n (d.eval x) (j.eval x) := by
  have h := thirdRetentionE_correct x n (.const ((2^n)^16)) (.const (2^n)) d j hd hpos
  simpa only [NatExpr.eval,Nat.cast_pow,Nat.cast_ofNat,lastE,remainderRetention] using h

end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletionFilterCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion
namespace Expressions
variable {v : Type*}

lemma ordinaryMass_value (x : v→ℕ) (t : ℕ) (s : RatExpr v) :
    (ordinaryMass t s).eval x=(1-1/(2:ℚ)^t)*s.eval x := by
  simp only [ordinaryMass,RatExpr.eval_mul,RatExpr.eval_const]
lemma coefficient_value (x : v→ℕ) (W t : ℕ) (s z : RatExpr v) :
    (coefficient W t s z).eval x=coeff W t (s.eval x) (z.eval x) := by
  simp only [coefficient,RatExpr.eval_div,RatExpr.eval_ofInt,RatExpr.eval_floor,
    RatExpr.eval_mul,RatExpr.eval_const,ordinaryMass_value,coeff,Exactness.completionCoeff]
lemma guess_value (x : v→ℕ) (W t : ℕ) (s z : RatExpr v) :
    (guess W t s z).eval x=guessRetention W t (s.eval x) (z.eval x) := by
  simp only [guess,RatExpr.eval_div,RatExpr.eval_mul,RatExpr.eval_sub,
    RatExpr.eval_const,coefficient_value,ordinaryMass_value,
    guessRetention,Exactness.completionRemainder,coeff]

end Expressions

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimeRecords
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma primeRecord_eq_factorization (ps : List ℕ) (hp : ∀ p∈ps,p.Prime) :
    primeRecord ps=ps.prod.factorization := by
  induction ps with
  | nil => simp [primeRecord]
  | cons p ps ih =>
    have hprime := hp p (by simp)
    have ht : ∀ q∈ps,q.Prime := fun q hq => hp q (by simp [hq])
    have hprod : ps.prod≠0 := by
      apply List.prod_ne_zero
      intro hzero
      exact (ht 0 hzero).ne_zero rfl
    rw [primeRecord,List.prod_cons,Nat.factorization_mul hprime.ne_zero hprod,
      hprime.factorization,ih ht]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveOrder
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma stripOrderPrime_multiple {G : Type*} [Monoid G] [DecidableEq G]
    (a : G) (hr : 0 < orderOf a) (q k : ℕ) :
    stripOrderPrime a q (orderOf a*k)=orderOf a*(if q∣k then k/q else k) := by
  let r := orderOf a
  have hcond : (q∣r*k ∧ a^((r*k)/q)=1) ↔ q∣k := by
    constructor
    · rintro ⟨hq,hpow⟩
      have h := orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hh : r*q∣r*k := by simpa only [Nat.mul_comm q] using (Nat.dvd_div_iff_mul_dvd hq).mp h
      exact (Nat.mul_dvd_mul_iff_left hr).mp hh
    · intro hk
      refine ⟨hk.mul_left r,?_⟩
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [Nat.mul_div_assoc r hk]
      exact dvd_mul_right r (k/q)
  change (if q∣r*k ∧ a^((r*k)/q)=1 then (r*k)/q else r*k)=_
  simp only [hcond]
  split_ifs with hq
  · exact Nat.mul_div_assoc r hq
  · rfl

lemma quotient_dvd_tail {k q v : ℕ} (hq : 0 < q) (hk : q∣k) (hkv : k∣q*v) : k/q ∣ v := by
  obtain ⟨c,hc⟩ := hkv
  refine ⟨c,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hq
  rw [← Nat.mul_assoc,Nat.mul_div_cancel' hk]
  exact hc

/-- Complete factor stripping: no excess prime can survive a scan of a known
factorization of a multiple of the initial quotient. There is no call to an
order oracle in this algorithm. -/
theorem stripOrderFactors_exact {G : Type*} [Monoid G] [DecidableEq G]
    (a : G) (hr : 0 < orderOf a) (qs : List ℕ)
    (hp : ∀ q∈qs, q.Prime) (k : ℕ) (hk : k∣qs.prod) :
    stripOrderFactors a qs (orderOf a*k)=orderOf a := by
  induction qs generalizing k with
  | nil =>
    have he : k=1 := Nat.dvd_one.mp hk
    simp [stripOrderFactors,he]
  | cons q qs ih =>
    have hq := hp q (by simp)
    have htail : ∀ p∈qs, p.Prime := fun p hh => hp p (by simp [hh])
    simp only [stripOrderFactors,stripOrderPrime_multiple a hr]
    apply ih htail
    by_cases hdiv : q∣k
    · rw [ite_eq_left hdiv]
      exact quotient_dvd_tail hq.pos hdiv hk
    · rw [ite_eq_right hdiv]
      exact (hq.coprime_iff_not_dvd.mpr hdiv).symm.dvd_of_dvd_mul_left hk

/-- Specializing to the known factorization of phi(m), as in source §5. The
factor list is explicit input produced by the completed auxiliary tree. -/
theorem strip_totient_factors {m : ℕ} (hm : 2 ≤ m) (a : (ZMod m)ˣ)
    (qs : List ℕ) (hp : ∀ q∈qs,q.Prime) (hprod : qs.prod=m.totient) :
    stripOrderFactors a qs m.totient=orderOf a := by
  let : NeZero m := ⟨by omega⟩
  have hd : orderOf a ∣ m.totient := by simpa [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using orderOf_dvd_natCard a
  have hr : 0 < orderOf a := orderOf_pos a
  have he := Nat.mul_div_cancel' hd
  have hq : m.totient/orderOf a ∣ qs.prod := by
    rw [hprod]
    exact (dvd_mul_left (m.totient/orderOf a) (orderOf a)).trans (dvd_of_eq he)
  rw [← he]
  exact stripOrderFactors_exact a hr qs hp _ hq

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DivisorData
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

lemma recordPrimes_prime {f : FactorRecord} (hp : ∀ p∈f.support,p.Prime) :
    ∀ p∈recordPrimes f,p.Prime := by
  intro p h
  obtain ⟨q,hq,hp'⟩ := List.mem_flatMap.mp h
  have he : p=q := (List.mem_replicate.mp hp').2
  subst p
  exact hp q ((Finset.mem_sort (· ≤ ·)).mp hq)

lemma recordPrimes_prod (f : FactorRecord) : (recordPrimes f).prod=f.prod (·^·) := by
  rw [recordPrimes,prod_flatMap]
  simp only [List.prod_replicate]
  rw [←List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
  rfl

lemma divisorPrimes_prime (m : ℕ) (ps : List ℕ) (hp : ∀ p∈ps,p.Prime) :
    ∀ p∈divisorPrimes m ps,p.Prime := by
  induction ps generalizing m with
  | nil => simp [divisorPrimes]
  | cons p ps ih =>
    have htail : ∀ q∈ps,q.Prime := fun q hq => hp q (by simp [hq])
    rw [divisorPrimes]
    split_ifs
    · intro q hq
      rcases List.mem_cons.mp hq with he | hq
      · subst q; exact hp p (by simp)
      · exact ih _ htail q hq
    · exact ih _ htail

lemma divisorPrimes_prod (ps : List ℕ) (hp : ∀ p∈ps,p.Prime) {m : ℕ} (hd : m∣ps.prod) :
    (divisorPrimes m ps).prod=m := by
  induction ps generalizing m with
  | nil =>
    have hm := Nat.dvd_one.mp hd
    simp [divisorPrimes,hm]
  | cons p ps ih =>
    have hprime := hp p (by simp)
    have htail : ∀ q∈ps,q.Prime := fun q hq => hp q (by simp [hq])
    rw [divisorPrimes]
    split_ifs with hdiv
    · rw [List.prod_cons,ih htail (quotient_dvd_tail hprime.pos hdiv hd),Nat.mul_div_cancel' hdiv]
    · exact ih htail ((hprime.coprime_iff_not_dvd.mpr hdiv).symm.dvd_of_dvd_mul_left hd)

@[simp] lemma trueData_factors (m : ℕ) : (trueData m).factors=m.factorization := by
  rw [trueData_eq]; rfl
@[simp] lemma trueData_descendants (m : ℕ) : (trueData m).descendants=(children m).map trueData := by
  rw [trueData_eq]; rfl

lemma dataDivisorPrimes_correct {M m : ℕ} (hM : 0<M) (hd : m∣M) :
    (∀ p∈dataDivisorPrimes (trueData M) m,p.Prime) ∧
      (dataDivisorPrimes (trueData M) m).prod=m := by
  have hp : ∀ p∈recordPrimes M.factorization,p.Prime :=
    recordPrimes_prime (fun _ => Nat.prime_of_mem_primeFactors)
  have hprod : (recordPrimes M.factorization).prod=M := by
    rw [recordPrimes_prod,Nat.prod_factorization_pow_eq_self hM.ne']
  refine ⟨?_,?_⟩
  · simpa only [dataDivisorPrimes,trueData_factors] using divisorPrimes_prime m _ hp
  · simpa only [dataDivisorPrimes,trueData_factors] using divisorPrimes_prod _ hp (show m∣(recordPrimes M.factorization).prod by rw [hprod]; exact hd)

lemma dataChildPrimes_correct {M label : ℕ} (h : label∈children M) :
    (∀ p∈dataChildPrimes (trueData M) label,p.Prime) ∧
      (dataChildPrimes (trueData M) label).prod=label := by
  have hex : ∃ d, ((children M).map trueData).find? (fun d => decide (d.label=label))=some d := by
    cases hf : ((children M).map trueData).find? (fun d => decide (d.label=label)) with
    | none =>
      have hh := List.find?_eq_none.mp hf (trueData label) (List.mem_map.mpr ⟨label,h,rfl⟩)
      simp only [trueData_label,decide_true] at hh
      contradiction
    | some d => exact ⟨d,rfl⟩
  obtain ⟨d,hd⟩ := hex
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hd)
  have he : l=label := by simpa only [trueData_label,decide_eq_true_eq] using List.find?_some hd
  subst l
  have hlabel := (child_bounds h).1
  simp only [dataChildPrimes,trueData_descendants,hd,trueData_factors]
  refine ⟨recordPrimes_prime (fun _ => Nat.prime_of_mem_primeFactors),?_⟩
  rw [recordPrimes_prod,Nat.prod_factorization_pow_eq_self (by omega)]

lemma dataTotientPrimes_correct {M m : ℕ} (hM : 0<M) (hm : 0 < m) (hd : m∣M) :
    (∀ p∈dataTotientPrimes (trueData M) m,p.Prime) ∧
      (dataTotientPrimes (trueData M) m).prod=m.totient := by
  obtain ⟨hprime,hprod⟩ := dataDivisorPrimes_correct hM hd
  have hf : primeRecord (dataDivisorPrimes (trueData M) m)=m.factorization := by
    rw [primeRecord_eq_factorization _ hprime,hprod]
  have hchild (p : ℕ) (hp : p∈m.factorization.support) (h2 : p≠2) :
      p-1∈children M := by
    have hpm : p.Prime ∧ p∣m ∧ m≠0 := Nat.mem_primeFactors.mp hp
    exact mem_children.mpr ⟨p,hpm.1,hpm.2.1.trans hd,hM.ne',by have := hpm.1.two_le; omega,rfl⟩
  rw [dataTotientPrimes,hf]
  refine ⟨?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
    have hq' := (Finset.mem_sort (· ≤ ·)).mp hq
    rcases List.mem_append.mp hp with hp | hp
    · have he := (List.mem_replicate.mp hp).2
      subst p
      exact Nat.prime_of_mem_primeFactors hq'
    · split_ifs at hp with h2
      · simp at hp
      · exact (dataChildPrimes_correct (hchild q hq' h2)).1 p hp
  · rw [prod_flatMap]
    calc
      _ = ((m.factorization.support.sort (· ≤ ·)).map
          (fun p => p^(m.factorization p-1)*(p-1))).prod := by
        congr 1
        apply List.map_congr_left
        intro p hp
        rw [List.prod_append,List.prod_replicate]
        split_ifs with h2
        · subst p
          simp
        · rw [(dataChildPrimes_correct (hchild p ((Finset.mem_sort (· ≤ ·)).mp hp) h2)).2]
      _ = m.factorization.prod (fun p e => p^(e-1)*(p-1)) := by
        rw [←List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
        rfl
      _ = m.totient := (Nat.totient_eq_prod_factorization hm.ne').symm

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

lemma stripPrimeNat_unit {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (q v : ℕ) :
    stripPrimeNat a m q v=stripOrderPrime u q v := by
  let : NeZero m := ⟨by omega⟩
  have he : a^(v/q)%m=1 ↔ u^(v/q)=1 := by
    rw [show a^(v/q)%m=((u^(v/q) : (ZMod m)ˣ) : ZMod m).val by
      rw [Units.val_pow_eq_pow_val,← ha,← Nat.cast_pow,ZMod.val_natCast]]
    constructor
    · intro h
      apply Units.ext
      apply ZMod.val_injective
      simpa only [Units.val_one,ZMod.val_one'' (by omega : m≠1)] using h
    · intro h
      rw [h,Units.val_one,ZMod.val_one'' (by omega : m≠1)]
  simp only [stripPrimeNat,stripOrderPrime,← Nat.dvd_iff_mod_eq_zero,he]

namespace BitArithmetic

@[simp] lemma liftInput_eval {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) (x : Basis l) :
    (liftInput a f).eval x=a.eval (x∘f) := by simp [liftInput,eval_comp]

lemma powOn_value {k w : ℕ} (a m e : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    (bitsValue ((powOn a m e).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^(bitsValue (e.eval x)).toNat%(bitsValue (m.eval x)).toNat := by
  have hh : horner ((e.rewire Fin.rev).eval x) w le_rfl=(bitsValue (e.eval x)).toNat := by
    rw [horner_full,Triangular.inputNumber_reverse]
    congr 2
    funext i
    simp [reverseBits,eval_rewire]
  rw [powOn,eval_comp,eval_pair,eval_pair,modularPower_value _ _ _ hm,hh]

lemma stripOn_value {k w : ℕ} (a m q v : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    (bitsValue ((stripOn a m q v).eval x)).toNat=stripPrimeNat
      (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
      (bitsValue (q.eval x)).toNat (bitsValue (v.eval x)).toNat := by
  have h1 : 1 < 2^w := lt_of_lt_of_le (by omega : 1 < (bitsValue (m.eval x)).toNat)
    (bitsValue (m.eval x)).isLt.le
  have hd : (bitsValue (((v.pair q).comp (div w)).eval x)).toNat=
      (bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat := by
    rw [eval_comp,eval_pair,div_word,BitVec.toNat_udiv]
  have hc : ((equalOn ((v.pair q).comp (mod w)) (wordConstant (BitVec.ofNat w 0))).band
      (equalOn (powOn a m ((v.pair q).comp (div w))) (wordConstant (BitVec.ofNat w 1)))).eval x 0=true ↔
      (bitsValue (v.eval x)).toNat%(bitsValue (q.eval x)).toNat=0 ∧
      (bitsValue (a.eval x)).toNat^((bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat)%
        (bitsValue (m.eval x)).toNat=1 := by
    rw [eval_band,Bool.and_eq_true,equalOn_value,equalOn_value,powOn_value _ _ _ _ hm,hd,
      eval_comp,eval_pair,mod_word,BitVec.toNat_umod,wordConstant_eval,wordConstant_eval,
      BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.zero_mod,Nat.mod_eq_of_lt h1]
  simp only [stripOn,wordMux_eval]
  split_ifs with hh
  · rw [hd,stripPrimeNat,ite_eq_left (hc.mp hh)]
  · rw [stripPrimeNat,ite_eq_right (fun h => hh (hc.mpr h))]

lemma stripUpdate_value {k w : ℕ} (a m q : BooleanNetwork k w) (x : Basis k) (z : Basis w)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    ∃ z', (stripUpdate a m q).eval (Fin.append x z)=Fin.append x z' ∧
      (bitsValue z').toNat=stripPrimeNat (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (bitsValue (q.eval x)).toNat (bitsValue z).toNat := by
  let v := stripOn (liftInput a (Fin.castAdd w)) (liftInput m (Fin.castAdd w))
      (liftInput q (Fin.castAdd w)) (select (Fin.natAdd k))
  have hx : Fin.append x z ∘ Fin.castAdd w=x := by funext i; exact Fin.append_left _ _ i
  have hz : Fin.append x z ∘ Fin.natAdd k=z := by funext i; exact Fin.append_right _ _ i
  refine ⟨v.eval (Fin.append x z),?_,?_⟩
  · simp only [stripUpdate,eval_pair,eval_select,hx]
    rfl
  · have hh := stripOn_value (liftInput a (Fin.castAdd w)) (liftInput m (Fin.castAdd w))
      (liftInput q (Fin.castAdd w)) (select (Fin.natAdd k)) (Fin.append x z)
      (by simpa only [liftInput_eval,hx] using hm)
    simpa only [liftInput_eval,eval_select,hx,hz] using hh

lemma stripScan_unit {k w m : ℕ} (hm : 2 ≤ m) (aN mN : BooleanNetwork k w)
    (u : (ZMod m)ˣ) (qs : List (BooleanNetwork k w)) (x : Basis k) (z : Basis w)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m) :
    ∃ z', (stripScan aN mN qs).eval (Fin.append x z)=Fin.append x z' ∧
      (bitsValue z').toNat=stripOrderFactors u (qs.map (fun q => (bitsValue (q.eval x)).toNat)) (bitsValue z).toNat := by
  induction qs generalizing z with
  | nil => exact ⟨z,by simp [stripScan],rfl⟩
  | cons q qs ih =>
    obtain ⟨z₁,hz₁,hv₁⟩ := stripUpdate_value aN mN q x z (by omega)
    obtain ⟨z₂,hz₂,hv₂⟩ := ih z₁
    refine ⟨z₂,?_,?_⟩
    · rw [stripScan,eval_comp,hz₁,hz₂]
    · rw [hv₂,hv₁,hmN,stripPrimeNat_unit hm u ha]
      rfl

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LabelRecoveryCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma pairChoice_eval {w : ℕ} (a b c d : Basis w) :
    (pairChoice w).eval (Fin.append (Fin.append a b) (Fin.append c d))=
      if (bitsValue a).toNat=0 then Fin.append c d else Fin.append a b := by
  rw [pairChoice,wordMux_eval]
  simp only [rootModulus_eval,rootGuess_eval]
  have he := equalOn_value
    ((rootModulus (w+w)).comp (rootModulus w))
    (wordConstant (n:=(w+w)+(w+w)) (BitVec.ofNat w 0))
    (Fin.append (Fin.append a b) (Fin.append c d))
  simp only [eval_comp,rootModulus_eval,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod] at he
  simp only [he]

lemma recoveryNet_value {n s w : ℕ} (Q B k : BooleanNetwork n w) (K : ℕ)
    (hw : cfWidth s K≤w) (x : Basis n)
    (hQ : (bitsValue (Q.eval x)).toNat<2^s) (hk : (bitsValue (k.eval x)).toNat<2^s) :
    ∃ d j : Basis w, (recoveryNet Q B k K).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=scanPairs
        (bitsValue (Q.eval x)).toNat (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat K := by
  induction K with
  | zero =>
    let z := (wordConstant (n:=n) (BitVec.ofNat w 0)).eval x
    refine ⟨z,z,?_,?_⟩
    · exact eval_pair _ _ x
    · simp [z,scanPairs,wordConstant_eval]
  | succ K ih =>
    have hwK : cfWidth s K≤w := by unfold cfWidth at *; nlinarith
    obtain ⟨c,d,hcd,hcdv⟩ := ih hwK
    obtain ⟨a,b,hab,habv⟩ := checkedConvergent_value K hwK Q B k x hQ hk
    have hs : (recoveryNet Q B k (K+1)).eval x=
        if (bitsValue a).toNat=0 then Fin.append c d else Fin.append a b := by
      rw [recoveryNet,eval_comp,eval_pair,hab,hcd,pairChoice_eval]
    have hv : (bitsValue a).toNat=(checkedPair (bitsValue (Q.eval x)).toNat
        (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat K).1 := congrArg Prod.fst habv
    by_cases ha : (bitsValue a).toNat=0
    · refine ⟨c,d,by rw [hs,ite_eq_left ha],?_⟩
      rw [scanPairs,ite_eq_right (by simpa [← hv] using ha),hcdv]
    · refine ⟨a,b,by rw [hs,ite_eq_right ha],?_⟩
      rw [scanPairs,ite_eq_left (by simpa [← hv] using ha)]
      exact habv

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderCandidateLaw
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

namespace OrderTrial

lemma labelEvent_pair {w s n d j : ℕ} (a m : Basis w) (x : Raw w s n)
    (h : labelEvent s n a m d j x) : labelPair s n x=(d,j) := by
  rcases h with h|h|h
  · rw [labelPair,ite_eq_left h.1]
    exact h.2.1.2
  · have hm := h.1
    rw [labelPair,ite_eq_right (by omega)]
    exact Prod.ext h.2.1 h.2.2.1
  · have hm := h.1
    rw [labelPair,ite_eq_right (by omega)]
    exact Prod.ext h.2.1 h.2.2.1

lemma trialResult_some {w s n d : ℕ} (a m : Basis w) (x : Raw w s n) :
    trialResult s n a m x=some d ↔ ∃ j,
      ValidLabel n (bitsValue a).toNat (bitsValue m).toNat d j ∧ labelEvent s n a m d j x := by
  classical
  unfold trialResult
  dsimp only
  split_ifs with h
  · constructor
    · intro hd
      have he := Option.some.inj hd
      exact ⟨(labelPair s n x).2,he ▸ h⟩
    · rintro ⟨j,hv,hl⟩
      rw [labelEvent_pair a m x hl]
  · constructor
    · intro hh; cases hh
    · rintro ⟨j,hv,hl⟩
      have he := labelEvent_pair a m x hl
      exact False.elim (h (by simpa only [he] using And.intro hv hl))

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness RepeatedTrials

lemma minOption_some_mem {a b : Option ℕ} {d : ℕ} (h : minOption a b=some d) :
    a=some d ∨ b=some d := by
  cases a with
  | none => exact Or.inr h
  | some a =>
    cases b with
    | none => exact Or.inl h
    | some b =>
      have he : min a b=d := Option.some.inj h
      by_cases hab : a≤b
      · exact Or.inl (congrArg some ((min_eq_left hab).symm.trans he))
      · exact Or.inr (congrArg some ((min_eq_right (by omega)).symm.trans he))

lemma minimumCandidate_mem {as : List (Option ℕ)} {d : ℕ} (h : minimumCandidate as=some d) :
    some d∈as := by
  induction as with
  | nil => cases h
  | cons a as ih =>
    rcases minOption_some_mem h with hd|hd
    · exact List.mem_cons.mpr (Or.inl hd.symm)
    · exact List.mem_cons.mpr (Or.inr (ih hd))

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveStatistics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

lemma recordPhi_factorization {m : ℕ} (hm : m≠0) : recordPhi m.factorization=m.totient := by
  rw [Nat.totient_eq_prod_factorization hm]
  apply Finset.prod_congr rfl
  intro p hp
  exact Nat.mul_comm _ _

lemma dataRecord_correct {M m : ℕ} (hM : 0 < M) (hd : m∣M) :
    dataRecord (trueData M) m = m.factorization := by
  have hh := dataDivisorPrimes_correct hM hd
  rw [dataRecord,primeRecord_eq_factorization _ hh.1,hh.2]

lemma dataPhi_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) :
    dataPhi (trueData M) m=m.totient := by
  rw [dataPhi,dataRecord_correct hM hd,recordPhi_factorization hm.ne']

lemma stripFactorsNat_unit {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (qs : List ℕ) (v : ℕ) :
    stripFactorsNat a m qs v=stripOrderFactors u qs v := by
  induction qs generalizing v with
  | nil => rfl
  | cons q qs ih => rw [stripFactorsNat,stripPrimeNat_unit hm u ha,ih]; rfl

/-- The retrospective order used for EVERY actual requested cofactor is the
true order, without calling an order oracle during execution. -/
lemma dataOrder_correct {M m a : ℕ} (hM : 0 < M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) :
    dataOrder (trueData M) a m=orderOf u := by
  have hh := dataTotientPrimes_correct hM (by omega : 0 < m) hd
  rw [dataOrder,dataPhi_correct hM (by omega) hd,stripFactorsNat_unit hm u ha]
  exact strip_totient_factors hm u _ hh.1 hh.2

lemma dataOrderSuccess_correct {M m a : ℕ} (hM : 0 < M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) (K : ℕ) :
    dataOrderSuccess (trueData M) a m K=Completion.orderSuccess (orderOf u) K := by
  rw [dataOrderSuccess,dataOrder_correct hM hm hd u ha]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveLists
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree OrderTrial

lemma basis_eq_natBasis {n a : ℕ} (ha : a<2^n) (x : Basis n) :
    (bitsValue x).toNat=a ↔ x=natBasis n a := by
  constructor
  · intro hx
    apply (bitsEquiv n).injective
    apply BitVec.eq_of_toNat_eq
    change (bitsValue x).toNat=(bitsValue (natBasis n a)).toNat
    rw [hx,natBasis_value,Nat.mod_eq_of_lt ha]
  · intro hx
    rw [hx,natBasis_value,Nat.mod_eq_of_lt ha]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletionPredicateCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion

lemma predicateFilter_value {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (coin : NatExpr v)
    (good guessGood : BooleanNetwork k 1) (x : Basis k) :
    (predicateFilter (W:=W) d s z vars branch coin good guessGood).eval x 0=true ↔
      ((bitsValue (branch.eval x)).toNat≠0 ∧ (good.eval x 0=true ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (coeff W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) ∨
      ((bitsValue (branch.eval x)).toNat=0 ∧ (guessGood.eval x 0=true ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (guessRetention W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) := by
  simp only [predicateFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    bnot_value,zeroWord_value,retentionNet_value,Expressions.coefficient_value,
    Expressions.guess_value]

/-- Exact same-history predicate semantics: this theorem does not supply or
assume an algorithm for either of the two input Boolean tests. -/
theorem predicateFilter_test {α v : Type*} {k b W t d : ℕ}
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (coin : NatExpr v)
    (good guessGood : BooleanNetwork k 1) (x : Basis k)
    (P : α→Prop) (Q : Basis W→Prop) (r : Raw α W t d) (S Z : ℚ)
    (hbranch : branch.eval x=r.1)
    (hcoin : coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=(bitsValue r.2.2.2).toNat)
    (hgood : good.eval x 0=true ↔ P r.2.1)
    (hguess : guessGood.eval x 0=true ↔ Q r.2.2.1)
    (hs : s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=S)
    (hz : z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=Z) :
    (predicateFilter (W:=W) d s z vars branch coin good guessGood).eval x 0=true ↔
      test P Q S Z r := by
  rw [predicateFilter_value,hbranch,hcoin,hgood,hguess,hs,hz]
  rfl
end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PreparedOracle
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

lemma packed_targetRegister {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y ∘ targetRegister n m r=y := by
  funext i
  exact packed_target x y i

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalCompletionOutput
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion

lemma rareWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (rareWires q W t d).eval (layout q W t d r)=r.1 := by
  funext i
  simp only [rareWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left]
lemma ordinaryWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (ordinaryWires q W t d).eval (layout q W t d r)=r.2.1 := by
  funext i
  simp only [ordinaryWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left,Fin.append_right]
lemma guessWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (guessWires q W t d).eval (layout q W t d r)=r.2.2.1 := by
  funext i
  simp only [guessWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left,Fin.append_right]
lemma retentionWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (retentionWires q W t d).eval (layout q W t d r)=r.2.2.2 := by
  funext i
  simp only [retentionWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_right]

lemma zeros_eval (k m : ℕ) (x : Basis k) : (zeros k m).eval x=fun _ => false := by
  funext i
  simp only [zeros,eval_vector,eval_constant]

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorWiring
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma tensorLayout_wire {q K : ℕ} (x : Fin K → Basis q) (i : Fin K) (j : Fin q) :
    tensorLayout q K x (tensorWire q K i j)=x i j := by
  induction K with
  | zero => exact Fin.elim0 i
  | succ K ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · change Fin.append (x 0) (tensorLayout q K (Fin.tail x)) (j.castAdd _) = _
      exact Fin.append_left _ _ _
    · change Fin.append (x 0) (tensorLayout q K (Fin.tail x))
        (Fin.natAdd q (tensorWire q K i j)) = _
      rw [Fin.append_right]
      exact ih (Fin.tail x) i

lemma tensorSelect_eval {q K : ℕ} (x : Fin K → Basis q) (i : Fin K) :
    (tensorSelect q K i).eval (tensorLayout q K x)=x i := by
  funext j
  exact tensorLayout_wire x i j
lemma tensorSelect_inverse {q K : ℕ} (x : Basis (tensorWidth q K)) (i : Fin K) :
    (tensorSelect q K i).eval x=(tensorLayout q K).symm x i := by
  obtain ⟨y,rfl⟩ := (tensorLayout q K).surjective x
  rw [tensorSelect_eval,Equiv.symm_apply_apply]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderNetworks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

lemma packed_append {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y=Fin.append (Fin.append x y) (fun _=>false) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · exact (packed_input x y j).trans (by simp)
    · exact (packed_target x y j).trans (by simp)
  · rw [packed_work x y _ (by simp),Fin.append_right]

namespace BooleanNetwork

lemma packNet_eval {k n m r : ℕ} (a : BooleanNetwork k n) (b : BooleanNetwork k m)
    (x : Basis k) : (packNet r a b).eval x=packed r (a.eval x) (b.eval x) := by
  rw [packNet,eval_pair,eval_pair,Completion.zeros_eval,packed_append]

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SamplerDecodeCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace BooleanNetwork

lemma leftNet_eval {u v : ℕ} (x : Basis u) (y : Basis v) :
    (leftNet u v).eval (Fin.append x y)=x := by
  funext i
  exact Fin.append_left x y i
lemma rightNet_eval {u v : ℕ} (x : Basis u) (y : Basis v) :
    (rightNet u v).eval (Fin.append x y)=y := by
  funext i
  exact Fin.append_right x y i
lemma equalOn_basis {k w : ℕ} (a b : BooleanNetwork k w) (x : Basis k) :
    (equalOn a b).eval x 0=true ↔ a.eval x=b.eval x := by
  rw [equalOn_value]
  constructor
  · intro h
    exact (bitsEquiv w).injective (BitVec.eq_of_toNat_eq h)
  · intro h; rw [h]

end BooleanNetwork
namespace OrderTrial

lemma sampleYNet_eval {u b : ℕ} (x : Basis (OrderSample.width u b)) :
    (sampleYNet u b).eval x=sampleY x := rfl
lemma sampleUNet_eval {u b : ℕ} (x : Basis (OrderSample.width u b)) :
    (sampleUNet u b).eval x=sampleU x := rfl

lemma triangularSelectedNet_eval {k b : ℕ} (y : BooleanNetwork k b) (x : Basis k) :
    (triangularSelectedNet y).eval x=Triangular.encode b (y.eval x,0) := by
  have h := (basisResidue b).symm_apply_eq.mpr (basisResidue_zero b).symm
  rw [triangularSelectedNet,packNet_eval,eval_pair,Completion.zeros_eval,Completion.zeros_eval]
  simp only [Triangular.encode,h]

lemma samplerSelectedNet_eval {k u b : ℕ} (a m : BooleanNetwork k u)
    (z : BooleanNetwork k (OrderSample.width u b)) (x : Basis k) :
    (samplerSelectedNet a m z).eval x 0=true ↔ SampleSelected (a.eval x) (m.eval x) (z.eval x) := by
  rw [samplerSelectedNet,equalOn_basis,packNet_eval,eval_pair,eval_pair,
    triangularSelectedNet_eval]
  simp only [eval_comp,sampleYNet_eval,sampleUNet_eval,SampleSelected,OrderSample.word,OrderSample.inputWord]

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MinimumCandidateCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma minNonzero_options (a b : Option ℕ)
    (ha : ∀ d, a=some d → 0<d) (hb : ∀ d, b=some d → 0<d) :
    minNonzero (a.getD 0) (b.getD 0)=(minOption a b).getD 0 := by
  cases a with
  | none => simp only [Option.getD_none,minNonzero,ite_true, if_true,minOption]
  | some a =>
    have hapos : a≠0 := (ha a rfl).ne'
    cases b with
    | none => simp only [Option.getD_none,Option.getD_some,minNonzero,ite_eq_right hapos,ite_true, if_true,minOption]
    | some b =>
      have hbpos : b≠0 := (hb b rfl).ne'
      simp only [Option.getD_some,minNonzero,ite_eq_right hapos,ite_eq_right hbpos,minOption]

lemma minimumChoice_value {w : ℕ} (a b : Basis w) :
    (bitsValue ((minimumChoice w).eval (Fin.append a b))).toNat=
      minNonzero (bitsValue a).toNat (bitsValue b).toNat := by
  have h₁ := equalOn_value (leftNet w w) (wordConstant (BitVec.ofNat w 0)) (Fin.append a b)
  have h₂ := equalOn_value (rightNet w w) (wordConstant (BitVec.ofNat w 0)) (Fin.append a b)
  simp only [leftNet_eval,rightNet_eval,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod] at h₁ h₂
  simp only [minimumChoice,wordMux_eval,leftNet_eval,rightNet_eval]
  simp only [h₁,h₂,wordLt_eval,leftNet_eval,rightNet_eval,decide_eq_true_eq]
  split_ifs with ha hb hab
  · simp only [minNonzero,ite_eq_left ha]
  · simp only [minNonzero,ite_eq_right ha,ite_eq_left hb]
  · simp only [minNonzero,ite_eq_right ha,ite_eq_right hb,min_eq_left hab.le]
  · simp only [minNonzero,ite_eq_right ha,ite_eq_right hb,min_eq_right (by omega : (bitsValue b).toNat≤(bitsValue a).toNat)]
lemma minimumNet_value {k w K : ℕ} (f : Fin K → BooleanNetwork k w) (x : Basis k)
    (g : Fin K → Option ℕ) (h : ∀ i,(bitsValue ((f i).eval x)).toNat=(g i).getD 0)
    (hp : ∀ i d,g i=some d→0<d) :
    (bitsValue ((minimumNet f).eval x)).toNat=(minimumCandidate (List.ofFn g)).getD 0 := by
  induction K with
  | zero => simp only [minimumNet,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod,
      List.ofFn_zero,minimumCandidate,Option.getD_none]
  | succ K ih =>
    rw [minimumNet,eval_comp,eval_pair,minimumChoice_value,h 0,
      ih (fun i=>f i.succ) (fun i=>g i.succ) (fun i=>h i.succ) (fun i=>hp i.succ),
      List.ofFn_succ,minimumCandidate]
    apply minNonzero_options _ _ (hp 0)
    intro d hd
    have hh := minimumCandidate_mem hd
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hh
    exact hp i.succ d hi

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RawTrialFields
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma rawMode_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawMode r).eval x=y.1 := by
  simp only [rawMode,eval_comp,h,rawLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval]
lemma rawSample_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawSample r).eval x=y.2.1 := by
  simp only [rawSample,eval_comp,h,rawLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval,rightNet_eval]
lemma rawGuesses_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawGuesses r).eval x=guessLayout n y.2.2 := by
  simp only [rawGuesses,eval_comp,h,rawLayout,productLayout_apply,Equiv.refl_apply,rightNet_eval]
lemma rawDen_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawDen r).eval x=y.2.2.1 := by
  rw [rawDen,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval]
lemma rawNum_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawNum r).eval x=y.2.2.2.1 := by
  rw [rawNum,eval_comp,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval,rightNet_eval]
lemma rawResidue_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawResidue r).eval x=y.2.2.2.2.1 := by
  rw [rawResidue,eval_comp,eval_comp,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,leftNet_eval,rightNet_eval]
lemma rawCoin_eval {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k)
    (y : Raw u s n) (h : r.eval x=rawLayout u s n y) : (rawCoin r).eval x=y.2.2.2.2.2 := by
  rw [rawCoin,eval_comp,eval_comp,eval_comp,rawGuesses_eval r x y h]
  simp only [guessLayout,productLayout_apply,Equiv.refl_apply,rightNet_eval]

lemma toWidth_value {k u w : ℕ} (a : BooleanNetwork k u) (h : u≤w) (x : Basis k) :
    (bitsValue ((toWidth w a).eval x)).toNat=(bitsValue (a.eval x)).toNat := by
  rw [toWidth,eval_comp,resizeWord_toNat h]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RawTrialLabelCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma recoveredPairNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    ∃ d j : Basis (decodeWidth u s n),
      (recoveredPairNet r).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=
        scanPairs (2^(s+2)) (2^n) (Triangular.outputNumber (sampleY y.2.1)) (decodeSteps s) := by
  have hw : cfWidth (s+3) (decodeSteps s)≤decodeWidth u s n := by unfold decodeWidth; omega
  have hs : s+2<decodeWidth u s n := by unfold decodeWidth; omega
  have hn : n<decodeWidth u s n := by unfold decodeWidth; omega
  have hQ : (bitsValue ((wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^(s+2)))).eval x)).toNat=2^(s+2) := by
    rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)]
  have hB : (bitsValue ((wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^n))).eval x)).toNat=2^n := by
    rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn)]
  have hy : (bitsValue ((toWidth (decodeWidth u s n) ((rawSample r).comp (sampleYNet u (s+2)))).eval x)).toNat =
      Triangular.outputNumber (sampleY y.2.1) := by
    rw [toWidth_value _ hs.le,eval_comp,rawSample_eval r x y h,sampleYNet_eval,bitsValue_toNat]
    rfl
  obtain ⟨d,j,hd,hv⟩ := recoveryNet_value
    (wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^(s+2))))
    (wordConstant (n:=k) (BitVec.ofNat (decodeWidth u s n) (2^n)))
    (toWidth (decodeWidth u s n) ((rawSample r).comp (sampleYNet u (s+2)))) (decodeSteps s) hw x
    (by rw [hQ]; exact Nat.pow_lt_pow_right (by decide) (by omega))
    (by rw [hy,Triangular.outputNumber,← bitsValue_toNat]
        exact (bitsValue (sampleY y.2.1)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  exact ⟨d,j,hd,by simpa only [hQ,hB,hy] using hv⟩

lemma trialPairNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    ∃ d j : Basis (decodeWidth u s n),
      (trialPairNet r).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=labelPair s n y := by
  have hw : 2≤decodeWidth u s n := by unfold decodeWidth; omega
  have hn : n≤decodeWidth u s n := by unfold decodeWidth; omega
  have h2 : 2<2^(decodeWidth u s n) := lt_of_lt_of_le (by decide : 2<2^2)
    (Nat.pow_le_pow_right (by decide) hw)
  have hm : (wordLt (toWidth (decodeWidth u s n) (rawMode r))
      (wordConstant (BitVec.ofNat (decodeWidth u s n) 2))).eval x 0=
      decide ((bitsValue y.1).toNat<2) := by
    rw [wordLt_eval,toWidth_value _ hw,rawMode_eval r x y h,wordConstant_eval,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2]
  by_cases ht : (bitsValue y.1).toNat<2
  · obtain ⟨d,j,hd,hv⟩ := recoveredPairNet_value r x y h
    refine ⟨d,j,?_,?_⟩
    · rw [trialPairNet,wordMux_eval,hm,ite_eq_left (by simpa only [decide_eq_true_eq] using ht),hd]
    · rw [labelPair,ite_eq_left ht]
      exact hv
  · refine ⟨(toWidth (decodeWidth u s n) (rawDen r)).eval x,
      (toWidth (decodeWidth u s n) (rawNum r)).eval x,?_,?_⟩
    · rw [trialPairNet,wordMux_eval,hm,ite_eq_right (by simpa only [decide_eq_true_eq] using ht),eval_pair]
    · rw [toWidth_value _ hn,toWidth_value _ hn,rawDen_eval r x y h,rawNum_eval r x y h,
        labelPair,ite_eq_right ht]

lemma trialDenNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    (bitsValue ((trialDenNet r).eval x)).toNat=(labelPair s n y).1 := by
  obtain ⟨d,j,hd,hv⟩ := trialPairNet_value r x y h
  rw [trialDenNet,eval_comp,hd,leftNet_eval]
  exact congrArg Prod.fst hv
lemma trialNumNet_value {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n))
    (x : Basis k) (y : Raw u s n) (h : r.eval x=rawLayout u s n y) :
    (bitsValue ((trialNumNet r).eval x)).toNat=(labelPair s n y).2 := by
  obtain ⟨d,j,hd,hv⟩ := trialPairNet_value r x y h
  rw [trialNumNet,eval_comp,hd,rightNet_eval]
  exact congrArg Prod.snd hv

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LabelValidationCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma labelValidNet_value {k w : ℕ} (n : ℕ) (a m d j : BooleanNetwork k w)
    (hn : n<w) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (labelValidNet n a m d j).eval x 0=true ↔
      ValidLabel n (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat := by
  have hp : 1<2^w := Nat.one_lt_two_pow (by omega)
  have hB : 2^n<2^w := Nat.pow_lt_pow_right (by decide) hn
  simp only [labelValidNet,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,
    equalOn_value,eval_comp,eval_pair,gcdNet_value,powOn_value a m d x hm,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hB,
    ValidLabel,Nat.Coprime]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialControlCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma firstRetNet_value {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) (x : Basis k)
    (hd : (bitsValue (d.eval x)).toNat≤2^n) (hp : 0<(bitsValue (d.eval x)).toNat) :
    (firstRetNet n d j t c).eval x 0=true ↔
      (bitsValue (c.eval x)).toNat<(Int.floor (firstRetention n
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat := by
  rw [firstRetNet,retentionNet_value,Expressions.firstE_value (fun i => (bitsValue ((decodeVars d j t c i).eval x)).toNat) n (.var .den) (.var .num) hd hp]
  rfl
lemma secondRetNet_value {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) (x : Basis k)
    (hd : (bitsValue (d.eval x)).toNat≤2^n) (hp : 0<(bitsValue (d.eval x)).toNat)
    (ht : (bitsValue (t.eval x)).toNat<(bitsValue (d.eval x)).toNat) :
    (secondRetNet n d j t c).eval x 0=true ↔
      (bitsValue (c.eval x)).toNat<(Int.floor (discrepancyRetention n
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat
          (bitsValue (t.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat := by
  rw [secondRetNet,retentionNet_value,Expressions.secondE_value (fun i => (bitsValue ((decodeVars d j t c i).eval x)).toNat) n (.var .den) (.var .num) (.var .residue) hd hp ht]
  rfl
lemma thirdRetNet_value {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) (x : Basis k)
    (hd : (bitsValue (d.eval x)).toNat≤2^n) (hp : 0<(bitsValue (d.eval x)).toNat) :
    (thirdRetNet n d j t c).eval x 0=true ↔
      (bitsValue (c.eval x)).toNat<(Int.floor (remainderRetention n
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat := by
  rw [thirdRetNet,retentionNet_value,Expressions.lastE_value (fun i => (bitsValue ((decodeVars d j t c i).eval x)).toNat) n (.var .den) (.var .num) hd hp]
  rfl

lemma trialAcceptOn_value {k w : ℕ} (n : ℕ) (a m mode d j t c : BooleanNetwork k w)
    (selected : BooleanNetwork k 1) (hn : n<w) (hw : 2≤w) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (trialAcceptOn n a m mode d j t c selected).eval x 0=true ↔
      ValidLabel n (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat ∧
      (((bitsValue (mode.eval x)).toNat<2 ∧ selected.eval x 0=true ∧
        (bitsValue (c.eval x)).toNat<(Int.floor (firstRetention n
          (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat) ∨
       ((bitsValue (mode.eval x)).toNat=2 ∧ (bitsValue (t.eval x)).toNat<(bitsValue (d.eval x)).toNat ∧
        (bitsValue (c.eval x)).toNat<(Int.floor (discrepancyRetention n
          (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat
            (bitsValue (t.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat) ∨
       ((bitsValue (mode.eval x)).toNat=3 ∧
        (bitsValue (c.eval x)).toNat<(Int.floor (remainderRetention n
          (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat)) := by
  have h2 : 2<2^w := lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) hw)
  have h3 : 3<2^w := lt_of_lt_of_le (by decide : 3<2^2) (Nat.pow_le_pow_right (by decide) hw)
  simp only [trialAcceptOn,eval_band,eval_bor,Bool.and_eq_true,Bool.or_eq_true,
    labelValidNet_value n a m d j hn x hm,wordLt_eval,decide_eq_true_eq,equalOn_value,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2,Nat.mod_eq_of_lt h3]
  apply and_congr_right
  intro hv
  rw [firstRetNet_value n d j t c x hv.2.1.le hv.1,
    thirdRetNet_value n d j t c x hv.2.1.le hv.1]
  by_cases ht : (bitsValue (t.eval x)).toNat<(bitsValue (d.eval x)).toNat
  · rw [secondRetNet_value n d j t c x hv.2.1.le hv.1 ht]
  · simp only [ht,false_and,and_false]

/-- At the actually recovered/guessed pair, pair equality checks simplify but
sampler scratch selection and the actual recorded retention coin do not. -/
lemma labelEvent_self {u s n : ℕ} (a m : Basis u) (r : Raw u s n) :
    labelEvent s n a m (labelPair s n r).1 (labelPair s n r).2 r ↔
      (((bitsValue r.1).toNat<2 ∧ SampleSelected a m r.2.1 ∧
        Retains (firstRetention n (labelPair s n r).1 (labelPair s n r).2) r.2.2.2.2.2) ∨
       ((bitsValue r.1).toNat=2 ∧ (bitsValue r.2.2.2.2.1).toNat<(labelPair s n r).1 ∧
        Retains (discrepancyRetention n (labelPair s n r).1 (labelPair s n r).2
          (bitsValue r.2.2.2.2.1).toNat) r.2.2.2.2.2) ∨
       ((bitsValue r.1).toNat=3 ∧
        Retains (remainderRetention n (labelPair s n r).1 (labelPair s n r).2) r.2.2.2.2.2)) := by
  by_cases h : (bitsValue r.1).toNat<2
  · have h2 : (bitsValue r.1).toNat≠2 := by omega
    have h3 : (bitsValue r.1).toNat≠3 := by omega
    simp only [labelEvent,modeFirst,modeSecond,modeThird,h,h2,h3,true_and,false_and,
      or_false,firstPass,recovered,labelPair,ite_true, if_true,Prod.mk.eta,and_true]
  · simp only [labelEvent,modeFirst,modeSecond,modeThird,h,false_and,false_or,
      labelPair,ite_false, if_false,secondPass,thirdPass,true_and]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RawTrialDecoder
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma rawAcceptNet_value {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k) (y : Raw u s n)
    (h : r.eval x=rawLayout u s n y) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (rawAcceptNet a m r).eval x 0=true ↔
      ValidLabel n (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (labelPair s n y).1 (labelPair s n y).2 ∧
      labelEvent s n (a.eval x) (m.eval x) (labelPair s n y).1 (labelPair s n y).2 y := by
  have hu : u≤decodeWidth u s n := by unfold decodeWidth; omega
  have hn : n<decodeWidth u s n := by unfold decodeWidth; omega
  have hw : 2≤decodeWidth u s n := by unfold decodeWidth; omega
  have hc : retentionBits n≤decodeWidth u s n := by unfold decodeWidth; omega
  have hm' : 2≤(bitsValue ((toWidth (decodeWidth u s n) m).eval x)).toNat := by
    rw [toWidth_value m hu]; exact hm
  rw [rawAcceptNet,trialAcceptOn_value _ _ _ _ _ _ _ _ _ hn hw x hm']
  simp only [toWidth_value a hu,toWidth_value m hu,toWidth_value (rawMode r) hw,
    toWidth_value (rawResidue r) hn.le,toWidth_value (rawCoin r) hc,
    trialDenNet_value r x y h,trialNumNet_value r x y h,
    rawMode_eval r x y h,rawResidue_eval r x y h,rawCoin_eval r x y h,
    samplerSelectedNet_eval,rawSample_eval r x y h]
  rw [labelEvent_self]
  rfl

lemma trialValueNet_value {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k) (y : Raw u s n)
    (h : r.eval x=rawLayout u s n y) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((trialValueNet a m r).eval x)).toNat=(trialResult s n (a.eval x) (m.eval x) y).getD 0 := by
  classical
  rw [trialValueNet,wordMux_eval]
  by_cases ht : (rawAcceptNet a m r).eval x 0=true
  · rw [ite_eq_left ht,trialDenNet_value r x y h]
    have hh := (rawAcceptNet_value a m r x y h hm).mp ht
    simp only [trialResult,ite_eq_left hh,Option.getD_some]
  · rw [ite_eq_right ht,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod]
    have hh := mt (rawAcceptNet_value a m r x y h hm).mpr ht
    simp only [trialResult,ite_eq_right hh,Option.getD_none]

lemma trialResult_getD_lt {u s n : ℕ} (a m : Basis u) (y : Raw u s n) :
    (trialResult s n a m y).getD 0<2^n := by
  classical
  unfold trialResult
  dsimp only
  split_ifs with h
  · exact h.1.2.1
  · change 0<2^n
    positivity

lemma trialSmallValueNet_value {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k) (y : Raw u s n)
    (h : r.eval x=rawLayout u s n y) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((trialSmallValueNet a m r).eval x)).toNat=(trialResult s n (a.eval x) (m.eval x) y).getD 0 := by
  rw [trialSmallValueNet,eval_comp,resizeWord_value,BitVec.toNat_setWidth,
    trialValueNet_value a m r x y h hm,Nat.mod_eq_of_lt (trialResult_getD_lt _ _ _)]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderDecoder
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial

lemma resizeWord_eq_natBasis {u w : ℕ} (x : Basis u) :
    (resizeWord u w).eval x=natBasis w (bitsValue x).toNat := by
  apply (bitsEquiv w).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue ((resizeWord u w).eval x)).toNat = (bitsValue (natBasis w (bitsValue x).toNat)).toNat
  rw [resizeWord_value,BitVec.toNat_setWidth,natBasis_value]

namespace OrderSlots

lemma usableOn_value {k n : ℕ} (a m : BooleanNetwork k n) (x : Basis k) (hn : 1≤n) :
    (usableOn a m).eval x 0=true ↔ Usable (a.eval x) (m.eval x) := by
  have h1 : 1<2^n := Nat.one_lt_two_pow (by omega)
  simp only [usableOn,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,equalOn_value,
    eval_comp,eval_pair,gcdNet_value,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,
    Usable,ZMod.isUnit_iff_coprime,Nat.Coprime]
lemma orderResultNet_value {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) (x : Basis k)
    (y : Fin (n^5)→Raw n (sampleExponent n) n) (h : raw.eval x=ordinaryLayout n y)
    (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((orderResultNet a m raw).eval x)).toNat=
      orderResult (sampleExponent n) n (a.eval x) (m.eval x) (n^5) y := by
  apply minimumNet_value _ x (fun i=>trialResult (sampleExponent n) n (a.eval x) (m.eval x) (y i))
  · intro i
    apply trialSmallValueNet_value _ _ _ x (y i) _ hm
    rw [eval_comp,h]
    exact tensorSelect_eval _ i
  · intro i d hd
    exact ((trialResult_some _ _ _).mp hd).choose_spec.1.1

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeMachine
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork RecordedHistory

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma current_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.currentNet t).eval (M.encoded x t h)=M.config x t h := by
  cases t with
  | zero=>rfl
  | succ t=>exact packed_targetRegister _ _

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeHistoryAccess
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma previousNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.previousNet t).eval (M.encoded x (t+1) (h,r))=M.encoded x t h := by
  rw [previousNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (NodeKernel.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) ∘
      firstRegister (M.width t) (NodeKernel.width n) M.initWork=_
  rw [packed_first,packed_first]
lemma lastNodeNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.lastNodeNet t).eval (M.encoded x (t+1) (h,r))=
      NodeKernel.encoding (M.query.eval (M.config x t h)) r := by
  rw [lastNodeNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (NodeKernel.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) ∘
      targetRegister (M.width t) (NodeKernel.width n) M.initWork=_
  rw [packed_first,packed_targetRegister]

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeVerifiedCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma rowQuery_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.rowQuery t).eval (M.encoded x (t+1) (h,r))=M.query.eval (M.config x t h) := by
  rw [rowQuery,eval_comp,eval_comp,M.previousNet_encoded,M.current_encoded]

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FlatLookupCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma logNets_values (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.logNets t).map (fun r=>((bitsValue (r.1.eval (M.encoded x t h))).toNat,
      SortedWords.numbers (List.ofFn (fun i=>(tensorLayout n n).symm
        (r.2.eval (M.encoded x t h)) i))))=M.dataLog x t h := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    change (_::List.map _ (List.map _ (M.logNets t)))=_
    simp only [List.map_map,Function.comp_def,eval_comp,M.previousNet_encoded,
      M.lastNodeNet_encoded,M.rowQuery_encoded]
    rw [ih]
    simp only [dataLog,PhysicalTree.nodeWords,PhysicalTree.resultFields,eval_comp,
      tensorSelect_inverse]
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FlatVerifiedData
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree
namespace PhysicalTree

lemma lookupFields_correct {rows : List (ℕ×List ℕ)} {n N m : ℕ}
    (h : CompleteLog n N rows) (hm : m∈rows.map Prod.fst) (hpos : m≠0) :
    CorrectEncoding m n (lookupFields rows m) := by
  cases hf : rows.find? (fun r=>decide (r.1=m)) with
  | none=>
    obtain ⟨r,hr,he⟩:=List.mem_map.mp hm
    have hh:=List.find?_eq_none.mp hf r hr
    simp only [he,decide_true] at hh
    contradiction
  | some r=>
    have hr:=List.mem_of_find?_eq_some hf
    have he : r.1=m := by simpa only [decide_eq_true_eq] using List.find?_some hf
    have hv:=h.2.1 r hr
    rcases hv with hz | hv
    · exact (hpos (he.symm.trans hz)).elim
    · simpa only [lookupFields,hf,he] using hv

lemma encoding_filter {n m : ℕ} {xs : List ℕ} (h : CorrectEncoding m n xs) :
    (∀ p∈xs.filter (fun p=>decide (p≠0)),p.Prime) ∧
      (xs.filter (fun p=>decide (p≠0))).prod=m := by
  obtain ⟨ps,hp,_hs,hprod,_hlen,rfl⟩:=h
  have he : (ps++List.replicate (n-ps.length) 0).filter (fun p=>decide (p≠0))=ps := by
    rw [List.filter_append]
    have hx : ps.filter (fun p=>decide (p≠0))=ps :=
      List.filter_eq_self.mpr (by intro p h; simpa only [decide_eq_true_eq] using (hp p h).ne_zero)
    rw [hx]
    simp
  rw [he]
  exact ⟨hp,hprod⟩

lemma lookupPrimes_correct {rows : List (ℕ×List ℕ)} {n N m : ℕ}
    (h : CompleteLog n N rows) (hm : m∈rows.map Prod.fst) (hpos : m≠0) :
    (∀ p∈lookupPrimes rows m,p.Prime) ∧ (lookupPrimes rows m).prod=m :=
  encoding_filter (lookupFields_correct h hm hpos)

lemma logDivisorPrimes_correct {rows : List (ℕ×List ℕ)} {n N M m : ℕ}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hpos : M≠0) (hd : m∣M) :
    (∀ p∈logDivisorPrimes rows M m,p.Prime) ∧ (logDivisorPrimes rows M m).prod=m := by
  obtain ⟨hp,hprod⟩:=lookupPrimes_correct h hM hpos
  exact ⟨divisorPrimes_prime m _ hp,divisorPrimes_prod _ hp (by rwa [hprod])⟩

lemma log_child_present {rows : List (ℕ×List ℕ)} {n N M d : ℕ}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hd : d∈children M) :
    d∈rows.map Prod.fst := by
  obtain ⟨r,hr,he⟩:=List.mem_map.mp hM
  exact h.2.2 r hr d (by rwa [he])

lemma logTotientPrimes_correct {rows : List (ℕ×List ℕ)} {n N M m : ℕ}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hpos : M≠0)
    (hm : 0 < m) (hd : m∣M) :
    (∀ p∈logTotientPrimes rows M m,p.Prime) ∧ (logTotientPrimes rows M m).prod=m.totient := by
  obtain ⟨hp,hprod⟩:=logDivisorPrimes_correct h hM hpos hd
  have hf : primeRecord (logDivisorPrimes rows M m)=m.factorization := by
    rw [primeRecord_eq_factorization _ hp,hprod]
  have hc (p : ℕ) (hp : p∈m.factorization.support) (h2 : p≠2) :
      (∀ q∈lookupPrimes rows (p-1),q.Prime) ∧ (lookupPrimes rows (p-1)).prod=p-1 := by
    have hpm:=Nat.mem_primeFactors.mp hp
    have hb : 2<p := by have := hpm.1.two_le; omega
    have hchild : p-1∈children M :=
      mem_children.mpr ⟨p,hpm.1,hpm.2.1.trans hd,hpos,hb,rfl⟩
    exact lookupPrimes_correct h (log_child_present h hM hchild) (by omega)
  rw [logTotientPrimes,hf]
  refine ⟨?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,hp⟩:=List.mem_flatMap.mp hp
    have hq':=(Finset.mem_sort (·≤·)).mp hq
    rcases List.mem_append.mp hp with hp | hp
    · have he:=(List.mem_replicate.mp hp).2
      subst p
      exact Nat.prime_of_mem_primeFactors hq'
    · split_ifs at hp with h2
      · simp at hp
      · exact (hc q hq' h2).1 p hp
  · rw [prod_flatMap]
    calc
      _ = ((m.factorization.support.sort (·≤·)).map
          (fun p=>p^(m.factorization p-1)*(p-1))).prod := by
        congr 1
        apply List.map_congr_left
        intro p hp
        rw [List.prod_append,List.prod_replicate]
        split_ifs with h2
        · subst p; simp
        · rw [(hc p ((Finset.mem_sort (·≤·)).mp hp) h2).2]
      _ = m.factorization.prod (fun p e=>p^(e-1)*(p-1)) := by
        rw [←List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
        rfl
      _ = m.totient := (Nat.totient_eq_prod_factorization hm.ne').symm

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalPowerCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
namespace RatExpr
variable {v : Type*}

lemma repeatedSuccess_value (x : v→ℕ) (a : RatExpr v) (K : ℕ) :
    (a.repeatedSuccess K).eval x=1-(1-a.eval x)^K := by
  simp only [repeatedSuccess,eval_sub,eval_const,eval_signedPower]

end RatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableOrder
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

lemma divisorPrimes_subset (m : ℕ) (ps : List ℕ) : divisorPrimes m ps ⊆ ps := by
  induction ps generalizing m with
  | nil=>simp [divisorPrimes]
  | cons p ps ih=>
    intro q hq
    rw [divisorPrimes] at hq
    split_ifs at hq
    · rcases List.mem_cons.mp hq with rfl|hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ hq)
    · exact List.mem_cons_of_mem _ (ih _ hq)

lemma primeRecord_support_subset (ps : List ℕ) : ∀ p∈(primeRecord ps).support,p∈ps := by
  induction ps with
  | nil=>simp [primeRecord]
  | cons q qs ih=>
    intro p hp
    have hp':=(Finsupp.mem_support_iff).mp hp
    by_cases he : p=q
    · subst p; exact List.mem_cons_self
    · have htail : (primeRecord qs) p≠0 := by
        simpa only [primeRecord,Finsupp.add_apply,Finsupp.single_eq_of_ne he,zero_add] using hp'
      exact List.mem_cons_of_mem _ (ih p (Finsupp.mem_support_iff.mpr htail))

namespace PhysicalTree

lemma tableFactors_prime {n N : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) : ∀ p∈tableFactors rows,p.Prime := by
  intro p hp
  obtain ⟨r,hr,hp⟩:=List.mem_flatMap.mp hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  split_ifs with hz
  · exact Nat.prime_two
  · have hr0 : r.1≠0 := fun he=>hz (Or.inl he)
    have hq0 : q≠0 := fun he=>hz (Or.inr he)
    have hv:=(h.2.1 r hr).resolve_left hr0
    exact (encoding_filter hv).1 q (List.mem_filter.mpr ⟨hq,by simpa using hq0⟩)

lemma lookupPrimes_subset_table {rows : List (ℕ×List ℕ)} {M : ℕ} (hM : M≠0) :
    lookupPrimes rows M ⊆ tableFactors rows := by
  intro p hp
  obtain ⟨hp,hp0⟩:=List.mem_filter.mp hp
  have hp0 : p≠0 := by simpa only [decide_eq_true_eq] using hp0
  cases hf : rows.find? (fun r=>decide (r.1=M)) with
  | none=>simp only [lookupFields,hf,List.not_mem_nil] at hp
  | some r=>
    have hr:=List.mem_of_find?_eq_some hf
    have he : r.1=M := by simpa only [decide_eq_true_eq] using List.find?_some hf
    have hpr : p∈r.2 := by simpa only [lookupFields,hf] using hp
    apply List.mem_flatMap.mpr
    refine ⟨r,hr,List.mem_map.mpr ⟨p,hpr,?_⟩⟩
    rw [ite_eq_right (by simp only [he,hM,hp0,or_self,not_false_eq_true])]

lemma logTotientPrimes_subset_table {n N M m : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0) (_hd : m∣M) :
    logTotientPrimes rows M m ⊆ tableFactors rows := by
  intro p hp
  obtain ⟨q,hq,hp⟩:=List.mem_flatMap.mp hp
  have hq' := primeRecord_support_subset (logDivisorPrimes rows M m) q
    ((Finset.mem_sort (·≤·)).mp hq)
  have hqparent : q∈lookupPrimes rows M := divisorPrimes_subset m _ hq'
  have hqprime := (lookupPrimes_correct h hM hM0).1 q hqparent
  rcases List.mem_append.mp hp with hp|hp
  · have he:=(List.mem_replicate.mp hp).2
    subst p
    exact lookupPrimes_subset_table hM0 hqparent
  · split_ifs at hp with h2
    · simp at hp
    · exact lookupPrimes_subset_table (by have:=hqprime.two_le; omega) hp

/-- A support-covering list gives a known multiple after n repetitions,
because every prime exponent of an n-bit positive integer is at most n. -/
lemma dvd_cover_power {v n : ℕ} (ps : List ℕ) (hv : v≠0) (hb : v≤2^n)
    (hp : ∀ p∈ps,p.Prime) (hcover : ∀ p : ℕ,p.Prime→p∣v→p∈ps) : v∣ps.prod^n := by
  have hprod : ps.prod≠0 := List.prod_ne_zero (by intro h;exact (hp 0 h).ne_zero rfl)
  apply (Nat.factorization_prime_le_iff_dvd hv (pow_ne_zero _ hprod)).mp
  intro p hprime
  by_cases hd : p∣v
  · have hm:=hcover p hprime hd
    have hpd : p∣ps.prod := List.dvd_prod hm
    have hpos : 1≤ps.prod.factorization p := (hprime.factorization_pos_of_dvd hprod hpd)
    have he : v.factorization p≤n := Nat.factorization_le_of_le_pow
      (hb.trans (Nat.pow_le_pow_left hprime.two_le n))
    rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
    exact he.trans (by nlinarith)
  · rw [Nat.factorization_eq_zero_of_not_dvd hd]
    exact Nat.zero_le _

/-- A rectangular verified data table is sufficient to recover the same
literal multiplicative order. No unbounded support extraction is required. -/
theorem table_strip_order {n N M m : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hb : m<2^n) (hd : m∣M) (a : (ZMod m)ˣ) :
    stripOrderFactors a (List.flatten (List.replicate n (tableFactors rows)))
      ((tableFactors rows).prod^n)=orderOf a := by
  let : NeZero m := ⟨by omega⟩
  have hc:=logTotientPrimes_correct h hM hM0 (by omega : 0 < m) hd
  have hcover : ∀ p : ℕ,p.Prime→p∣m.totient→p∈tableFactors rows := by
    intro p hp hpd
    have mem : p∈logTotientPrimes rows M m := by
      have hpd' : p∣(logTotientPrimes rows M m).prod := by rwa [hc.2]
      obtain ⟨q,hq,hpq⟩:=(Nat.prime_iff.mp hp).dvd_prod_iff.mp hpd'
      have he:=((hc.1 q hq).eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one
      simpa only [he] using hq
    exact logTotientPrimes_subset_table h hM hM0 hd mem
  have hphi : m.totient∣(tableFactors rows).prod^n := dvd_cover_power _
    (Nat.totient_pos.mpr (by omega : 0 < m)).ne'
    ((Nat.totient_le m).trans hb.le) (tableFactors_prime h) hcover
  have horder : orderOf a∣m.totient := by
    simpa [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using orderOf_dvd_natCard a
  have hmul := Nat.mul_div_cancel' (horder.trans hphi)
  rw [←hmul]
  apply stripOrderFactors_exact a (orderOf_pos a)
  · intro p hp
    obtain ⟨xs,hxs,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hxs).2
    subst xs
    exact tableFactors_prime h p hp
  · have he : (List.flatten (List.replicate n (tableFactors rows))).prod=
        (tableFactors rows).prod^n := by
      rw [List.prod_flatten,List.map_replicate,List.prod_replicate]
    rw [he]
    exact Nat.div_dvd_of_dvd (horder.trans hphi)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableOrderCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

lemma tableFactor_value {k n : ℕ} (hn : 2≤n) (label p : BooleanNetwork k n) (x : Basis k) :
    (bitsValue ((tableFactor label p).eval x)).toNat=
      if (bitsValue (label.eval x)).toNat=0 ∨ (bitsValue (p.eval x)).toNat=0 then 2
      else (bitsValue (p.eval x)).toNat := by
  have hb : 2<2^n := lt_of_lt_of_le (by norm_num : 2<2^2) (Nat.pow_le_pow_right (by norm_num) hn)
  have hh : ((zeroWord label).bor (zeroWord p)).eval x 0=true ↔
      (bitsValue (label.eval x)).toNat=0 ∨ (bitsValue (p.eval x)).toNat=0 := by
    rw [eval_bor,Bool.or_eq_true,zeroWord_value,zeroWord_value]
  rw [tableFactor,wordMux_eval]
  by_cases h : ((zeroWord label).bor (zeroWord p)).eval x 0=true
  · rw [ite_eq_left h,ite_eq_left (hh.mp h),wordConstant_eval]
    exact Nat.mod_eq_of_lt hb
  · rw [ite_eq_right h,ite_eq_right (fun h' => h (hh.mpr h'))]

lemma tableNets_values {k n : ℕ} (hn : 2≤n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    (tableNets rows).map (fun p=>(bitsValue (p.eval x)).toNat)=
      PhysicalTree.tableFactors (tableValues rows x) := by
  simp only [tableNets,tableValues,PhysicalTree.tableFactors,List.map_flatMap,List.flatMap_map,
    List.map_map,Function.comp_def,tableFactor_value hn]

lemma orderFromList_unit {k w m : ℕ} (hm : 2 ≤ m) (aN mN : BooleanNetwork k w)
    (u : (ZMod m)ˣ) (qs : List (BooleanNetwork k w)) (x : Basis k)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m)
    (hb : (qs.map (fun q=>(bitsValue (q.eval x)).toNat)).prod<2^w) :
    (bitsValue ((orderFromList aN mN qs).eval x)).toNat=
      stripOrderFactors u (qs.map (fun q=>(bitsValue (q.eval x)).toNat))
        ((qs.map (fun q=>(bitsValue (q.eval x)).toNat)).prod) := by
  obtain ⟨z,he,hv⟩:=stripScan_unit hm aN mN u qs x ((productNet qs).eval x) ha hmN
  have hz : Fin.append x z ∘ Fin.natAdd k=z := by funext i;exact Fin.append_right _ _ i
  rw [orderFromList,eval_comp,eval_comp,eval_pair,eval_select]
  change (bitsValue ((select (Fin.natAdd k)).eval ((stripScan aN mN qs).eval
    (Fin.append x ((productNet qs).eval x))))).toNat=_
  rw [he,eval_select,hz,hv,productNet_nat,Nat.mod_eq_of_lt hb]

/-- A uniform polynomial-width exact product bound. -/
lemma word_list_product_bound {k w n : ℕ} (qs : List (BooleanNetwork k w)) (x : Basis k)
    (h : ∀ q∈qs,(bitsValue (q.eval x)).toNat≤2^n) :
    (qs.map (fun q=>(bitsValue (q.eval x)).toNat)).prod<2^(n*qs.length+1) := by
  have hb:=List.prod_le_pow_card (qs.map (fun q=>(bitsValue (q.eval x)).toNat)) (2^n)
    (by intro p hp;obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp;exact h q hq)
  rw [List.length_map,←pow_mul] at hb
  exact hb.trans_lt (Nat.pow_lt_pow_right (by omega : 1<2) (by omega))

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_VerifiedTableOrder
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

lemma tableOrderPrimes_values {k n : ℕ} (hn : 2 ≤ n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    (tableOrderPrimes rows).map (fun p=>(bitsValue (p.eval x)).toNat)=
      List.flatten (List.replicate n (PhysicalTree.tableFactors (tableValues rows x))) := by
  have hw : n ≤ tableOrderWidth n (tableNets rows).length := by
    dsimp only [tableOrderWidth]
    omega
  simp only [tableOrderPrimes,List.map_flatten,List.map_replicate,List.map_map,
    Function.comp_def,eval_comp,resizeWord_toNat hw]
  rw [tableNets_values hn]

lemma tableOrderPrimes_length {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    (tableOrderPrimes rows).length=n*(tableNets rows).length := by
  simp only [tableOrderPrimes,List.length_flatten,List.map_replicate,List.length_map,
    List.sum_replicate,smul_eq_mul]

lemma tableOrderPrimes_product_bound {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    ((tableOrderPrimes rows).map (fun p=>(bitsValue (p.eval x)).toNat)).prod < 2^(tableOrderWidth n (tableNets rows).length) := by
  have h : ∀ p∈tableOrderPrimes rows,(bitsValue (p.eval x)).toNat ≤ 2^n := by
    intro p hp
    obtain ⟨ps,hps,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hps).2
    subst ps
    obtain ⟨r,_hr,rfl⟩:=List.mem_map.mp hp
    rw [eval_comp,resizeWord_toNat (by dsimp [tableOrderWidth];omega)]
    exact (bitsValue (r.eval x)).isLt.le
  have hb:=word_list_product_bound (tableOrderPrimes rows) x h
  rw [tableOrderPrimes_length] at hb
  exact hb.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by dsimp [tableOrderWidth];omega))

theorem tableOrder_exact {k n N M m : ℕ} (hn : 2 ≤ n)
    (aN mN : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k)
    (h : PhysicalTree.CompleteLog n N (tableValues rows x))
    (hM : M∈(tableValues rows x).map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hd : m∣M) (u : (ZMod m)ˣ)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m) :
    (bitsValue ((tableOrder aN mN rows).eval x)).toNat=orderOf u := by
  let w:=tableOrderWidth n (tableNets rows).length
  have hwide : n ≤ w := by dsimp [w,tableOrderWidth];omega
  have hv:=orderFromList_unit hm (aN.comp (resizeWord n w)) (mN.comp (resizeWord n w))
    u (tableOrderPrimes rows) x
    (by simpa only [eval_comp,resizeWord_toNat hwide] using ha)
    (by simpa only [eval_comp,resizeWord_toNat hwide] using hmN)
    (tableOrderPrimes_product_bound rows x)
  rw [tableOrderPrimes_values hn] at hv
  have hb : m < 2^n := by rw [←hmN];exact (bitsValue (mN.eval x)).isLt
  have hs:=PhysicalTree.table_strip_order h hM hM0 hm hb hd u
  rw [List.prod_flatten,List.map_replicate,List.prod_replicate,hs] at hv
  have hord : orderOf u < 2^n := by
    let : NeZero m:=⟨by omega⟩
    have hh : orderOf u ≤ m.totient := by
      simpa only [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using (orderOf_le_card (x := u))
    exact (hh.trans (Nat.totient_le m)).trans_lt hb
  rw [tableOrder,eval_comp,resizeWord_value,BitVec.toNat_setWidth,hv,Nat.mod_eq_of_lt hord]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma fieldRows_values (x : Basis c) (t : ℕ) (h : Trace n t) :
    tableValues (M.fieldRows t) (M.encoded x t h)=M.dataLog x t h := by
  rw [←M.logNets_values x t h]
  simp only [fieldRows,tableValues,List.map_map,Function.comp_def,List.map_ofFn,
    eval_comp,tensorSelect_inverse,SortedWords.numbers,List.map_ofFn]

lemma retainedOrder_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedOrder t a m).eval (M.encoded x t r))).toNat=orderOf u := by
  apply tableOrder_exact hn a m (M.fieldRows t) (M.encoded x t r)
  · rwa [M.fieldRows_values]
  · rwa [M.fieldRows_values]
  · exact hP0
  · exact hd
  · exact hdiv
  · exact ha
  · exact hm

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableTotient
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma totientScan_exact (ps : List ℕ) (v : ℕ) (hv : 0 < v)
    (hp : ∀ p∈ps,p.Prime) (hd : v ∣ ps.prod) : totientScan ps v=v.totient := by
  induction ps generalizing v with
  | nil=>
    have he : v=1 := Nat.eq_one_of_dvd_one hd
    subst v
    simp [totientScan]
  | cons p ps ih=>
    have hprime:=hp p (List.mem_cons_self)
    have hps : ∀ q∈ps,q.Prime := fun q hq=>hp q (List.mem_cons_of_mem _ hq)
    rw [List.prod_cons] at hd
    rw [totientScan]
    by_cases hdv : p ∣ v
    · rw [ite_eq_left hdv]
      have he : p*(v/p)=v := Nat.mul_div_cancel' hdv
      have hd' : v/p ∣ ps.prod := by
        apply (Nat.mul_dvd_mul_iff_left hprime.pos).mp
        rwa [he]
      have hv' : 0 < v/p := by
        exact Nat.div_pos (Nat.le_of_dvd hv hdv) hprime.pos
      rw [ih (v/p) hv' hps hd']
      conv_rhs => rw [←he]
      by_cases hpp : p ∣ v/p
      · rw [ite_eq_left hpp,Nat.totient_mul_of_prime_of_dvd hprime hpp]
      · rw [ite_eq_right hpp,Nat.totient_mul_of_prime_of_not_dvd hprime hpp]
    · rw [ite_eq_right hdv]
      apply ih v hv hps
      exact (hprime.coprime_iff_not_dvd.mpr hdv).symm.dvd_of_dvd_mul_left hd

namespace PhysicalTree
/-- The same rectangular table which suffices for order stripping supplies
Euler's totient of every positive divisor of the group exponent. -/
theorem table_totient_exact {n N M m d : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hb : m < 2^n) (hd : m∣M) (hd0 : 0 < d) (hdt : d∣m.totient) :
    totientScan (List.flatten (List.replicate n (tableFactors rows))) d=d.totient := by
  have hc:=logTotientPrimes_correct h hM hM0 (by omega : 0 < m) hd
  have hcover : ∀ p : ℕ,p.Prime→p∣m.totient→p∈tableFactors rows := by
    intro p hp hpd
    have mem : p∈logTotientPrimes rows M m := by
      have hpd' : p∣(logTotientPrimes rows M m).prod := by rwa [hc.2]
      obtain ⟨q,hq,hpq⟩:=(Nat.prime_iff.mp hp).dvd_prod_iff.mp hpd'
      have he:=((hc.1 q hq).eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one
      simpa only [he] using hq
    exact logTotientPrimes_subset_table h hM hM0 hd mem
  have hphi : m.totient∣(tableFactors rows).prod^n := dvd_cover_power _
    (Nat.totient_pos.mpr (by omega : 0 < m)).ne'
    ((Nat.totient_le m).trans hb.le) (tableFactors_prime h) hcover
  apply totientScan_exact _ d hd0
  · intro p hp
    obtain ⟨xs,hxs,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hxs).2
    subst xs
    exact tableFactors_prime h p hp
  · rw [List.prod_flatten,List.map_replicate,List.prod_replicate]
    exact hdt.trans hphi
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TotientAccumulator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma totientFoldNat_score (B : ℕ) (ps : List ℕ) (s : ℕ×ℕ) (hs : s.2 < B) :
    (totientFoldNat B ps s).2=(s.2*totientScan ps s.1)%B := by
  induction ps generalizing s with
  | nil=>simp only [totientFoldNat,totientScan,mul_one,Nat.mod_eq_of_lt hs]
  | cons p ps ih=>
    rw [totientFoldNat,ih (totientStepNat B p s) (by
      unfold totientStepNat
      split
      · exact Nat.mod_lt _ (Nat.zero_lt_of_lt hs)
      · exact hs)]
    rw [totientScan]
    unfold totientStepNat
    split_ifs with hd hp
    · simp only [Nat.mod_mul_mod,mul_assoc]
    · simp only [Nat.mod_mul_mod,mul_assoc]
    · rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TotientCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

lemma totientPair_value {k w : ℕ} (hw : 0 < w) (q v a : BooleanNetwork k w) (x : Basis k) :
    let y := (totientPair q v a).eval x
    ((bitsValue (y ∘ Fin.castAdd w)).toNat,(bitsValue (y ∘ Fin.natAdd w)).toNat)=
      totientStepNat (2^w) (bitsValue (q.eval x)).toNat
        ((bitsValue (v.eval x)).toNat,(bitsValue (a.eval x)).toNat) := by
  have h1 : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  let d := (v.pair q).comp (div w)
  let cond := zeroWord ((v.pair q).comp (mod w))
  let weight := wordMux (zeroWord ((d.pair q).comp (mod w))) q
    (natSubOn q (wordConstant (BitVec.ofNat w 1)))
  have hd : (bitsValue (d.eval x)).toNat=(bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat := by
    rw [show d=(v.pair q).comp (div w) from rfl,eval_comp,eval_pair,div_word,BitVec.toNat_udiv]
  have hc : cond.eval x 0=true ↔ (bitsValue (q.eval x)).toNat ∣ (bitsValue (v.eval x)).toNat := by
    rw [show cond=zeroWord ((v.pair q).comp (mod w)) from rfl,zeroWord_value,
      eval_comp,eval_pair,mod_word,BitVec.toNat_umod,Nat.dvd_iff_mod_eq_zero]
  have hweight : (bitsValue (weight.eval x)).toNat=
      if (bitsValue (q.eval x)).toNat ∣ (bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat
      then (bitsValue (q.eval x)).toNat else (bitsValue (q.eval x)).toNat-1 := by
    have hh : (zeroWord ((d.pair q).comp (mod w))).eval x 0=true ↔
        (bitsValue (q.eval x)).toNat ∣ (bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat := by
      rw [zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,hd,Nat.dvd_iff_mod_eq_zero]
    rw [show weight=wordMux (zeroWord ((d.pair q).comp (mod w))) q
      (natSubOn q (wordConstant (BitVec.ofNat w 1))) from rfl,wordMux_eval]
    by_cases he : (zeroWord ((d.pair q).comp (mod w))).eval x 0=true
    · rw [ite_eq_left he,ite_eq_left (hh.mp he)]
    · rw [ite_eq_right he,ite_eq_right (fun h=>he (hh.mpr h)),natSubOn_value,wordConstant_eval,
        BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  dsimp only
  rw [totientPair,eval_pair]
  change ((bitsValue ((Fin.append ((wordMux cond d v).eval x)
      ((wordMux cond ((a.pair weight).comp (mul w)) a).eval x)) ∘ Fin.castAdd w)).toNat,
    (bitsValue ((Fin.append ((wordMux cond d v).eval x)
      ((wordMux cond ((a.pair weight).comp (mul w)) a).eval x)) ∘ Fin.natAdd w)).toNat)=_
  have hl (l r : Basis w) : Fin.append l r ∘ Fin.castAdd w=l := by
    funext i; exact Fin.append_left _ _ i
  have hr (l r : Basis w) : Fin.append l r ∘ Fin.natAdd w=r := by
    funext i; exact Fin.append_right _ _ i
  rw [hl,hr,wordMux_eval,wordMux_eval,totientStepNat]
  by_cases he : cond.eval x 0=true
  · rw [ite_eq_left he,ite_eq_left he,ite_eq_left (hc.mp he),hd,eval_comp,eval_pair,mul_word,
      BitVec.toNat_mul,hweight]
  · rw [ite_eq_right he,ite_eq_right he,ite_eq_right (fun h=>he (hc.mpr h))]

lemma totientUpdate_value {k w : ℕ} (hw : 0 < w) (q : BooleanNetwork k w)
    (x : Basis k) (s : Basis (w+w)) :
    ∃ s', (totientUpdate q).eval (Fin.append x s)=Fin.append x s' ∧
      ((bitsValue (s' ∘ Fin.castAdd w)).toNat,(bitsValue (s' ∘ Fin.natAdd w)).toNat)=
        totientStepNat (2^w) (bitsValue (q.eval x)).toNat
          ((bitsValue (s ∘ Fin.castAdd w)).toNat,(bitsValue (s ∘ Fin.natAdd w)).toNat) := by
  have hx : Fin.append x s ∘ Fin.castAdd (w+w)=x := by funext i;exact Fin.append_left _ _ i
  let Q:=liftInput q (Fin.castAdd (w+w))
  let V : BooleanNetwork (k+(w+w)) w:=select (fun i=>Fin.natAdd k (Fin.castAdd w i))
  let A : BooleanNetwork (k+(w+w)) w:=select (fun i=>Fin.natAdd k (Fin.natAdd w i))
  have hq : Q.eval (Fin.append x s)=q.eval x := by simp only [Q,liftInput_eval,hx]
  have hv : V.eval (Fin.append x s)=s ∘ Fin.castAdd w := by
    funext i; exact Fin.append_right _ _ _
  have ha : A.eval (Fin.append x s)=s ∘ Fin.natAdd w := by
    funext i; exact Fin.append_right _ _ _
  refine ⟨(totientPair Q V A).eval (Fin.append x s),?_,?_⟩
  · simp only [totientUpdate,eval_pair,eval_select,hx]
    rfl
  · simpa only [hq,hv,ha] using totientPair_value hw Q V A (Fin.append x s)

lemma totientScanNet_value {k w : ℕ} (hw : 0 < w) (qs : List (BooleanNetwork k w))
    (x : Basis k) (s : Basis (w+w)) :
    ∃ s', (totientScanNet qs).eval (Fin.append x s)=Fin.append x s' ∧
      ((bitsValue (s' ∘ Fin.castAdd w)).toNat,(bitsValue (s' ∘ Fin.natAdd w)).toNat)=
        totientFoldNat (2^w) (qs.map (fun q=>(bitsValue (q.eval x)).toNat))
          ((bitsValue (s ∘ Fin.castAdd w)).toNat,(bitsValue (s ∘ Fin.natAdd w)).toNat) := by
  induction qs generalizing s with
  | nil=>exact ⟨s,rfl,rfl⟩
  | cons q qs ih=>
    obtain ⟨s₁,he₁,hv₁⟩:=totientUpdate_value hw q x s
    obtain ⟨s₂,he₂,hv₂⟩:=ih s₁
    refine ⟨s₂,?_,?_⟩
    · rw [totientScanNet,eval_comp,he₁,he₂]
    · rw [List.map_cons,totientFoldNat,←hv₁]
      exact hv₂

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableTotientCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

lemma totientFromList_value {k w : ℕ} (hw : 0 < w) (v : BooleanNetwork k w)
    (qs : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((totientFromList v qs).eval x)).toNat=
      totientScan (qs.map (fun q=>(bitsValue (q.eval x)).toNat))
        (bitsValue (v.eval x)).toNat % 2^w := by
  let one : Basis w:=(wordConstant (n:=k) (BitVec.ofNat w 1)).eval x
  let s:=Fin.append (v.eval x) one
  have h1 : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  have hs : ((bitsValue (s ∘ Fin.castAdd w)).toNat,(bitsValue (s ∘ Fin.natAdd w)).toNat)=
      ((bitsValue (v.eval x)).toNat,1) := by
    have hl : s ∘ Fin.castAdd w=v.eval x := by funext i; exact Fin.append_left _ _ i
    have hr : s ∘ Fin.natAdd w=one := by funext i; exact Fin.append_right _ _ i
    rw [hl,hr]
    simp only [one,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  obtain ⟨s',he,hv⟩:=totientScanNet_value hw qs x s
  rw [hs] at hv
  have hv':=congrArg Prod.snd hv
  rw [totientFoldNat_score _ _ (_,1) h1,one_mul] at hv'
  have houtput : Fin.append x s' ∘ (fun i=>Fin.natAdd k (Fin.natAdd w i))=s' ∘ Fin.natAdd w := by
    funext i; exact Fin.append_right _ _ _
  rw [totientFromList,eval_comp,eval_comp,eval_pair,eval_pair,eval_select]
  change (bitsValue ((select (fun i=>Fin.natAdd k (Fin.natAdd w i))).eval
    ((totientScanNet qs).eval (Fin.append x s)))).toNat=_
  rw [he,eval_select,houtput]
  exact hv'

theorem tableTotient_exact {k n N M m d : ℕ} (hn : 2 ≤ n) (v : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k)
    (hc : PhysicalTree.CompleteLog n N (tableValues rows x))
    (hM : M∈(tableValues rows x).map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hb : m < 2^n) (hd : m∣M) (hd0 : 0 < d) (hdt : d∣m.totient)
    (hv : (bitsValue (v.eval x)).toNat=d) :
    (bitsValue ((tableTotient v rows).eval x)).toNat=d.totient := by
  rw [tableTotient,totientFromList_value (by omega),List.map_flatten,List.map_replicate,
    tableNets_values hn,hv,PhysicalTree.table_totient_exact hc hM hM0 hm hb hd hd0 hdt]
  have hdB : d < 2^n := by rw [←hv]; exact (bitsValue (v.eval x)).isLt
  exact Nat.mod_eq_of_lt ((Nat.totient_le d).trans_lt hdB)

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedTotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma retainedTotient_exact {N P m d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (v : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hm : 2 ≤ m) (hb : m < 2^n) (hdiv : m∣P) (hd0 : 0 < d) (hdt : d∣m.totient)
    (hv : (bitsValue (v.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedTotient t v).eval (M.encoded x t r))).toNat=d.totient := by
  apply tableTotient_exact hn v (M.fieldRows t) (M.encoded x t r)
  · rwa [M.fieldRows_values]
  · rwa [M.fieldRows_values]
  · exact hP0
  · exact hm
  · exact hb
  · exact hdiv
  · exact hd0
  · exact hdt
  · exact hv

lemma retainedOrderPhi_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedOrderPhi t a m).eval (M.encoded x t r))).toNat=(orderOf u).totient := by
  let : NeZero d := ⟨by omega⟩
  apply M.retainedTotient_exact hn t (M.retainedOrder t a m) x r hc hP hP0 hd
  · rw [←hm]; exact (bitsValue (m.eval (M.encoded x t r))).isLt
  · exact hdiv
  · exact orderOf_pos u
  · simpa only [ZMod.card_units_eq_totient] using (orderOf_dvd_card (x:=u))
  · exact M.retainedOrder_exact hn t a m x r hc hP hP0 hd hdiv u ha hm
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedOrderFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace Completion.Expressions

lemma orderRateCoin_value (n K : ℕ) (v : Fin 3→ℕ) (hd : v 0≤2^n) :
    (orderRateCoin n K).eval v=1-(1-(v 1:ℚ)*prescribedMass (v 0))^K := by
  rw [orderRateCoin,RatExpr.repeatedSuccess_value,RatExpr.eval_mul,RatExpr.eval_ofNat,
    OrderTrial.Expressions.lambdaE_correct]
  · rfl
  · exact hd
end Completion.Expressions
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma orderFilterVars_eval (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis (M.width t)) (r : OrderSlots.Result n)
    (hraw : raw.eval x=OrderSlots.layout n r) :
    (bitsValue ((M.orderFilterVars t a m raw 0).eval x)).toNat=
      (bitsValue ((M.retainedOrder t a m).eval x)).toNat ∧
    (bitsValue ((M.orderFilterVars t a m raw 1).eval x)).toNat=
      (bitsValue ((M.retainedOrderPhi t a m).eval x)).toNat ∧
    (bitsValue ((M.orderFilterVars t a m raw 2).eval x)).toNat=(bitsValue r.2.2.2).toNat := by
  simp only [orderFilterVars,Fin.reduceEq,ite_true, if_true,ite_false, if_false,eval_comp]
  rw [resizeWord_toNat (by dsimp only [orderVarWidth,OrderSlots.coinWidth]; omega),
    resizeWord_toNat (by dsimp only [orderVarWidth,OrderSlots.coinWidth]; omega),
    resizeWord_toNat (by dsimp only [orderVarWidth,OrderSlots.coinWidth]; omega),hraw]
  change _ ∧ _ ∧ (bitsValue ((Completion.retentionWires _ _ _ _).eval
    (Completion.layout _ _ _ _ (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)))).toNat=_
  rw [Completion.retentionWires_eval]
  exact ⟨rfl,rfl,rfl⟩

lemma orderActualFilter_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis c) (h : Trace n t) (r : OrderSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t h))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t h))).toNat=d)
    (hr : raw.eval (M.encoded x t h)=OrderSlots.layout n r) :
    (M.orderActualFilter t a m raw).eval (M.encoded x t h) 0=true ↔
      Completion.test (fun y=>orderResult (OrderSlots.sampleExponent n) n
        (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h)) (n^5) y=orderOf u)
        (fun y=>y=natBasis _ (orderOf u)) (Completion.orderSuccess (orderOf u) (n^5)) (Completion.target n) r := by
  have hv:=M.orderFilterVars_eval t a m raw (M.encoded x t h) r hr
  have he:=M.retainedOrder_exact hn t a m x h hc hP hP0 hd hdiv u ha hm
  have hf:=M.retainedOrderPhi_exact hn t a m x h hc hP hP0 hd hdiv u ha hm
  unfold orderActualFilter
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
  · exact hv.2.2
  · rw [equalOn_value,he,OrderSlots.orderResultNet_value _ _ _ _ r.2.1]
    · rw [eval_comp,hr]
      exact Completion.ordinaryWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
    · rwa [hm]
  · have heq : ((M.retainedOrder t a m).comp (resizeWord n (Completion.transitionWidth n))).eval (M.encoded x t h)=
        natBasis (Completion.transitionWidth n) (orderOf u) := by
      rw [eval_comp,resizeWord_eq_natBasis,he]
    have hvv : (raw.comp (Completion.guessWires (OrderSlots.ordinaryWidth n)
        (Completion.transitionWidth n) (2*n) ((n+10)*n^5))).eval (M.encoded x t h)=r.2.2.1 := by
      rw [eval_comp,hr]
      exact Completion.guessWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
    rw [equalOn_value,hvv,heq]
    exact ⟨fun hh=>(bitsEquiv _).injective (BitVec.eq_of_toNat_eq hh),congrArg (fun z=>(bitsValue z).toNat)⟩
  · rw [Completion.Expressions.orderRateCoin_value]
    · rw [hv.1,hv.2.1,he,hf]
      rfl
    · rw [hv.1]
      exact (bitsValue ((M.retainedOrder t a m).eval (M.encoded x t h))).isLt.le
  · exact RatExpr.eval_const _ _

lemma orderDummyFilter_exact (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) (x : Basis (M.width t))
    (r : OrderSlots.Result n) (hr : raw.eval x=OrderSlots.layout n r) :
    (M.orderDummyFilter t a m raw).eval x 0=true ↔
      Completion.test (fun _=>True) (fun y=>y=natBasis _ 0) 1 (Completion.target n) r := by
  have hv:=M.orderFilterVars_eval t a m raw x r hr
  unfold orderDummyFilter
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)
  · exact hv.2.2
  · simp only [eval_constant]
  · rw [zeroWord_value,eval_comp,hr]
    change (bitsValue ((Completion.guessWires _ _ _ _).eval
      (Completion.layout _ _ _ _ (r.1,OrderSlots.ordinaryLayout n r.2.1,r.2.2)))).toNat=0 ↔ _
    rw [Completion.guessWires_eval]
    exact basis_eq_natBasis (by positivity) _
  · exact RatExpr.eval_const _ _
  · exact RatExpr.eval_const _ _
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveSlots
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree OrderTrial

lemma residueUsable_iff {n : ℕ} (a m : Basis n) :
    residueUsable (bitsValue a).toNat (bitsValue m).toNat ↔ OrderSlots.Usable a m := by
  simp only [residueUsable,OrderSlots.Usable,ZMod.isUnit_iff_coprime]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedOrderTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Both actual usable slots and actual dummy slots, with the identical physical
coin and retained guessed string in their respective branches. -/
theorem retainedOrderFilter_exact_oai {N P : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis c) (h : Trace n t) (r : OrderSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ (bitsValue (m.eval (M.encoded x t h))).toNat)
    (hdiv : (bitsValue (m.eval (M.encoded x t h))).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=OrderSlots.layout n r) :
    (M.retainedOrderFilter t a m raw).eval (M.encoded x t h) 0=true ↔
      dataOrderPassed (trueData P) (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h)) r := by
  classical
  rw [retainedOrderFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,OrderSlots.usableOn_value a m _ (by omega),
    dataOrderPassed,residueUsable_iff]
  by_cases hu : OrderSlots.Usable (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h))
  · simp only [hu,ite_eq_left,true_and,not_true_eq_false,false_and,or_false]
    rw [dataOrder_correct (by omega) hd hdiv hu.2.unit hu.2.unit_spec.symm,
      dataOrderSuccess_correct (by omega) hd hdiv hu.2.unit hu.2.unit_spec.symm]
    exact M.orderActualFilter_exact hn t a m raw x h r hc hP hP0 hd hdiv
      hu.2.unit hu.2.unit_spec.symm rfl hr
  · simp only [hu,ite_eq_right,false_and,not_false_eq_true,true_and,false_or]
    exact M.orderDummyFilter_exact t a m raw (M.encoded x t h) r hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter_exact_oai := @OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter_exact_oai
