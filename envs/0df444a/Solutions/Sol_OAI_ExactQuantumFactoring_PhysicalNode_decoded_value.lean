-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.PhysicalNode.decoded_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:14:44.50064+00:00
-- url     : https://prove2.me/submissions/62d7d8f5-00ed-4803-adf7-488a2f6fe6c7

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

lemma eval_iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) (x : Fin n → Bool) :
    (iterate c k).eval x = (c.eval^[k]) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change (c.comp (iterate c k)).eval x = _
    rw [eval_comp, ih, Function.iterate_succ_apply]

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

lemma staticPowerStep_eval (w : ℕ) (a b : Basis w) :
    (staticPowerStep w).eval (Fin.append a b) =
      Fin.append a ((mul w).eval (Fin.append a b)) := by
  simp only [staticPowerStep,eval_pair,eval_select]
  congr 1
  funext i
  exact Fin.append_left a b i

lemma staticPower_iterate (w e : ℕ) (a b : Basis w) :
    ∃ z : Basis w,
      ((staticPowerStep w).iterate e).eval (Fin.append a b) = Fin.append a z ∧
      bitsValue z = bitsValue a^e * bitsValue b := by
  induction e generalizing b with
  | zero => refine ⟨b,?_,?_⟩ <;> simp [eval_iterate]
  | succ e ih =>
    rw [eval_iterate,Function.iterate_succ_apply,staticPowerStep_eval]
    have h := ih ((mul w).eval (Fin.append a b))
    rw [eval_iterate] at h
    obtain ⟨z,hz,hv⟩ := h
    refine ⟨z,hz,?_⟩
    rw [hv,mul_word,pow_succ]
    exact (mul_assoc _ _ _).symm

lemma staticPower_eval (w e : ℕ) (a : Basis w) :
    bitsValue ((staticPower w e).eval a) = bitsValue a^e := by
  simp only [staticPower,eval_comp,eval_pair,eval_select,Function.comp_id,eval_rewire]
  obtain ⟨z,hz,hv⟩ := staticPower_iterate w e a ((wordConstant (BitVec.ofNat w 1)).eval a)
  rw [hz]
  have he : Fin.append a z ∘ Fin.natAdd w = z := by funext i; exact Fin.append_right _ _ i
  rw [he,hv,wordConstant_eval]
  simp

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
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

lemma rootNext_word (w k : ℕ) (m g : Basis w) :
    bitsValue ((rootNext w k).eval (Fin.append m g)) =
      bitsValue g + BitVec.ofNat w (2^k) := by
  rw [rootNext,eval_comp,eval_pair,add_word,rootGuess_eval,wordConstant_eval]

lemma rootStep_pack (w e k : ℕ) (m g : Basis w) :
    (rootStep w e k).eval (Fin.append m g) =
      Fin.append m ((rootNew w e k).eval (Fin.append m g)) := by
  rw [rootStep,eval_pair,rootModulus_eval]

lemma rootNext_value {n k : ℕ} (m g : Basis (rootWidth n))
    (hk : k ≤ n) (hg : (bitsValue g).toNat+2^k ≤ 2^n) :
    (bitsValue ((rootNext (rootWidth n) k).eval (Fin.append m g))).toNat =
      (bitsValue g).toNat+2^k := by
  have hn : n < rootWidth n := by dsimp [rootWidth] <;> nlinarith
  have hp : 2^n < 2^(rootWidth n) := Nat.pow_lt_pow_right (by decide) hn
  have hkp : 2^k < 2^(rootWidth n) :=
    (Nat.pow_le_pow_right (by decide) hk).trans_lt hp
  rw [rootNext_word,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hkp,
    Nat.mod_eq_of_lt (hg.trans_lt hp)]

lemma candidatePower_lt {n e v : ℕ} (he : e ≤ n) (hv : v ≤ 2^n) :
    v^e < 2^(rootWidth n) := by
  have hne : n*e ≤ n*n := Nat.mul_le_mul_left n he
  calc
    v^e ≤ (2^n)^e := Nat.pow_le_pow_left hv e
    _ = 2^(n*e) := (pow_mul 2 n e).symm
    _ ≤ 2^(n*n) := Nat.pow_le_pow_right (by decide) hne
    _ < 2^(rootWidth n) := Nat.pow_lt_pow_right (by decide) (by simp [rootWidth])

lemma rootNew_value {n e k : ℕ} (m g : Basis (rootWidth n))
    (he : e ≤ n) (hk : k ≤ n) (hg : (bitsValue g).toNat+2^k ≤ 2^n) :
    (bitsValue ((rootNew (rootWidth n) e k).eval (Fin.append m g))).toNat =
      if ((bitsValue g).toNat+2^k)^e ≤ (bitsValue m).toNat
      then (bitsValue g).toNat+2^k else (bitsValue g).toNat := by
  have hv := rootNext_value m g hk hg
  rw [rootNew,wordMux_eval,wordLe_eval,eval_comp,staticPower_eval,rootModulus_eval]
  rw [BitVec.toNat_pow,hv,Nat.mod_eq_of_lt (candidatePower_lt he hg)]
  split_ifs <;> simp_all [rootGuess_eval]

lemma rootPrefix_value {n e : ℕ} (m g : Basis (rootWidth n)) (he : e ≤ n)
    (k : ℕ) (hk : k ≤ n) (hg : (bitsValue g).toNat+2^k ≤ 2^n) :
    ∃ z : Basis (rootWidth n),
      (rootPrefix (rootWidth n) e k).eval (Fin.append m g) = Fin.append m z ∧
      (bitsValue z).toNat = Primality.rootSearch (bitsValue m).toNat e k (bitsValue g).toNat := by
  induction k generalizing g with
  | zero => exact ⟨g,rfl,rfl⟩
  | succ k ih =>
    have hg' : (bitsValue g).toNat+2^k ≤ 2^n := by
      have : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    let z := (rootNew (rootWidth n) e k).eval (Fin.append m g)
    have hz : (bitsValue z).toNat =
        if ((bitsValue g).toNat+2^k)^e ≤ (bitsValue m).toNat
        then (bitsValue g).toNat+2^k else (bitsValue g).toNat := rootNew_value m g he (by omega) hg'
    have hzk : (bitsValue z).toNat+2^k ≤ 2^n := by
      rw [hz]
      split_ifs
      · rw [pow_succ] at hg
        omega
      · exact hg'
    obtain ⟨z',hz',hv'⟩ := ih z (by omega) hzk
    refine ⟨z',?_,?_⟩
    · rw [rootPrefix,eval_comp,rootStep_pack]
      exact hz'
    · rw [hv',hz]
      rfl

lemma boundedRootNet_value (n e : ℕ) (he : e ≤ n) (m : Basis (rootWidth n)) :
    (bitsValue ((boundedRootNet n e).eval m)).toNat =
      Primality.boundedRoot (bitsValue m).toNat e n := by
  let g := (wordConstant (BitVec.ofNat (rootWidth n) 0)).eval m
  have hg : (bitsValue g).toNat=0 := by
    dsimp [g]
    rw [wordConstant_eval]
    simp
  obtain ⟨z,hz,hv⟩ := rootPrefix_value m g he n le_rfl (by rw [hg];omega)
  simp only [boundedRootNet,eval_comp,eval_pair,eval_select,Function.comp_id,eval_rewire]
  change (bitsValue (((rootPrefix (rootWidth n) e n).eval (Fin.append m g)) ∘
    Fin.natAdd (rootWidth n))).toNat = _
  rw [hz]
  have hh : Fin.append m z ∘ Fin.natAdd (rootWidth n)=z := by
    funext i
    exact Fin.append_right m z i
  rw [hh,hv,hg]
  rfl

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

lemma halfWord_value {k w : ℕ} (hw : 2 ≤ w) (d : BooleanNetwork k w) (x : Basis k) :
    (bitsValue ((halfWord d).eval x)).toNat=(bitsValue (d.eval x)).toNat/2 := by
  have h2 : 2 < 2^w := (by norm_num : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  rw [halfWord,eval_comp,eval_pair,div_word,wordConstant_eval,BitVec.toNat_udiv,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2]

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
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_inv _root_.OAI.ExactQuantumFactoring.RatExpr.eval_minus _root_.OAI.ExactQuantumFactoring.RatExpr.eval_neg _root_.OAI.ExactQuantumFactoring.RatExpr.eval_num _root_.OAI.ExactQuantumFactoring.RatExpr.eval_over _root_.OAI.ExactQuantumFactoring.RatExpr.eval_plus _root_.OAI.ExactQuantumFactoring.RatExpr.eval_power _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.RatExpr.eval_sum _root_.OAI.ExactQuantumFactoring.RatExpr.eval_times
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalRounding
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ifLe _root_.OAI.ExactQuantumFactoring.IntExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifEq _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifIntLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifLt _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_inv _root_.OAI.ExactQuantumFactoring.RatExpr.eval_max _root_.OAI.ExactQuantumFactoring.RatExpr.eval_min _root_.OAI.ExactQuantumFactoring.RatExpr.eval_minus _root_.OAI.ExactQuantumFactoring.RatExpr.eval_neg _root_.OAI.ExactQuantumFactoring.RatExpr.eval_num _root_.OAI.ExactQuantumFactoring.RatExpr.eval_over _root_.OAI.ExactQuantumFactoring.RatExpr.eval_plus _root_.OAI.ExactQuantumFactoring.RatExpr.eval_power _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.RatExpr.eval_sum _root_.OAI.ExactQuantumFactoring.RatExpr.eval_times
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

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LabelRecoveryCircuit
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

end BitArithmetic
end ExactQuantumFactoring


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
lemma rareNet_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (rareNet q W t d).eval (layout q W t d r) 0=true ↔ rare r.1 := by
  rw [rareNet,equalOn_value,rareWires_eval,wordConstant_eval]
  simp only [BitVec.toNat_ofNat,Nat.zero_mod,rare]
lemma outputNet_eval {q W t d : ℕ} (ordinary : BooleanNetwork q W)
    (r : Raw (Basis q) W t d) :
    (outputNet ordinary t d).eval (layout q W t d r)=output ordinary.eval r := by
  rw [outputNet,wordMux_eval,guessWires_eval,eval_comp,ordinaryWires_eval,output]
  simp only [rareNet_eval r]
lemma zeros_eval (k m : ℕ) (x : Basis k) : (zeros k m).eval x=fun _ => false := by
  funext i
  simp only [zeros,eval_vector,eval_constant]

end Completion
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlCircuit
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


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController

lemma properOn_value {k w : ℕ} (hw : 0<w) (m d : BooleanNetwork k w) (x : Basis k) :
    (properOn m d).eval x 0=true ↔ ProperDivisor (bitsValue (m.eval x)).toNat
      (bitsValue (d.eval x)).toNat := by
  have h1 : 1<2^w := Nat.one_lt_pow (by omega) (by decide)
  rw [properOn,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    wordLt_eval,wordLt_eval,decide_eq_true_eq,decide_eq_true_eq,wordConstant_eval,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,zeroWord_value,eval_comp,eval_pair,
    mod_word,BitVec.toNat_umod,←Nat.dvd_iff_mod_eq_zero]
  exact and_assoc

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionNetworks
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
open BooleanNetwork
namespace TransitionWords

lemma encodeNet_eval {k n K : ℕ} (f : Fin K → BooleanNetwork k n) (x : Basis k) :
    (encodeNet f).eval x=encode (fun i => (f i).eval x) := by
  funext i
  rw [encodeNet,eval_vector]
  dsimp only [encode]
  split_ifs <;> simp only [eval_rewire,Function.comp_apply,eval_constant]

end TransitionWords
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListNetworks
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
namespace PhysicalListSlots

lemma sampleNet_eval {n : ℕ} (x : Basis (ListSampler.width n)) : (sampleNet n).eval x=sampleRead x := rfl

lemma ordinaryNet_eval {n : ℕ} (x : Basis (ordinaryWidth n)) : (ordinaryNet n).eval x=ordinary x := by
  change (TransitionWords.encodeNet _).eval x=TransitionWords.encode _
  rw [TransitionWords.encodeNet_eval]
  congr 1
  funext i
  rw [eval_comp,tensorSelect_inverse,sampleNet_eval]
lemma outputNet_eval {n : ℕ} (r : Result n) :
    (outputNet n).eval (layout n r)=output r := by
  change (Completion.outputNet _ _ _).eval (Completion.layout _ _ _ _ r)=_
  rw [Completion.outputNet_eval]
  unfold output Completion.output
  simp only [ordinaryNet_eval]

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplit
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
open BooleanNetwork Exactness
namespace FixedSplit

lemma listWires_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (listWires n).eval (listEncoding m l)=PhysicalListSlots.layout n l := by
  exact packed_targetRegister m _
lemma modulusWires_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (modulusWires n).eval (listEncoding m l)=m := packed_first m _

lemma baseNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (l : PhysicalListSlots.Result n) :
    (baseNet i).eval (listEncoding m l)=bases l i := by
  rw [baseNet,eval_rewire,eval_comp,listWires_eval,PhysicalListSlots.outputNet_eval]
  rfl

end FixedSplit
end ExactQuantumFactoring


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

lemma ordinaryOn_eval {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) (x : Basis k)
    (y : Fin (n^5)→Raw n (sampleExponent n) n) (h : raw.eval x=ordinaryLayout n y)
    (hn : 1≤n) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (ordinaryOn a m raw).eval x=ordinary (a.eval x) (m.eval x) y := by
  classical
  rw [ordinaryOn,eval_comp,resizeWord_eq_natBasis,wordMux_eval]
  simp only [usableOn_value a m x hn]
  by_cases hu : Usable (a.eval x) (m.eval x)
  · rw [ite_eq_left hu,orderResultNet_value a m raw x y h hm,ordinary,ite_eq_left hu]
  · rw [ite_eq_right hu,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod,ordinary,ite_eq_right hu]

lemma outputOn_eval {k n : ℕ} (a m : BooleanNetwork k n) (raw : BooleanNetwork k (width n))
    (x : Basis k) (y : Result n) (h : raw.eval x=layout n y) (hn : 1≤n)
    (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (outputOn a m raw).eval x=output (a.eval x) (m.eval x) y := by
  let z : Completion.Raw (Basis (ordinaryWidth n)) (Completion.transitionWidth n) (2*n) ((n+10)*n^5) :=
    (y.1,ordinaryLayout n y.2.1,y.2.2)
  have hz : layout n y=Completion.layout (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5) z := rfl
  have ho : (raw.comp (Completion.ordinaryWires (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5))).eval x=
      ordinaryLayout n y.2.1 := by
    rw [eval_comp,h,hz,Completion.ordinaryWires_eval]
  rw [outputOn,wordMux_eval,ordinaryOn_eval a m _ x y.2.1 ho hn hm]
  simp only [eval_comp,h,hz,Completion.guessWires_eval,Completion.rareNet_eval,output,Completion.output,z]

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SuppliedDivisorCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
namespace Primality
lemma rootSearch_lt (m e k g : ℕ) : rootSearch m e k g < g+2^k := by
  induction k generalizing g with
  | zero => simp [rootSearch]
  | succ k ih =>
    simp only [rootSearch]
    split_ifs with h
    · have hh := ih (g+2^k)
      rw [pow_succ]
      omega
    · have hh := ih g
      rw [pow_succ]
      omega
lemma boundedRoot_lt (m e n : ℕ) : boundedRoot m e n < 2^n := by
  simpa only [boundedRoot,zero_add] using rootSearch_lt m e n 0
end Primality

namespace BitArithmetic
open BooleanNetwork FactorController

lemma firstProperNet_value {k w : ℕ} (hw : 0<w) (m : BooleanNetwork k w)
    (ds : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((firstProperNet m ds).eval x)).toNat =
      firstProper (bitsValue (m.eval x)).toNat (ds.map (fun d => (bitsValue (d.eval x)).toNat)) := by
  induction ds with
  | nil => simp [firstProperNet,firstProper,wordConstant_eval]
  | cons d ds ih =>
    rw [firstProperNet,wordMux_eval]
    simp only [properOn_value hw,List.map_cons,firstProper]
    split_ifs <;> simp_all

lemma evenOn_value {k w : ℕ} (hw : 2≤w) (m : BooleanNetwork k w) (x : Basis k) :
    (evenOn m).eval x 0=true ↔ 2∣(bitsValue (m.eval x)).toNat := by
  have h2 : 2<2^w := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  rw [evenOn,zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2,Nat.dvd_iff_mod_eq_zero]

lemma rootOn_value {k n e : ℕ} (hn : 0<n) (he : e≤n)
    (m : BooleanNetwork k (n+1)) (x : Basis k) :
    (bitsValue ((rootOn n e m).eval x)).toNat=Primality.boundedRoot (bitsValue (m.eval x)).toNat e n := by
  have hw : n+1 ≤ rootWidth n := by dsimp [rootWidth] <;> nlinarith
  rw [rootOn,eval_comp,resizeWord_value,BitVec.toNat_setWidth,eval_comp,
    boundedRootNet_value n e he,eval_comp,resizeWord_toNat hw]
  exact Nat.mod_eq_of_lt ((Primality.boundedRoot_lt _ _ _).trans
    (Nat.pow_lt_pow_right (by decide) (by omega)))

lemma rootsOn_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k (n+1)) (x : Basis k) :
    (bitsValue ((rootsOn n m).eval x)).toNat=rootSplit (bitsValue (m.eval x)).toNat n := by
  rw [rootsOn,firstProperNet_value (by omega),rootSplit,rootProposals,List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  exact rootOn_value hn (by have hh := List.mem_range.mp he; omega) m x

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WideSplitCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController

lemma halfPowerBits_value {k w e : ℕ} (he : 2≤e) (a m : BooleanNetwork k w)
    (d : BooleanNetwork k e) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((halfPowerBits a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%(bitsValue (m.eval x)).toNat := by
  have hh : horner (((halfWord d).rewire Fin.rev).eval x) e le_rfl=(bitsValue (d.eval x)).toNat/2 := by
    rw [horner_full,Triangular.inputNumber_reverse]
    have hr : reverseBits e (((halfWord d).rewire Fin.rev).eval x)=(halfWord d).eval x := by
      funext i
      simp [reverseBits,eval_rewire]
    rw [hr,halfWord_value he]
  rw [halfPowerBits,eval_comp,eval_pair,eval_pair,modularPower_value _ _ _ hm,hh]

lemma shiftedHalfBits_value {k n e : ℕ} (he : 2≤e) (a m : BooleanNetwork k (n+1))
    (d : BooleanNetwork k e) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((shiftedHalfBits a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
        (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat-1 := by
  have hp := Nat.mod_lt ((bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2))
    (by omega : 0<(bitsValue (m.eval x)).toNat)
  have hsum : (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
      (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat<2^(n+1) := by
    rw [pow_succ]; omega
  have h1 : 1<2^(n+1) := Nat.one_lt_two_pow (by omega)
  rw [shiftedHalfBits,eval_comp,eval_pair,sub_word,eval_comp,eval_pair,add_word,
    wordConstant_eval,BitVec.toNat_sub,BitVec.toNat_add,halfPowerBits_value he _ _ _ _ hm,
    Nat.mod_eq_of_lt hsum,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  let v := (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
    (bitsValue (m.eval x)).toNat
  let M := (bitsValue (m.eval x)).toNat
  change (2^(n+1)-1+(v+M))%2^(n+1)=v+M-1
  have hh : 2^(n+1)-1+(v+M)=2^(n+1)+(v+M-1) := by dsimp [v,M];omega
  rw [hh,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by dsimp [v,M];omega)]

lemma candidateBits_value {k n e : ℕ} (he : 2≤e) (a m : BooleanNetwork k (n+1))
    (d : BooleanNetwork k e) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((candidateBits a m d).eval x)).toNat=candidateDivisor
      (bitsValue (m.eval x)).toNat (bitsValue (a.eval x)).toNat (bitsValue (d.eval x)).toNat := by
  have hpos : ¬(bitsValue (d.eval x)).toNat=0 ↔ 0<(bitsValue (d.eval x)).toNat := by omega
  simp only [candidateBits,wordMux_eval,eval_band,Bool.and_eq_true,bnot_value,
    zeroWord_value,evenOn_value he,hpos,candidateDivisor]
  split_ifs
  · rw [eval_comp,eval_pair,gcdNet_value,shiftedHalfBits_value he _ _ _ _ hm hb]
  · simp [wordConstant_eval]

lemma ordersBits_value {k n e : ℕ} (he : 2≤e) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k e)) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((ordersBits m ars).eval x)).toNat=orderSplit (bitsValue (m.eval x)).toNat
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  rw [ordersBits,firstProperNet_value (by omega),orderSplit,List.map_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro ar _
  exact candidateBits_value he ar.1 m ar.2 x hm hb

theorem suppliedBits_value {k n e : ℕ} (hn : 0<n) (he : 2≤e) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k e)) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((suppliedBits n m ars).eval x)).toNat=suppliedDivisor (bitsValue (m.eval x)).toNat n
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  simp only [suppliedBits,wordMux_eval,evenOn_value (by omega : 2≤n+1),
    properOn_value (by omega : 0<n+1),rootsOn_value hn,suppliedDivisor]
  split_ifs
  · rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    exact (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact rootsOn_value hn m x
  · exact ordersBits_value he m ars x hm hb

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplitDecoder
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
namespace FixedSplit

lemma launchWires_eval {n : ℕ} (m : Basis n) (r : Raw n) :
    (launchWires n).eval (encoding m r)=listEncoding m r.1 := packed_first _ _
lemma allOrderWires_eval {n : ℕ} (m : Basis n) (r : Raw n) :
    (allOrderWires n).eval (encoding m r)=ordersLayout n r.2 := packed_targetRegister _ _
lemma modulusNet_eval {n : ℕ} (m : Basis n) (r : Raw n) :
    (modulusNet n).eval (encoding m r)=m := by
  rw [modulusNet,eval_comp,launchWires_eval,modulusWires_eval]
lemma actualBaseNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (r : Raw n) :
    (actualBaseNet i).eval (encoding m r)=bases r.1 i := by
  rw [actualBaseNet,eval_comp,launchWires_eval,baseNet_eval]
lemma actualOrderRawNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (r : Raw n) :
    (actualOrderRawNet i).eval (encoding m r)=OrderSlots.layout n (r.2 i) := by
  rw [actualOrderRawNet,eval_comp,allOrderWires_eval]
  exact tensorSelect_eval _ i
lemma actualOrderNet_eval {n : ℕ} (hn : 1≤n) (i : Fin (n^5)) (m : Basis n) (r : Raw n)
    (hm : 2≤(bitsValue m).toNat) :
    (actualOrderNet i).eval (encoding m r)=OrderSlots.output (bases r.1 i) m (r.2 i) := by
  rw [actualOrderNet,OrderSlots.outputOn_eval _ _ _ _ (r.2 i)
    (actualOrderRawNet_eval i m r) hn (by rw [modulusNet_eval];exact hm),
    actualBaseNet_eval,modulusNet_eval]

theorem divisorNet_value {n : ℕ} (hn : 2≤n) (m : Basis n) (r : Raw n)
    (hm : 2≤(bitsValue m).toNat) :
    (bitsValue ((divisorNet n).eval (encoding m r))).toNat=divisor m r := by
  have hm' : (bitsValue ((liftedModulus n).eval (encoding m r))).toNat=(bitsValue m).toNat := by
    rw [liftedModulus,eval_comp,resizeWord_toNat (by omega),modulusNet_eval]
  have he : 2≤Completion.transitionWidth n := by
    unfold Completion.transitionWidth
    calc 2≤n := hn
         _ ≤ n*(n^5+1) := Nat.le_mul_of_pos_right n (by omega)
  rw [divisorNet,suppliedBits_value (by omega) he _ _ _ (by rw [hm'];exact hm)
    (by rw [hm'];exact (bitsValue m).isLt),hm',divisor]
  congr 1
  rw [actualPairs,List.map_ofFn]
  unfold pairs
  congr 1
  funext i
  simp only [Function.comp_apply,eval_comp,resizeWord_toNat (Nat.le_succ n),
    actualBaseNet_eval,actualOrderNet_eval (by omega : 1≤n) i m r hm]

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeSplitMachine
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
namespace PhysicalNode

lemma decoded_value_oai {n : ℕ} (hn : 2 ≤ n) (q : Basis n) (r : FixedSplit.Raw n)
    (hq : 2 ≤ (bitsValue q).toNat) :
    (bitsValue (decoded q r)).toNat=FixedSplit.divisor q r :=
  FixedSplit.divisorNet_value hn q r hq

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.PhysicalNode.decoded_value_oai := @OAI.ExactQuantumFactoring.PhysicalNode.decoded_value_oai
