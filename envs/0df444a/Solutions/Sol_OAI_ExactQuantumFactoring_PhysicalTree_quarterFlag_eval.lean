-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.PhysicalTree.quarterFlag_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:15:25.405984+00:00
-- url     : https://prove2.me/submissions/78c303b8-5ad0-415f-adc4-a11dfc804164

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
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalNode_decoded_value
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTree_accepted_iff_passed
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTree_treePrefixFilter_passed

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_Primality
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Necessary exact primality component of Appendix A.  The tests are polynomial
congruences, not a primality oracle.  These lemmas start the appendix's actual
root-count proof; no polynomial-time implementation is assumed here. -/
namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

lemma Introspective.one {F : Type*} [CommRing F] (s : ℕ) (f : F[X]) :
    Introspective s 1 f := by intro z _; simp

lemma Introspective.mul_exp {F : Type*} [CommRing F] {s k l : ℕ} {f : F[X]}
    (hk : Introspective s k f) (hl : Introspective s l f) :
    Introspective s (k*l) f := by
  intro z hz
  rw [pow_mul, hk z hz, hl]
  · rw [pow_mul]
  · rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]

lemma Introspective.pow_exp {F : Type*} [CommRing F] {s k : ℕ} {f : F[X]}
    (hk : Introspective s k f) (u : ℕ) : Introspective s (k^u) f := by
  induction u with
  | zero => simpa using Introspective.one s f
  | succ u hu => simpa [pow_succ] using hu.mul_exp hk

lemma Introspective.mul_poly {F : Type*} [CommRing F] {s k : ℕ} {f g : F[X]}
    (hf : Introspective s k f) (hg : Introspective s k g) :
    Introspective s k (f*g) := by
  intro z hz
  simp only [eval_mul, mul_pow]
  rw [hf z hz, hg z hz]

lemma Introspective.prod {F ι : Type*} [CommRing F] {s k : ℕ}
    (S : Finset ι) (f : ι → F[X]) (hf : ∀ i ∈ S, Introspective s k (f i)) :
    Introspective s k (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro z _; simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul_poly
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma natCast_frobenius {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (a : ℕ) : (a : F)^p = (a : F) := by
  exact map_natCast (frobenius F p) a

lemma linear_frobenius {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (s a : ℕ) : Introspective s p (X + C (a : F)) := by
  intro z _
  simp only [eval_add, eval_X, eval_C]
  rw [add_pow_char, natCast_frobenius]

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityRootCount
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

lemma residueOrbit_rep {s m p : ℕ} (x : residueOrbit s m p) :
    ∃ u v : ℕ, ((m^u*p^v : ℕ) : ZMod s) = x.val := by
  simpa using (Submonoid.mem_closure_pair (m : ZMod s) (p : ZMod s) x.val).mp x.property

lemma residueRoot_injective {F : Type*} [Field F] {s m p : ℕ} [NeZero s]
    {w : F} (hw : IsPrimitiveRoot w s) :
    Function.Injective (residueRoot (s := s) (m := m) (p := p) w) := by
  intro x y hxy
  apply Subtype.ext
  apply ZMod.val_injective
  exact hw.pow_inj (ZMod.val_lt x.val) (ZMod.val_lt y.val) hxy

lemma eval_eq_on_orbit {F : Type*} [Field F] {s m p : ℕ} {w : F}
    (hw : w^s = 1) {f g : F[X]}
    (hfm : Introspective s m f) (hfp : Introspective s p f)
    (hgm : Introspective s m g) (hgp : Introspective s p g)
    (hfg : f.eval w = g.eval w) (x : residueOrbit s m p) :
    f.eval (residueRoot w x) = g.eval (residueRoot w x) := by
  obtain ⟨u,v,hrep⟩ := residueOrbit_rep x
  have hf := ((hfm.pow_exp u).mul_exp (hfp.pow_exp v)) w hw
  have hg := ((hgm.pow_exp u).mul_exp (hgp.pow_exp v)) w hw
  have hk : residueRoot w x = w^(m^u*p^v) := by
    unfold residueRoot
    rw [← hrep, ZMod.val_natCast, ← pow_eq_pow_mod _ hw]
  rw [hk, ← hf, ← hg, hfg]

/-- The lower-bound injection is proved by h distinct roots of f-g, not by
assuming any tested product has a nonzero value. -/
lemma eval_injective_low_degree {F : Type*} [Field F] {s m p : ℕ} [NeZero s]
    {w : F} (hw : IsPrimitiveRoot w s) {f g : F[X]}
    (hfm : Introspective s m f) (hfp : Introspective s p f)
    (hgm : Introspective s m g) (hgp : Introspective s p g)
    (hfg : f.eval w = g.eval w)
    (hf : f.natDegree < Nat.card (residueOrbit s m p))
    (hg : g.natDegree < Nat.card (residueOrbit s m p)) : f = g := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite (residueOrbit s m p)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq f g (residueRoot_injective (m := m) (p := p) hw)
  · exact eval_eq_on_orbit hw.pow_eq_one hfm hfp hgm hgp hfg
  · simpa [Nat.card_eq_fintype_card] using max_lt hf hg

lemma subsetPolynomial_injective {F : Type*} [Field F] :
    Function.Injective (subsetPolynomial (F := F)) := by
  intro S T h
  have hr := congrArg Polynomial.roots h
  simpa [subsetPolynomial, Polynomial.roots_prod_X_sub_C, Finset.val_inj] using hr

lemma subsetPolynomial_degree {F : Type*} [Field F] (S : Finset F) :
    (subsetPolynomial S).natDegree = S.card :=
  Polynomial.natDegree_finsetProd_X_sub_C_eq_card S id

lemma subsetPolynomial_introspective {F : Type*} [Field F] {s k : ℕ}
    (S : Finset F) (hf : ∀ a ∈ S, Introspective s k (X-C a)) :
    Introspective s k (subsetPolynomial S) := Introspective.prod S _ hf

/-- The entire lower/upper root count, prior to arithmetic estimates: a collision
of two distinct integer exponents bounds the number of subset products. -/
lemma subset_count_le_collision {F : Type*} [Field F] {s m p : ℕ} [NeZero s]
    {w : F} (hw : IsPrimitiveRoot w s) (S : Finset F) {t k₁ k₂ : ℕ}
    (ht : t < Nat.card (residueOrbit s m p))
    (hm : ∀ a ∈ S, Introspective s m (X-C a))
    (hp : ∀ a ∈ S, Introspective s p (X-C a))
    (hk₁ : ∀ a ∈ S, Introspective s k₁ (X-C a))
    (hk₂ : ∀ a ∈ S, Introspective s k₂ (X-C a))
    (hk : w^k₁ = w^k₂) (hne : k₁ ≠ k₂) :
    S.card.choose t ≤ max k₁ k₂ := by
  classical
  let T := S.powersetCard t
  let values := T.image (fun A => (subsetPolynomial A).eval w)
  have he : Set.InjOn (fun A => (subsetPolynomial A).eval w) T := by
    intro A hA B hB hAB
    obtain ⟨hAS,hAt⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨hBS,hBt⟩ := Finset.mem_powersetCard.mp hB
    apply subsetPolynomial_injective
    exact eval_injective_low_degree hw
      (subsetPolynomial_introspective A (fun a ha => hm a (hAS ha)))
      (subsetPolynomial_introspective A (fun a ha => hp a (hAS ha)))
      (subsetPolynomial_introspective B (fun a ha => hm a (hBS ha)))
      (subsetPolynomial_introspective B (fun a ha => hp a (hBS ha))) hAB
      (by simpa [subsetPolynomial_degree, hAt] using ht)
      (by simpa [subsetPolynomial_degree, hBt] using ht)
  have hv : values.card = S.card.choose t := by
    rw [Finset.card_image_of_injOn he, Finset.card_powersetCard]
  have hpoly : (X^k₁-X^k₂ : F[X]) ≠ 0 := by
    intro hz
    have heq := congrArg Polynomial.natDegree (sub_eq_zero.mp hz)
    exact hne (by simpa using heq)
  have hroots : values.val ⊆ (X^k₁-X^k₂ : F[X]).roots := by
    intro z hz
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hAS,_⟩ := Finset.mem_powersetCard.mp hA
    rw [Polynomial.mem_roots hpoly]
    have h₁ := subsetPolynomial_introspective A (fun a ha => hk₁ a (hAS ha)) w hw.pow_eq_one
    have h₂ := subsetPolynomial_introspective A (fun a ha => hk₂ a (hAS ha)) w hw.pow_eq_one
    simp only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X]
    rw [h₁,h₂,hk,sub_self]
  calc
    S.card.choose t = values.card := hv.symm
    _ ≤ (X^k₁-X^k₂ : F[X]).natDegree := Polynomial.card_le_degree_of_subset_roots hroots
    _ ≤ max k₁ k₂ := by simpa using Polynomial.natDegree_sub_le (X^k₁ : F[X]) (X^k₂)

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityArithmetic
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

lemma orbit_order_le (s m p : ℕ) [NeZero s] :
    orderOf (m : ZMod s) ≤ Nat.card (residueOrbit s m p) := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite _
  let f : Fin (orderOf (m : ZMod s)) → residueOrbit s m p := fun i =>
    ⟨(m : ZMod s)^i.val, (Submonoid.mem_closure_pair _ _ _).mpr
      ⟨i.val,0,by simp⟩⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact pow_injOn_Iio_orderOf i.isLt j.isLt (congrArg Subtype.val he)
  simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

lemma orbit_card_le {s m p : ℕ} [Fact s.Prime]
    (hm : (m : ZMod s) ≠ 0) (hp : (p : ZMod s) ≠ 0) :
    Nat.card (residueOrbit s m p) ≤ s-1 := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite _
  have hn : ∀ x : residueOrbit s m p, x.val ≠ 0 := by
    intro x
    obtain ⟨u,v,huv⟩ := residueOrbit_rep x
    rw [← huv]
    exact_mod_cast mul_ne_zero (pow_ne_zero u hm) (pow_ne_zero v hp)
  let f : residueOrbit s m p → (ZMod s)ˣ := fun x => Units.mk0 x.val (hn x)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Units.val hxy
  simpa [Nat.card_eq_fintype_card, Nat.totient_prime (Fact.out : s.Prime)] using Fintype.card_le_of_injective f hf

/-- Pigeonhole collision in the square of side floor(sqrt |H|)+1. -/
lemma orbit_collision (s m p : ℕ) [NeZero s] :
    ∃ u v u' v' : ℕ,
      u ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      v ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      u' ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      v' ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      (u,v) ≠ (u',v') ∧
      ((m^u*p^v : ℕ) : ZMod s) = ((m^u'*p^v' : ℕ) : ZMod s) := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite _
  let q := Nat.sqrt (Nat.card (residueOrbit s m p))
  let f : Fin (q+1) × Fin (q+1) → residueOrbit s m p := fun x =>
    ⟨(m : ZMod s)^x.1.val*(p : ZMod s)^x.2.val,
      (Submonoid.mem_closure_pair _ _ _).mpr ⟨x.1.val,x.2.val,rfl⟩⟩
  have hb : Fintype.card (residueOrbit s m p) <
      Fintype.card (Fin (q+1) × Fin (q+1)) := by
    simpa [Fintype.card_prod, Nat.card_eq_fintype_card, q] using
      Nat.lt_succ_sqrt (Nat.card (residueOrbit s m p))
  obtain ⟨a,b,hab,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hb
  refine ⟨a.1.val,a.2.val,b.1.val,b.2.val,
    Nat.le_of_lt_succ a.1.isLt,Nat.le_of_lt_succ a.2.isLt,
    Nat.le_of_lt_succ b.1.isLt,Nat.le_of_lt_succ b.2.isLt,?_,?_⟩
  · intro h
    apply hab
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst h)
    · exact Fin.ext (congrArg Prod.snd h)
  · simpa [f] using congrArg Subtype.val he

lemma prime_factorization_positive {m q : ℕ} (hm : m ≠ 0) (hq : q.Prime)
    (hqm : q ∣ m) : 0 < m.factorization q := by
  exact hq.factorization_pos_of_dvd hm hqm

/-- Distinct exponent pairs represent distinct natural numbers, using the other
prime divisor of m. This is where the perfect-power test is essential. -/
lemma exponent_pair_injective {m p q : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hqm : q ∣ m) (hpq : p ≠ q) :
    Function.Injective (fun uv : ℕ × ℕ => m^uv.1*p^uv.2) := by
  intro a b hab
  dsimp at hab
  have hfac := congrArg (fun k : ℕ => k.factorization q) hab
  have hpq0 : p.factorization q = 0 := by
    rw [hp.factorization]
    simp [hpq]
  simp only [Nat.factorization_mul (pow_ne_zero _ hm) (pow_ne_zero _ hp.ne_zero),
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hpq0, mul_zero, add_zero] at hfac
  have hu : a.1 = b.1 := Nat.mul_right_cancel (prime_factorization_positive hm hq hqm) hfac
  have hv : a.2 = b.2 := by
    rw [hu] at hab
    have h := Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hm) _) hab
    exact Nat.pow_right_injective hp.two_le h
  exact Prod.ext hu hv

lemma exponent_bound {m p q u v : ℕ} (hm : 1 ≤ m) (hp : p ≤ m)
    (hu : u ≤ q) (hv : v ≤ q) : m^u*p^v ≤ m^(2*q) := by
  calc
    m^u*p^v ≤ m^q*m^q := Nat.mul_le_mul (Nat.pow_le_pow_right hm hu)
      ((Nat.pow_le_pow_left hp v).trans (Nat.pow_le_pow_right hm hv))
    _ = m^(2*q) := by rw [← pow_add]; congr 1; omega

/-- Elementary combinatorial bound used in the appendix. Pair the descending
factors M-i with c*(t-i), so no real logarithms or asymptotics are assumed. -/
lemma power_le_choose_mul {c s t : ℕ} (ht : t ≤ s) :
    c^t ≤ (c*s).choose t := by
  have hd : c^t * t.factorial ≤ (c*s).descFactorial t := by
    rw [← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_eq_prod_range]
    calc
      c^t * ∏ i ∈ Finset.range t, (t-i) =
          ∏ i ∈ Finset.range t, c*(t-i) := by simp [Finset.prod_mul_distrib]
      _ ≤ ∏ i ∈ Finset.range t, (c*s-i) := by
        apply Finset.prod_le_prod'
        intro i hi
        have hi' := Finset.mem_range.mp hi
        by_cases hc : c = 0
        · simp [hc]
        · have hc' : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc
          rw [Nat.mul_sub_left_distrib]
          have hct : c*t ≤ c*s := Nat.mul_le_mul_left c ht
          have hci : i ≤ c*i := Nat.le_mul_of_pos_left i (by omega)
          omega
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hd
  exact Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_comm] using hd) (Nat.factorial_pos t)

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityCorrectness
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

lemma other_prime_divisor {m p : ℕ} (_hm : 2 ≤ m) (hcom : ¬ m.Prime)
    (hpow : ¬ PerfectPower m) (hp : p.Prime) (hpm : p ∣ m) :
    ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ p ≠ q := by
  by_contra hn
  have hu : IsPrimePow m := isPrimePow_iff_unique_prime_dvd.mpr
    ⟨p, ⟨hp,hpm⟩, fun q hq => by
      by_contra he
      exact hn ⟨q,hq.1,hq.2,Ne.symm he⟩⟩
  obtain ⟨q,e,hq,he,hqe⟩ := (isPrimePow_nat_iff m).mp hu
  have he2 : 2 ≤ e := by
    by_contra h
    have : e = 1 := by omega
    subst e
    simp only [pow_one] at hqe
    exact hcom (hqe ▸ hq)
  exact hpow ⟨q,e,hq.two_le,he2,hqe⟩

lemma sqrt_exponent_lt {n h : ℕ} (hn : 3 ≤ n) (hh : n^2 < h) :
    n * Nat.sqrt h < h := by
  have hsq := Nat.sqrt_le h
  have hnl : n ≤ Nat.sqrt h := Nat.le_sqrt'.mpr hh.le
  by_cases he : n = Nat.sqrt h
  · rw [← he]
    simpa [pow_two] using hh
  · have hlt : n < Nat.sqrt h := by omega
    have hpos : 0 < Nat.sqrt h := by omega
    calc
      n * Nat.sqrt h < Nat.sqrt h * Nat.sqrt h := Nat.mul_lt_mul_of_pos_right hlt hpos
      _ ≤ h := hsq

lemma upper_lt_lower {n m h : ℕ} (hn : 3 ≤ n) (hm : m < 2^n) (hh : n^2 < h) :
    m^(2*Nat.sqrt h) < 8^(h-1) := by
  have hnh := sqrt_exponent_lt hn hh
  have h3 : 3 < h := by nlinarith
  have hqpos : 0 < 2*Nat.sqrt h := by
    have := (Nat.sqrt_pos.mpr (show 0 < h by omega)); omega
  calc
    m^(2*Nat.sqrt h) < (2^n)^(2*Nat.sqrt h) := Nat.pow_lt_pow_left hm (by omega)
    _ = 2^(2*(n*Nat.sqrt h)) := by rw [← pow_mul]; congr 1; ring
    _ < 2^(2*h) := Nat.pow_lt_pow_right (by decide) (by omega)
    _ < 2^(3*(h-1)) := Nat.pow_lt_pow_right (by decide) (by omega)
    _ = 8^(h-1) := by rw [pow_mul]; norm_num

/-- This is the appendix's entire root-count contradiction, over an arbitrary
characteristic-p extension with a primitive s-th root. -/
lemma root_count_contradiction {F : Type*} [Field F] {n m s p q : ℕ}
    [Fact s.Prime] [Fact p.Prime] [CharP F p]
    (hn : 3 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n)
    (hms : (m : ZMod s) ≠ 0) (hps : (p : ZMod s) ≠ 0)
    (hpbig : 8*s < p) (hpm : p ∣ m) (hq : q.Prime) (hqm : q ∣ m) (hpq : p ≠ q)
    (horder : n^2 < orderOf (m : ZMod s))
    {w : F} (hw : IsPrimitiveRoot w s)
    (htest : ∀ a : ℕ, 1 ≤ a → a ≤ 8*s → Introspective s m (X+C (a : F))) : False := by
  classical
  let S : Finset F := (Finset.Icc 1 (8*s)).image (fun a : ℕ => -(a : F))
  have hScard : S.card = 8*s := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb he
      apply CharP.natCast_injOn_Iio F p
      · exact lt_of_le_of_lt (Finset.mem_Icc.mp ha).2 hpbig
      · exact lt_of_le_of_lt (Finset.mem_Icc.mp hb).2 hpbig
      · exact neg_injective he
  have hSm : ∀ a ∈ S, Introspective s m (X-C a) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    simpa using htest b (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
  have hSp : ∀ a ∈ S, Introspective s p (X-C a) := by
    intro a ha
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
    simpa using (linear_frobenius (F := F) p s b)
  let h := Nat.card (residueOrbit s m p)
  have hlarge : n^2 < h := horder.trans_le (orbit_order_le s m p)
  have hsmall : h ≤ s-1 := orbit_card_le hms hps
  obtain ⟨u,v,u',v',hu,hv,hu',hv',hne,hcon⟩ := orbit_collision s m p
  have hne' : m^u*p^v ≠ m^u'*p^v' :=
    fun he => hne (exponent_pair_injective (by omega) Fact.out hq hqm hpq he)
  have hew : w^(m^u*p^v) = w^(m^u'*p^v') := by
    conv_lhs => rw [pow_eq_pow_mod _ hw.pow_eq_one]
    conv_rhs => rw [pow_eq_pow_mod _ hw.pow_eq_one]
    congr 1
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hcon
  have hc := subset_count_le_collision hw S (t := h-1) (by change h-1 < h; omega)
    hSm hSp (fun a ha => ((hSm a ha).pow_exp u).mul_exp ((hSp a ha).pow_exp v))
    (fun a ha => ((hSm a ha).pow_exp u').mul_exp ((hSp a ha).pow_exp v')) hew hne'
  rw [hScard] at hc
  have hpmle : p ≤ m := Nat.le_of_dvd (by omega) hpm
  have hupp : max (m^u*p^v) (m^u'*p^v') ≤ m^(2*Nat.sqrt h) :=
    max_le (exponent_bound (by omega) hpmle hu hv)
      (exponent_bound (by omega) hpmle hu' hv')
  have hlow : 8^(h-1) ≤ (8*s).choose (h-1) := power_le_choose_mul (by omega)
  exact (not_lt_of_ge (hlow.trans (hc.trans hupp))) (upper_lt_lower hn hmb hlarge)

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AKSCriteria
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality

lemma prime_not_perfectPower {m : ℕ} (hm : m.Prime) : ¬ PerfectPower m := by
  rintro ⟨b,e,hb,he,h⟩
  have hd : b ∣ m := by rw [← h]; exact dvd_pow_self b (by omega)
  have hbm : b=m := (hm.eq_one_or_self_of_dvd b hd).resolve_left (by omega)
  subst b
  have hlt : m < m^e := by
    simpa using Nat.pow_lt_pow_right (by omega : 1 < m) (by omega : 1 < e)
  omega

lemma order_tests_iff {m s k : ℕ} (hs : s.Prime) (hcop : s.Coprime m) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → m^j%s ≠ 1) ↔ k < orderOf (m : ZMod s) := by
  let : Fact s.Prime := ⟨hs⟩
  have ho : 0 < orderOf (m : ZMod s) :=
    ((ZMod.isUnit_iff_coprime m s).mpr hcop.symm).isOfFinOrder.orderOf_pos
  have hp (j : ℕ) : m^j%s=1 ↔ (m : ZMod s)^j=1 := by
    constructor
    · intro h
      have : ((m^j%s : ℕ) : ZMod s)=(1 : ZMod s) := by
        simpa only [Nat.cast_one] using congrArg (fun a : ℕ => (a : ZMod s)) h
      simpa only [ZMod.natCast_mod,Nat.cast_pow,Nat.cast_one] using this
    · intro h
      have := congrArg ZMod.val h
      simpa only [← Nat.cast_pow,ZMod.val_natCast,ZMod.val_one] using this
  constructor
  · intro h
    by_contra hn
    exact h _ ho (by omega) ((hp _).mpr (pow_orderOf_eq_one (m : ZMod s)))
  · intro h j hj hk hh
    exact pow_ne_one_of_lt_orderOf (by omega) (hk.trans_lt h) ((hp j).mp hh)

lemma prime_of_no_small_divisor {m B : ℕ} (hm : 2 ≤ m) (hb : m ≤ B)
    (h : ∀ d : ℕ, 2 ≤ d → d ≤ B → d < m → ¬ d ∣ m) : m.Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨hm,?_⟩
  intro d hd hdm
  by_contra hne
  have hd2 : 2 ≤ d := by
    by_contra hn
    have : d=0 := by omega
    subst d
    simp only [Nat.zero_dvd] at hdm
    omega
  exact h d hd2 (by omega) hd hdm

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanFold
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_vector _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

lemma any_eval {n : ℕ} (cs : List (BooleanNetwork n 1)) (x : Fin n → Bool) :
    (any cs).eval x 0=true ↔ ∃ c ∈ cs, c.eval x 0=true := by
  induction cs with
  | nil => simp [any]
  | cons c cs ih => simp [any,ih]

lemma all_eval {n : ℕ} (cs : List (BooleanNetwork n 1)) (x : Fin n → Bool) :
    (all cs).eval x 0=true ↔ ∀ c ∈ cs, c.eval x 0=true := by
  induction cs with
  | nil => simp [all]
  | cons c cs ih => simp [all,ih]

end ExactQuantumFactoring.BooleanNetwork


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
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

lemma constMod_value (w d : ℕ) (x : Basis w) (hd : d < 2^w) :
    (bitsValue ((constMod w d).eval x)).toNat=(bitsValue x).toNat%d := by
  rw [constMod,eval_comp,eval_pair,eval_select,Function.comp_id,mod_word,wordConstant_eval,
    BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hd]

lemma dividesNet_value (w d : ℕ) (x : Basis w) (hd : d < 2^w) :
    (dividesNet w d).eval x 0=true ↔ d ∣ (bitsValue x).toNat := by
  rw [dividesNet,equalOn_value,constMod_value _ _ _ hd,wordConstant_eval]
  simp only [BitVec.toNat_ofNat,Nat.zero_mod]
  exact Nat.dvd_iff_mod_eq_zero.symm

lemma constPowMod_value (w s j : ℕ) (x : Basis w) (hs : 2 ≤ s)
    (hsw : s < 2^w) (hjw : j < 2^w) :
    (bitsValue ((constPowMod w s j).eval x)).toNat = (bitsValue x).toNat^j%s := by
  let sb := (wordConstant (n := w) (BitVec.ofNat w s)).eval x
  let eb := ((wordConstant (n := w) (BitVec.ofNat w j)).rewire Fin.rev).eval x
  have hs' : (bitsValue sb).toNat=s := by
    simp only [sb,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hsw]
  have he : horner eb w le_rfl=j := by
    rw [horner_full,Triangular.inputNumber_reverse]
    have hh : reverseBits w eb = (wordConstant (n := w) (BitVec.ofNat w j)).eval x := by
      funext i
      simp [reverseBits,eb]
    rw [hh,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hjw]
  have hm : 2 ≤ (bitsValue sb).toNat := by omega
  simp only [constPowMod,eval_comp,eval_pair,eval_select,Function.comp_id]
  change (bitsValue ((modularPower w w).eval (Fin.append (Fin.append x sb) eb))).toNat=_
  rw [modularPower_value _ _ _ hm,he,hs']

lemma powerOneNet_value (w s j : ℕ) (x : Basis w) (hs : 2 ≤ s)
    (hsw : s < 2^w) (hjw : j < 2^w) :
    (powerOneNet w s j).eval x 0=true ↔ (bitsValue x).toNat^j%s=1 := by
  rw [powerOneNet,equalOn_value,constPowMod_value _ _ _ _ hs hsw hjw,wordConstant_eval,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 1 < 2^w)]

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

lemma all_ofFn_eval {n k : ℕ} (cs : Fin k → BooleanNetwork n 1) (x : Basis n) :
    (all (List.ofFn cs)).eval x 0=true ↔ ∀ i, (cs i).eval x 0=true := by
  rw [all_eval]
  simp

lemma any_ofFn_eval {n k : ℕ} (cs : Fin k → BooleanNetwork n 1) (x : Basis n) :
    (any (List.ofFn cs)).eval x 0=true ↔ ∃ i, (cs i).eval x 0=true := by
  rw [any_eval]
  simp

lemma bnot_value {n : ℕ} (c : BooleanNetwork n 1) (x : Basis n) :
    c.bnot.eval x 0=true ↔ ¬ c.eval x 0=true := by simp

end ExactQuantumFactoring.BooleanNetwork

namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma orderTests_value (w s k : ℕ) (x : Basis w) (hs : 2 ≤ s)
    (hsw : s < 2^w) (hkw : k < 2^w) :
    (orderTests w s k).eval x 0=true ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ k → (bitsValue x).toNat^j%s ≠ 1 := by
  rw [orderTests,all_ofFn_eval]
  constructor
  · intro h j hj hjk
    have hh := (bnot_value _ _).mp (h (⟨j-1,by omega⟩ : Fin k))
    rw [powerOneNet_value _ _ _ _ hs hsw (by omega)] at hh
    simpa only [show j-1+1=j by omega] using hh
  · intro h i
    rw [bnot_value,powerOneNet_value _ _ _ _ hs hsw (by have := i.isLt;omega)]
    exact h (i.val+1) (by omega) (by omega)

lemma properDivisor_value (w d : ℕ) (x : Basis w) (hd : d < 2^w) :
    (properDivisor w d).eval x 0=true ↔ d ∣ (bitsValue x).toNat ∧ d < (bitsValue x).toNat := by
  rw [properDivisor,eval_band,Bool.and_eq_true,dividesNet_value _ _ _ hd,
    wordLt_eval,wordConstant_eval,eval_select,Function.comp_id,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hd,decide_eq_true_eq]

lemma noSmallDivisor_value (w B : ℕ) (x : Basis w) (hB : B < 2^w) :
    (noSmallDivisor w B).eval x 0=true ↔
      ∀ d : ℕ, 2 ≤ d → d ≤ B → d < (bitsValue x).toNat → ¬ d ∣ (bitsValue x).toNat := by
  rw [noSmallDivisor,all_ofFn_eval]
  constructor
  · intro h d hd hdB hdm hdiv
    have hh := (bnot_value _ _).mp (h (⟨d-2,by omega⟩ : Fin (B-1)))
    rw [properDivisor_value _ _ _ (by omega)] at hh
    exact hh (by simpa [show d-2+2=d by omega] using And.intro hdiv hdm)
  · intro h i
    rw [bnot_value,properDivisor_value _ _ _ (by have := i.isLt;omega)]
    rintro ⟨hd,hlt⟩
    exact h (i.val+2) (by omega) (by omega) hlt hd

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Strictly smaller 2-adic level makes a divisor divide the half-order. -/
theorem dvd_half_of_level_lt {d r : ℕ} (hr : r ≠ 0) (hdr : d ∣ r)
    (hlevel : padicValNat 2 d < padicValNat 2 r) : d ∣ r / 2 := by
  rcases hdr with ⟨k, rfl⟩
  have hd : d ≠ 0 := left_ne_zero_of_mul hr
  have hk : k ≠ 0 := right_ne_zero_of_mul hr
  rw [padicValNat.mul hd hk] at hlevel
  have htwo : 2 ∣ k := dvd_of_one_le_padicValNat (by omega : 1 ≤ padicValNat 2 k)
  rcases htwo with ⟨t, rfl⟩
  use t
  rw [show d * (2 * t) = (d * t) * 2 by ring, Nat.mul_div_cancel _ (by decide)]

/-- Divisibility cannot increase the 2-adic valuation. -/
theorem level_le_of_dvd {d r : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) :
    padicValNat 2 d ≤ padicValNat 2 r := by
  rcases hdr with ⟨k, rfl⟩
  rw [padicValNat.mul (left_ne_zero_of_mul hr) (right_ne_zero_of_mul hr)]
  omega

/-- A single lower-level component suffices for a proper nontrivial split.
The largest-level component is not assumed to have a chosen generator. -/
theorem splitGcd_proper_of_lower_component {m d : ℕ} (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hdm : d ∣ m) (a : (ZMod m)ˣ)
    (hlevel : padicValNat 2 (orderOf (Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom a))
      < padicValNat 2 (orderOf a)) :
    1 < splitGcd a ∧ splitGcd a < m ∧ splitGcd a ∣ m := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero d := ⟨by omega⟩
  let f : (ZMod m)ˣ →* (ZMod d)ˣ := Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom
  have hr : 0 < orderOf a := orderOf_pos a
  have hhalf : orderOf (f a) ∣ orderOf a / 2 :=
    dvd_half_of_level_lt hr.ne' (orderOf_map_dvd f a) hlevel
  have hreduce : f a ^ (orderOf a / 2) = 1 := orderOf_dvd_iff_pow_eq_one.mp hhalf
  have htwo : 2 ∣ orderOf a := dvd_of_one_le_padicValNat (by omega)
  have hhalfnz : orderOf a / 2 ≠ 0 := by
    have : 2 ≤ orderOf a := Nat.le_of_dvd hr htwo
    omega
  have hglobal : a ^ (orderOf a / 2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf hhalfnz (Nat.div_lt_self hr (by decide))
  have hle : 1 ≤ halfOrderResidue a + m := by omega
  have hcastm : ((halfOrderResidue a + m - 1 : ℕ) : ZMod m) =
      ((a ^ (orderOf a / 2) : (ZMod m)ˣ) : ZMod m) - 1 := by
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, add_zero]
    exact congrArg (fun x : ZMod m => x - 1) (ZMod.natCast_zmod_val _)
  have hcastd : ((halfOrderResidue a + m - 1 : ℕ) : ZMod d) = 0 := by
    have heq : (ZMod.castHom hdm (ZMod d))
        ((a ^ (orderOf a / 2) : (ZMod m)ˣ) : ZMod m) = 1 := by
      have hv := congrArg (fun x : (ZMod d)ˣ => (x : ZMod d)) hreduce
      change (((f a) ^ (orderOf a / 2) : (ZMod d)ˣ) : ZMod d) = 1 at hv
      rw [← map_pow] at hv
      exact hv
    have hz : (m : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff m d).mpr hdm
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one, hz, add_zero]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at heq
    exact sub_eq_zero.mpr heq
  have hdiv : d ∣ halfOrderResidue a + m - 1 :=
    (ZMod.natCast_eq_zero_iff _ _).mp hcastd
  have hnond : ¬ m ∣ halfOrderResidue a + m - 1 := by
    intro h
    have hz := (ZMod.natCast_eq_zero_iff _ m).mpr h
    rw [hcastm] at hz
    exact hglobal (Units.ext (sub_eq_zero.mp hz))
  have hgpos : 0 < splitGcd a := Nat.gcd_pos_of_pos_right _ (by omega)
  have hglower : d ≤ splitGcd a := Nat.le_of_dvd hgpos (Nat.dvd_gcd hdiv hdm)
  have hgupper : splitGcd a ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  have hgneq : splitGcd a ≠ m := by
    intro h
    exact hnond (Nat.gcd_eq_right_iff_dvd.mp h)
  exact ⟨by omega, by omega, Nat.gcd_dvd_right _ _⟩

/-- Two unequal local levels guarantee that one of them is below the global
level, so the verified order always supplies a nontrivial gcd. -/
theorem splitGcd_proper_of_unequal_components {m d e : ℕ} (hm : 2 ≤ m)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hdm : d ∣ m) (hem : e ∣ m) (a : (ZMod m)ˣ)
    (hne : padicValNat 2 (orderOf (Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom a)) ≠
      padicValNat 2 (orderOf (Units.map (ZMod.castHom hem (ZMod e)).toMonoidHom a))) :
    1 < splitGcd a ∧ splitGcd a < m ∧ splitGcd a ∣ m := by
  let : NeZero m := ⟨by omega⟩
  have hr : orderOf a ≠ 0 := (orderOf_pos a).ne'
  have hdle := level_le_of_dvd hr
    (orderOf_map_dvd (Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom) a)
  have hele := level_le_of_dvd hr
    (orderOf_map_dvd (Units.map (ZMod.castHom hem (ZMod e)).toMonoidHom) a)
  rcases lt_or_gt_of_ne hne with h | h
  · exact splitGcd_proper_of_lower_component hm hd hdm a (h.trans_le hele)
  · exact splitGcd_proper_of_lower_component hm he hem a (h.trans_le hdle)

end ExactQuantumFactoring


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

lemma child_even {M d : ℕ} (hd : d ∈ children M) : Even d := by
  obtain ⟨p,hp,_,_,hp2,rfl⟩ := mem_children.mp hd
  have ho := hp.odd_of_ne_two (by omega)
  exact (Nat.even_sub (by omega : 1≤p)).mpr (by simpa using ho)

lemma grandchild_half {M d e : ℕ} (hd : d ∈ children M) (he : e ∈ children d) :
    2*e<M := by
  obtain ⟨p,hp,hpd,hd0,hp2,rfl⟩ := mem_children.mp he
  have hopen := hp.odd_of_ne_two (by omega)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr hopen
  have hdiv := hcop.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp (child_even hd)) hpd
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hdiv
  have hdm := (child_bounds hd).2
  omega

lemma children_prod_le {M : ℕ} (hM : 0<M) : (children M).prod≤M := by
  unfold children
  rw [← List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
  calc
    (∏ p ∈ M.primeFactors.filter (fun p => 2<p), (p-1)) ≤
      ∏ p ∈ M.primeFactors.filter (fun p => 2<p), p :=
      Finset.prod_le_prod' (fun _ _ => Nat.sub_le _ _)
    _ ≤ ∏ p ∈ M.primeFactors, p := Finset.prod_le_prod_of_subset_of_one_le'
      (Finset.filter_subset _ _)
      (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)

lemma level_bounds {M d k : ℕ} (hM : 2≤M) (hd : d ∈ level M k) : 2≤d ∧ d≤M := by
  induction k generalizing M with
  | zero =>
    have he : d=M := by simpa [level] using hd
    subst d
    exact ⟨hM,le_rfl⟩
  | succ k ih =>
    obtain ⟨e,he,hd⟩ := List.mem_flatMap.mp hd
    have hb := child_bounds he
    have hh := ih hb.1 hd
    exact ⟨hh.1,hh.2.trans hb.2.le⟩

lemma level_two_step {M d k : ℕ} (hd : d ∈ level M (2*k)) : 2^k*d≤M := by
  induction k generalizing M with
  | zero =>
    have he : d=M := by simpa [level] using hd
    simpa using he.le
  | succ k ih =>
    have heq : 2*(k+1)=2*k+1+1 := by omega
    rw [heq,level] at hd
    obtain ⟨e,he,hd⟩ := List.mem_flatMap.mp hd
    rw [level] at hd
    obtain ⟨f,hf,hd⟩ := List.mem_flatMap.mp hd
    have hx := ih hd
    have hh := grandchild_half he hf
    rw [pow_succ]
    nlinarith

lemma level_empty {M n : ℕ} (hM : 2≤M) (hbound : M<2^n) : level M (2*n)=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  have hx := level_two_step hd
  have hy := (level_bounds hM hd).1
  have hp : 0<2^n := by positivity
  nlinarith

lemma prod_flatMap (f : ℕ→List ℕ) (xs : List ℕ) :
    (xs.flatMap f).prod=(xs.map (fun x => (f x).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma level_prod_le {M k : ℕ} (hM : 2≤M) : (level M k).prod≤M := by
  induction k generalizing M with
  | zero => simp [level]
  | succ k ih =>
    rw [level,prod_flatMap]
    calc
      ((children M).map (fun d => (level d k).prod)).prod ≤
        ((children M).map id).prod := List.prod_map_le_prod_map₀ _ _
          (fun _ _ => Nat.zero_le _) (fun d hd => ih (child_bounds hd).1)
      _ = (children M).prod := by simp
      _ ≤ M := children_prod_le (by omega)

lemma pow_length_le_prod (xs : List ℕ) (hxs : ∀ x ∈ xs, 2≤x) : 2^xs.length≤xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have hi := ih (fun y hy => hxs y (by simp [hy]))
    simp only [List.length_cons,List.prod_cons,pow_succ]
    exact (Nat.mul_le_mul hi hx).trans_eq (Nat.mul_comm _ _)

lemma level_length_lt {M n k : ℕ} (hM : 2≤M) (hbound : M<2^n) :
    (level M k).length<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  exact (pow_length_le_prod _ (fun _ hd => (level_bounds hM hd).1)).trans_lt
    ((level_prod_le hM).trans_lt hbound)

lemma splitWeight_bound {M n : ℕ} (hM : 0<M) (hbound : M<2^n) : splitWeight M<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  have hh := pow_length_le_prod M.primeFactorsList
    (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
  rw [Nat.prod_primeFactorsList hM.ne'] at hh
  exact hh.trans_lt hbound

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorController
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded, guarded binary factor controller for a single auxiliary-tree node.
Only proper divisors are accepted and primality is tested, never assumed.  The
mathematical prime-factor count is used solely in its termination proof. -/
namespace ExactQuantumFactoring.FactorController
open AuxiliaryTree

lemma ProperDivisor.quotient {m d : ℕ} (h : ProperDivisor m d) :
    2 ≤ m/d ∧ m/d < m ∧ d*(m/d)=m := by
  rcases h with ⟨hd,hdm,hdiv⟩
  have he := Nat.mul_div_cancel' hdiv
  have hp : 0 < m/d := Nat.div_pos (by omega) (by omega)
  have hl : m/d < m := Nat.div_lt_self (by omega) hd
  refine ⟨?_,hl,he⟩
  by_contra hh
  have : m/d=1 := by omega
  rw [this,mul_one] at he
  omega

lemma splitWeight_pos {m : ℕ} (hm : 2 ≤ m) : 0 < splitWeight m := by
  by_contra h
  have hl : m.primeFactorsList=[] := List.length_eq_zero_iff.mp (by
    change splitWeight m=0
    omega)
  have he := Nat.prod_primeFactorsList (by omega : m≠0)
  rw [hl,List.prod_nil] at he
  omega

lemma splitWeight_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    splitWeight (a*b)=splitWeight a+splitWeight b := by
  have hh := (Nat.perm_primeFactorsList_mul ha.ne' hb.ne').length_eq
  simpa only [splitWeight,List.length_append] using hh

lemma splitWeight_split {m d : ℕ} (h : ProperDivisor m d) :
    splitWeight m=splitWeight d+splitWeight (m/d) := by
  have hq := h.quotient
  conv_lhs =>  rw [← hq.2.2]
  exact splitWeight_mul (by have := h.1; omega) (by omega)

lemma weight_prime (m : ℕ) (ms : List ℕ) (hm : m.Prime) :
    weight (m::ms)=weight ms+1 := by
  simp [weight,splitWeight,Nat.primeFactorsList_prime hm,Nat.add_comm]

lemma weight_split {m d : ℕ} (h : ProperDivisor m d) (ms : List ℕ) :
    weight (m::ms)=weight (d::m/d::ms)+1 := by
  have hd := splitWeight_pos (by have := h.1; omega : 2 ≤ d)
  have hq := splitWeight_pos h.quotient.1
  have he := splitWeight_split h
  simp only [weight,List.map_cons,List.sum_cons]
  omega

end ExactQuantumFactoring.FactorController


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FavorableSplit
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

lemma component_modulus_two_lt {m : ℕ} (hm : m≠0) (hodd : Odd m) (p : Component m) :
    2 < p.val^m.factorization p.val := by
  have hp := Nat.mem_primeFactors.mp p.property
  have hp2 : p.val≠2 := by
    intro he
    have hdiv : 2∣m := he ▸ hp.2.1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  exact (lt_of_le_of_ne hp.1.two_le (Ne.symm hp2)).trans_le
    (Nat.le_pow (hp.1.factorization_pos_of_dvd hm hp.2.1))

lemma unitCRT_apply {m : ℕ} (hm : m≠0) (a : (ZMod m)ˣ) (p : Component m) :
    unitCRT m hm a p=Units.map (ZMod.castHom (Nat.ordProj_dvd m p.val)
      (ZMod (p.val^m.factorization p.val))).toMonoidHom a := by
  apply Units.ext
  change ZMod.equivPi m hm (a : ZMod m) p = _
  exact RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun p : Component m => ZMod (p.val^m.factorization p.val)) p).comp
      (ZMod.equivPi m hm).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd m p.val) (ZMod (p.val^m.factorization p.val)))) (a : ZMod m)

/-- A favorable CRT event supplies a proper split from the actual true order. -/
theorem favorable_split {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (hodd : Odd m)
    (p₀ : Component m) (a : (ZMod m)ˣ) (hf : FavorableUnit (by omega : m≠0) hb p₀ a) :
    2 ∣ orderOf a ∧ FactorController.ProperDivisor m (splitGcd a) := by
  classical
  obtain ⟨p,hp⟩ := not_forall.mp hf
  have hneq : padicValNat 2 (orderOf (unitCRT m (by omega) a p)) ≠
      padicValNat 2 (orderOf (unitCRT m (by omega) a p₀)) := by
    exact fun he => hp (Fin.ext he)
  simp only [unitCRT_apply] at hneq
  have hproper := splitGcd_proper_of_unequal_components hm
    (component_modulus_two_lt (by omega) hodd p).le
    (component_modulus_two_lt (by omega) hodd p₀).le
    (Nat.ordProj_dvd m p.val) (Nat.ordProj_dvd m p₀.val) a hneq
  let f := Units.map (ZMod.castHom (Nat.ordProj_dvd m p.val)
    (ZMod (p.val^m.factorization p.val))).toMonoidHom
  let g := Units.map (ZMod.castHom (Nat.ordProj_dvd m p₀.val)
    (ZMod (p₀.val^m.factorization p₀.val))).toMonoidHom
  have hr : orderOf a≠0 := (orderOf_pos a).ne'
  have hp' := level_le_of_dvd hr (orderOf_map_dvd f a)
  have h₀ := level_le_of_dvd hr (orderOf_map_dvd g a)
  have heven : 2∣orderOf a := dvd_of_one_le_padicValNat (by
    change padicValNat 2 (orderOf (f a)) ≠ padicValNat 2 (orderOf (g a)) at hneq
    omega)
  exact ⟨heven,hproper⟩

lemma canonicalUnit_component {m : ℕ} (hm : m≠0) (p₀ p : Component m) :
    unitCRT m hm (canonicalUnit hm p₀) p=if p=p₀ then 1 else -1 := by
  rw [canonicalUnit,MulEquiv.apply_symm_apply]

lemma component_neg_one_order {m : ℕ} (hm : m≠0) (hodd : Odd m) (p : Component m) :
    orderOf (-1 : ComponentUnits m p)=2 := by
  have hd := component_modulus_two_lt hm hodd p
  let : Fact (1 < p.val^m.factorization p.val) := ⟨by omega⟩
  rw [← orderOf_units]
  change orderOf (-1 : ZMod (p.val^m.factorization p.val))=2
  rw [orderOf_neg_one,ringChar.eq _ (p.val^m.factorization p.val),ite_eq_right (by omega)]

lemma canonicalUnit_favorable {m n : ℕ} (hm : m≠0) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) :
    FavorableUnit hm hb p₀ (canonicalUnit hm p₀) := by
  intro h
  have he := congrArg Fin.val (h p₁)
  simp only [componentLevel,canonicalUnit_component,ite_eq_right hne,
    component_neg_one_order hm hodd p₁] at he
  norm_num at he

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BinaryRoots
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

lemma rootSearch_spec {m e : ℕ} (_he : 0 < e) (k guess : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) :
    (rootSearch m e k guess)^e ≤ m ∧ m < (rootSearch m e k guess+1)^e := by
  induction k generalizing guess with
  | zero => simpa only [rootSearch,pow_zero] using And.intro hlo hhi
  | succ k ih =>
    simp only [rootSearch]
    by_cases hnext : (guess+2^k)^e ≤ m
    · rw [ite_eq_left hnext]
      apply ih _ hnext
      have hh : guess+2^k+2^k=guess+2^(k+1) := by rw [pow_succ]; omega
      rw [hh]
      exact hhi
    · rw [ite_eq_right hnext]
      exact ih _ hlo (by omega)

lemma rootSearch_eq {m e : ℕ} (he : 0 < e) (k guess b : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) (hb : b^e=m) :
    rootSearch m e k guess=b := by
  obtain ⟨hl,hh⟩ := rootSearch_spec he k guess hlo hhi
  have hl' : rootSearch m e k guess ≤ b :=
    (Nat.pow_le_pow_iff_left he.ne').mp (hl.trans_eq hb.symm)
  have hh' : b < rootSearch m e k guess+1 :=
    (Nat.pow_lt_pow_iff_left he.ne').mp (hb ▸ hh)
  omega

lemma boundedRoot_spec {m e n : ℕ} (he : 0 < e) (hm : m < 2^n) :
    (boundedRoot m e n)^e ≤ m ∧ m < (boundedRoot m e n+1)^e := by
  apply rootSearch_spec he n 0
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))

lemma boundedRoot_pow_eq {m e n b : ℕ} (he : 0 < e) (hm : m < 2^n) (hb : b^e=m) :
    boundedRoot m e n=b := by
  apply rootSearch_eq he n 0 b
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))
  · exact hb

lemma perfectPower_exponent_lt {m n b e : ℕ} (hm : m < 2^n) (hb : 2 ≤ b)
    (h : b^e=m) : e < n := by
  have hh : 2^e < 2^n := (Nat.pow_le_pow_left hb e).trans_lt (h ▸ hm)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hh

end ExactQuantumFactoring.Primality


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

lemma halfOrderResidue_nat {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) :
    halfOrderResidue u=a^(orderOf u/2)%m := by
  let : NeZero m := ⟨by omega⟩
  simp only [halfOrderResidue,Units.val_pow_eq_pow_val,← ha,← Nat.cast_pow,ZMod.val_natCast]

lemma candidateDivisor_trueOrder {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (heven : 2 ∣ orderOf u) :
    candidateDivisor m a (orderOf u)=splitGcd u := by
  let : NeZero m := ⟨by omega⟩
  rw [candidateDivisor,ite_eq_left ⟨orderOf_pos u,heven⟩,splitGcd,halfOrderResidue_nat hm u ha]

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProvidedSplits
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
open FactorController

lemma firstProper_of_mem {m d : ℕ} {ds : List ℕ} (hd : d∈ds)
    (hp : ProperDivisor m d) : ProperDivisor m (firstProper m ds) := by
  induction ds with
  | nil => simp at hd
  | cons a ds ih =>
    simp only [firstProper]
    split_ifs with ha
    · exact ha
    · rcases List.mem_cons.mp hd with rfl | ht
      · exact False.elim (ha hp)
      · exact ih ht

/-- `ars` are the supplied list entries paired with the recorded order outputs.
When the good list entry has its true order, the actual guarded scan splits. -/
lemma orderSplit_good {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (hodd : Odd m)
    (p₀ : Component m) (ars : List (ℕ×ℕ))
    (u : (ZMod m)ˣ) (hf : FavorableUnit (by omega : m≠0) hb p₀ u)
    (hmem : ((u : ZMod m).val,orderOf u)∈ars) : ProperDivisor m (orderSplit m ars) := by
  let : NeZero m := ⟨by omega⟩
  have hh := favorable_split hm hb hodd p₀ u hf
  have he : candidateDivisor m (u : ZMod m).val (orderOf u)=splitGcd u :=
    candidateDivisor_trueOrder hm u (ZMod.natCast_zmod_val _) hh.1
  apply firstProper_of_mem (List.mem_map.mpr ⟨_,hmem,rfl⟩)
  exact he ▸ hh.2

lemma perfectPower_proper {m b e : ℕ} (hb : 2 ≤ b) (he : 2 ≤ e) (hp : b^e=m) :
    ProperDivisor m b := by
  rcases e with _ | e
  · omega
  have he0 : 0 < e := by omega
  have hpow : 1 < b^e := by exact one_lt_pow₀ (by omega) (by omega)
  refine ⟨by omega,?_,?_⟩
  · rw [← hp,pow_succ]
    nlinarith
  · rw [← hp,pow_succ]
    exact dvd_mul_left b (b^e)

lemma rootSplit_good {m n : ℕ} (hb : m < 2^n) (hp : Primality.PerfectPower m) :
    ProperDivisor m (rootSplit m n) := by
  obtain ⟨b,e,hb2,he,hpow⟩ := hp
  have hen := Primality.perfectPower_exponent_lt hb hb2 hpow
  have hroot := Primality.boundedRoot_pow_eq (by omega : 0 < e) hb hpow
  apply firstProper_of_mem (d:=b)
  · apply List.mem_map.mpr
    refine ⟨e,List.mem_range.mpr (by omega),hroot⟩
  · exact perfectPower_proper hb2 he hpow

lemma suppliedDivisor_good {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (hprime : ¬m.Prime)
    (ars : List (ℕ×ℕ))
    (hgood : Odd m → ¬Primality.PerfectPower m →
      ∃ (p₀ : Component m) (u : (ZMod m)ˣ),
        FavorableUnit (by omega : m≠0) hb p₀ u ∧ ((u : ZMod m).val,orderOf u)∈ars) :
    ProperDivisor m (suppliedDivisor m n ars) := by
  simp only [suppliedDivisor]
  split_ifs with htwo hroot
  · refine ⟨by decide,?_,htwo⟩
    by_contra h
    have : m=2 := by omega
    exact hprime (this ▸ Nat.prime_two)
  · exact hroot
  · have hodd : Odd m := Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using htwo)
    have hpow : ¬Primality.PerfectPower m := fun hp => hroot (rootSplit_good hb hp)
    obtain ⟨p₀,u,hf,hu⟩ := hgood hodd hpow
    exact orderSplit_good hm hb hodd p₀ ars u hf hu

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AuxiliaryProducer
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
open AuxiliaryTree FactorController

namespace DataProducer

lemma child_level_empty {m depth d : ℕ} (h : level m (depth+1)=[]) (hd : d∈children m) :
    level d depth=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e he
  have hh : e∈level m (depth+1) := List.mem_flatMap.mpr ⟨d,hd,he⟩
  rw [h] at hh
  exact List.not_mem_nil hh

end DataProducer
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicAlgebra
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

lemma cyclic_mul_coeff {R : Type*} [Semiring R] {s : ℕ} [NeZero s]
    (a b : Cyclic R s) (k : Fin s) :
    (a*b).coeff k = ∑ i : Fin s, a.coeff i * b.coeff (k-i) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum_fintype]
  · congr 1
    ext i
    rw [sub_eq_add_neg,add_comm k]
  · intro i
    simp

lemma cyclicC_nat {R : Type*} [Semiring R] (s : ℕ) [NeZero s] (a : ℕ) :
    cyclicC s (a : R) = (a : Cyclic R s) := by
  induction a with
  | zero => simp [cyclicC]
  | succ a ih =>
    rw [Nat.cast_succ,Nat.cast_succ,← ih]
    simp [cyclicC,AddMonoidAlgebra.single_add,AddMonoidAlgebra.one_def]

/-- Primes satisfy the literal cyclic-array test by characteristic-p Frobenius. -/
lemma cyclic_prime_test {m s : ℕ} [NeZero s] (hm : m.Prime) (a : ℕ) :
    (cyclicX (R := ZMod m) s + cyclicC s (a : ZMod m))^m =
      cyclicX s ^m + cyclicC s (a : ZMod m) := by
  let : Fact m.Prime := ⟨hm⟩
  let : CharP (Cyclic (ZMod m) s) m :=
    charP_of_injective_ringHom (f := AddMonoidAlgebra.singleZeroRingHom)
      AddMonoidAlgebra.single_right_injective m
  rw [cyclicC_nat,add_pow_char,natCast_frobenius]

lemma cyclicEval_X {R F : Type*} [Semiring R] [CommRing F]
    {s : ℕ} [NeZero s] (hs : 2 ≤ s) (f : R →+* F) (z : F) (hz : z^s=1) :
    cyclicEval f z hz (cyclicX s) = z := by
  simp [cyclicEval,cyclicX,rootPower, Nat.mod_eq_of_lt (by omega : 1 < s)]

lemma cyclicEval_C {R F : Type*} [Semiring R] [CommRing F]
    {s : ℕ} [NeZero s] (f : R →+* F) (z : F) (hz : z^s=1) (a : R) :
    cyclicEval f z hz (cyclicC s a) = f a := by
  simp [cyclicEval,cyclicC,rootPower]

/-- Equality of the two concrete coefficient arrays gives exactly the
introspective identity needed by the appendix's root-count contradiction. -/
lemma cyclic_test_introspective {F : Type*} [Field F] {m s p a : ℕ}
    [NeZero s] [CharP F p] (hs : 2 ≤ s) (hpm : p ∣ m)
    (h : (cyclicX (R := ZMod m) s + cyclicC s (a : ZMod m))^m =
      cyclicX s ^m + cyclicC s (a : ZMod m)) :
    Introspective s m (Polynomial.X+Polynomial.C (a : F)) := by
  intro z hz
  have hh := congrArg (cyclicEval (ZMod.castHom hpm F) z hz) h
  simpa only [map_pow,map_add,cyclicEval_X hs,cyclicEval_C,map_natCast,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_natCast] using hh

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicPrimality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality

theorem cyclic_large_branch_prime {n m s : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n)
    [NeZero s] (hs : s.Prime) (hcop : s.Coprime m) (horder : n^2 < orderOf (m : ZMod s))
    (hpow : ¬ PerfectPower m)
    (hsmall : ∀ d : ℕ, 2 ≤ d → d ≤ 8*s → ¬ d ∣ m)
    (htest : ∀ a : ℕ, 1 ≤ a → a ≤ 8*s →
      (cyclicX (R := ZMod m) s+cyclicC s (a : ZMod m))^m=
        cyclicX s^m+cyclicC s (a : ZMod m)) : m.Prime := by
  by_contra hcom
  obtain ⟨p,hp,hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  obtain ⟨q,hq,hqm,hpq⟩ := other_prime_divisor hm hcom hpow hp hpm
  let : Fact s.Prime := ⟨hs⟩
  let : Fact p.Prime := ⟨hp⟩
  have hpbig : 8*s < p := by
    by_contra h
    exact hsmall p hp.two_le (by omega) hpm
  have hms : (m : ZMod s) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (hs.coprime_iff_not_dvd).mp hcop
  have hps : (p : ZMod s) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hs hp).mp hd
    nlinarith [hs.two_le]
  have hsp : (s : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hs.pos (by nlinarith)
  let : NeZero (s : ZMod p) := ⟨hsp⟩
  obtain ⟨w,hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod p)) s
  exact root_count_contradiction (by omega) hm hmb hms hps hpbig hpm hq hqm hpq horder hw
    (fun a ha hb => cyclic_test_introspective hs.two_le hpm (htest a ha hb))


end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordBlocks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

lemma wordBlocks_eval {n s w : ℕ} (f : Fin s → BooleanNetwork n w) (x : Basis n) (i : Fin s) :
    block ((wordBlocks f).eval x) i=(f i).eval x := by
  funext j
  simp only [block,wordBlocks,eval_vector,eval_rewire,Function.comp_apply,Equiv.symm_apply_apply]

lemma addMod_value {n w : ℕ} (a b m : BooleanNetwork n w) (x : Basis n)
    (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((addMod a b m).eval x)).toNat =
      ((bitsValue (a.eval x)).toNat+(bitsValue (b.eval x)).toNat)%
        (bitsValue (m.eval x)).toNat := by
  simp only [addMod,eval_rewire,eval_comp,eval_pair]
  rw [bitsValue_take,mod_word,BitVec.toNat_setWidth,BitVec.toNat_umod,add_word,BitVec.toNat_add]
  simp only [padRight_word,setWidth_toNat_of_le (by omega : w ≤ w+1)]
  have hp : (bitsValue (a.eval x)).toNat+(bitsValue (b.eval x)).toNat < 2^(w+1) := by
    rw [pow_succ]
    have ha := (bitsValue (a.eval x)).isLt
    have hb := (bitsValue (b.eval x)).isLt
    omega
  rw [Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt]
  exact (Nat.mod_lt _ hm).trans (bitsValue (m.eval x)).isLt

lemma sumMod_value {n w : ℕ} (m : BooleanNetwork n w) (as : List (BooleanNetwork n w))
    (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((sumMod m as).eval x)).toNat =
      (as.map (fun a => (bitsValue (a.eval x)).toNat)).sum%(bitsValue (m.eval x)).toNat := by
  induction as with
  | nil => simp [sumMod,wordConstant_eval]
  | cons a as ih =>
    rw [sumMod,addMod_value _ _ _ _ hm,ih]
    simp only [List.map_cons,List.sum_cons,Nat.add_mod_mod]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

lemma cyclicMulNet_value {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat)
    (k : Fin s) :
    (bitsValue (block ((cyclicMulNet a b m).eval x) k)).toNat =
      (∑ i : Fin s, (bitsValue (block (a.eval x) i)).toNat *
        (bitsValue (block (b.eval x) (k-i))).toNat) % (bitsValue (m.eval x)).toNat := by
  rw [cyclicMulNet,wordBlocks_eval,sumMod_value _ _ _ hm]
  simp only [List.map_ofFn,List.sum_ofFn]
  have hh : ∀ i : Fin s, (bitsValue ((cyclicTerm a b m k i).eval x)).toNat =
      ((bitsValue (block (a.eval x) i)).toNat *
        (bitsValue (block (b.eval x) (k-i))).toNat) % (bitsValue (m.eval x)).toNat := by
    intro i
    rw [cyclicTerm,mulMod_word _ _ _ _ hm]
    simp only [eval_comp,blockNet_eval]
  simp only [Function.comp_apply]
  simp_rw [hh]
  exact (Finset.sum_nat_mod _ _ _).symm

lemma cyclicMulNet_correct {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    decodeCyclic (bitsValue (m.eval x)).toNat ((cyclicMulNet a b m).eval x) =
      decodeCyclic (bitsValue (m.eval x)).toNat (a.eval x)*
        decodeCyclic (bitsValue (m.eval x)).toNat (b.eval x) := by
  ext k
  rw [decodeCyclic_coeff,cyclicMulNet_value _ _ _ _ hm,cyclic_mul_coeff]
  simp only [ZMod.natCast_mod,Nat.cast_sum,Nat.cast_mul,decodeCyclic_coeff]

lemma cyclicMulNet_canonical {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    CanonicalCyclic (bitsValue (m.eval x)).toNat ((cyclicMulNet a b m).eval x) := by
  intro k
  rw [cyclicMulNet_value _ _ _ _ hm]
  exact Nat.mod_lt _ hm

lemma decodeCyclic_injective {s w m : ℕ} (hm : 0 < m) {a b : Basis (s*w)}
    (ha : CanonicalCyclic m a) (hb : CanonicalCyclic m b)
    (hh : decodeCyclic m a=decodeCyclic m b) : a=b := by
  let : NeZero m := ⟨by omega⟩
  have hv : ∀ i : Fin s, bitsValue (block a i)=bitsValue (block b i) := by
    intro i
    have he := congrArg (fun c : Cyclic (ZMod m) s => (c.coeff i).val) hh
    simp only [decodeCyclic_coeff,ZMod.val_natCast,Nat.mod_eq_of_lt (ha i),
      Nat.mod_eq_of_lt (hb i)] at he
    exact BitVec.eq_of_toNat_eq he
  funext k
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective k
  have he := congrArg (fun v : BitVec w => v.getLsbD j.val) (hv i)
  simpa only [bitsValue_bit,block] using he

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicConstants
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

lemma arrayConstant_value {n s w : ℕ} (f : Fin s → ℕ) (x : Basis n) (i : Fin s) :
    (bitsValue (block ((arrayConstant s w f).eval x) i)).toNat = f i % 2^w := by
  rw [arrayConstant,wordBlocks_eval,wordConstant_eval,BitVec.toNat_ofNat]

lemma cyclicOne_value {n s w m : ℕ} [NeZero s] (hw : 0 < w) (x : Basis n) :
    decodeCyclic m ((cyclicOne s w).eval x)=1 := by
  have hp : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  ext i
  rw [decodeCyclic_coeff,cyclicOne,arrayConstant_value,AddMonoidAlgebra.one_def]
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> simp_all [Nat.mod_eq_of_lt hp]

lemma cyclicOne_canonical {n s w m : ℕ} [NeZero s] (hm : 2 ≤ m) (x : Basis n) :
    CanonicalCyclic m ((cyclicOne s w).eval x) := by
  intro i
  rw [cyclicOne,arrayConstant_value]
  split_ifs
  · exact (Nat.mod_le _ _).trans_lt (by omega)
  · simp only [Nat.zero_mod]
    omega

lemma cyclicAddNet_value {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat)
    (i : Fin s) :
    (bitsValue (block ((cyclicAddNet a b m).eval x) i)).toNat =
      ((bitsValue (block (a.eval x) i)).toNat+(bitsValue (block (b.eval x) i)).toNat)%
        (bitsValue (m.eval x)).toNat := by
  rw [cyclicAddNet,wordBlocks_eval,addMod_value _ _ _ _ hm]
  simp only [eval_comp,blockNet_eval]

lemma cyclicAddNet_correct {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    decodeCyclic (bitsValue (m.eval x)).toNat ((cyclicAddNet a b m).eval x) =
      decodeCyclic (bitsValue (m.eval x)).toNat (a.eval x)+
        decodeCyclic (bitsValue (m.eval x)).toNat (b.eval x) := by
  ext i
  rw [decodeCyclic_coeff,cyclicAddNet_value _ _ _ _ hm]
  simp [ZMod.natCast_mod,decodeCyclic_coeff]

lemma cyclicAddNet_canonical {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    CanonicalCyclic (bitsValue (m.eval x)).toNat ((cyclicAddNet a b m).eval x) := by
  intro i
  rw [cyclicAddNet_value _ _ _ _ hm]
  exact Nat.mod_lt _ hm

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicPowerCircuit
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
open BooleanNetwork Primality

lemma cyclicStep_pack {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) :
    (cyclicStep s w i).eval (cyclicPack a m e z)=
      cyclicPack a m e ((cyclicNew s w i).eval (cyclicPack a m e z)) := by
  simp only [cyclicStep,eval_pair,eval_select,cyclicPack]
  congr 1
  funext j
  exact Fin.append_left _ _ j

lemma cyclicNew_value {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) (hm : 0 < (bitsValue m).toNat) :
    decodeCyclic (bitsValue m).toNat ((cyclicNew s w i).eval (cyclicPack a m e z)) =
      if e i then decodeCyclic (bitsValue m).toNat z ^ 2 * decodeCyclic (bitsValue m).toNat a
        else decodeCyclic (bitsValue m).toNat z ^ 2 := by
  have hm' : 0 < (bitsValue ((cyclicMod s w b).eval (cyclicPack a m e z))).toNat := by
    simpa only [cyclicMod_eval] using hm
  have hs := cyclicMulNet_correct (cyclicAcc s w b) (cyclicAcc s w b)
    (cyclicMod s w b) (cyclicPack a m e z) hm'
  have hp := cyclicMulNet_correct
    (cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b))
    (cyclicBase s w b) (cyclicMod s w b) (cyclicPack a m e z) hm'
  rw [cyclicMod_eval] at hs hp
  simp only [cyclicAcc_eval,cyclicBase_eval] at hs hp
  rw [cyclicNew,wordMux_eval,cyclicBit_eval]
  split
  · rw [hp,hs,pow_two]
  · rw [hs,pow_two]

lemma cyclicNew_canonical {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) (hm : 0 < (bitsValue m).toNat) :
    CanonicalCyclic (bitsValue m).toNat ((cyclicNew s w i).eval (cyclicPack a m e z)) := by
  have hm' : 0 < (bitsValue ((cyclicMod s w b).eval (cyclicPack a m e z))).toNat := by
    simpa only [cyclicMod_eval] using hm
  rw [cyclicNew,wordMux_eval,cyclicBit_eval]
  split <;>
    simpa only [cyclicMod_eval] using (cyclicMulNet_canonical _ _ _ _ hm')

lemma cyclicPrefix_value {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z₀ : Basis (s*w)) (hm : 0 < (bitsValue m).toNat)
    (h₀ : decodeCyclic (bitsValue m).toNat z₀=1) (hc : CanonicalCyclic (bitsValue m).toNat z₀)
    (k : ℕ) (hk : k ≤ b) :
    ∃ z : Basis (s*w), (cyclicPrefix s w b k hk).eval (cyclicPack a m e z₀)=cyclicPack a m e z ∧
      decodeCyclic (bitsValue m).toNat z=decodeCyclic (bitsValue m).toNat a ^horner e k hk ∧
      CanonicalCyclic (bitsValue m).toNat z := by
  induction k with
  | zero => exact ⟨z₀,by simp [cyclicPrefix],by simpa only [horner,pow_zero] using h₀,hc⟩
  | succ k ih =>
    obtain ⟨z,hz,hv,_hzc⟩ := ih (by omega)
    refine ⟨(cyclicNew s w ⟨k,by omega⟩).eval (cyclicPack a m e z),?_,?_,
      cyclicNew_canonical _ _ _ _ _ hm⟩
    · rw [cyclicPrefix,eval_comp,hz,cyclicStep_pack]
    · rw [cyclicNew_value _ _ _ _ _ hm,hv]
      cases he : e (⟨k,by omega⟩ : Fin b)
      · simp only [horner,he,Bool.false_eq_true,ite_false, if_false,Bool.toNat_false,Nat.add_zero]
        rw [← pow_mul,Nat.mul_comm (horner e k _) 2]
      · simp only [horner,he,ite_true, if_true,Bool.toNat_true]
        rw [← pow_mul,pow_succ,Nat.mul_comm (horner e k _) 2]

lemma cyclicPower_value {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (hw : 0 < w) (hm : 2 ≤ (bitsValue m).toNat) :
    decodeCyclic (bitsValue m).toNat ((cyclicPower s w b).eval (Fin.append (Fin.append a m) e))=
      decodeCyclic (bitsValue m).toNat a ^ horner e b le_rfl ∧
    CanonicalCyclic (bitsValue m).toNat ((cyclicPower s w b).eval (Fin.append (Fin.append a m) e)) := by
  let input := Fin.append (Fin.append a m) e
  obtain ⟨z,hz,hv,hc⟩ := cyclicPrefix_value a m e ((cyclicOne s w).eval input)
    (by omega) (cyclicOne_value hw input) (cyclicOne_canonical hm input) b le_rfl
  have he : (cyclicPower s w b).eval input=z := by
    simp only [cyclicPower,eval_comp,eval_rewire,eval_pair,eval_select,Function.comp_id]
    change ((cyclicPrefix s w b b le_rfl).eval
      (cyclicPack a m e ((cyclicOne s w).eval input))) ∘ Fin.natAdd ((s*w+w)+b)=z
    rw [hz]
    funext i
    exact Fin.append_right _ _ i
  change decodeCyclic (bitsValue m).toNat ((cyclicPower s w b).eval input)=_ ∧
    CanonicalCyclic (bitsValue m).toNat ((cyclicPower s w b).eval input)
  rw [he]
  exact ⟨hv,hc⟩

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicTestCircuit
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
open BooleanNetwork Primality

lemma arrayConstant_decode {n s w m : ℕ} (f : Fin s → ℕ)
    (hf : ∀ i, f i < 2^w) (x : Basis n) :
    decodeCyclic m ((arrayConstant s w f).eval x)=cyclicOf (fun i => (f i : ZMod m)) := by
  ext i
  rw [decodeCyclic_coeff,arrayConstant_value,cyclicOf_coeff,Nat.mod_eq_of_lt (hf i)]

lemma cyclicXNet_value {n s w m : ℕ} [NeZero s] (hw : 0 < w) (x : Basis n) :
    decodeCyclic m ((cyclicXNet s w).eval x)=cyclicX s := by
  have hp : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  unfold cyclicXNet
  rw [arrayConstant_decode _ (by intro i; split_ifs <;> omega)]
  ext i
  simp only [cyclicOf_coeff,cyclicX,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> simp_all

lemma cyclicCNet_value {n s w m a : ℕ} [NeZero s] (ha : a < 2^w) (x : Basis n) :
    decodeCyclic m ((cyclicCNet s w a).eval x)=cyclicC s (a : ZMod m) := by
  unfold cyclicCNet
  rw [arrayConstant_decode _ (by intro i; split_ifs <;> omega)]
  ext i
  simp only [cyclicOf_coeff,cyclicC,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> simp_all

lemma cyclicPowerOn_value {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) (x : Basis n)
    (hw : 0 < w) (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    decodeCyclic (bitsValue (m.eval x)).toNat ((cyclicPowerOn a m e).eval x)=
      decodeCyclic (bitsValue (m.eval x)).toNat (a.eval x)^horner (e.eval x) b le_rfl ∧
    CanonicalCyclic (bitsValue (m.eval x)).toNat ((cyclicPowerOn a m e).eval x) := by
  simpa only [cyclicPowerOn,eval_comp,eval_pair] using
    cyclicPower_value (a.eval x) (m.eval x) (e.eval x) hw hm

lemma horner_reverse {w : ℕ} (x : Basis w) :
    horner (x ∘ Fin.rev) w le_rfl = (bitsValue x).toNat := by
  rw [horner_full,Triangular.inputNumber_reverse]
  congr 2
  funext i
  simp [reverseBits]

lemma cyclicTest_correct (s w a : ℕ) [NeZero s] (x : Basis w)
    (hw : 0 < w) (hm : 2 ≤ (bitsValue x).toNat) (ha : a < 2^w) :
    (cyclicTest s w a).eval x 0=true ↔
      (cyclicX s+cyclicC s (a : ZMod (bitsValue x).toNat) : Cyclic (ZMod (bitsValue x).toNat) s)^
        (bitsValue x).toNat = cyclicX s^(bitsValue x).toNat+cyclicC s (a : ZMod (bitsValue x).toNat) := by
  let m : BooleanNetwork w w := select id
  let e : BooleanNetwork w w := select Fin.rev
  let X : BooleanNetwork w (s*w) := cyclicXNet s w
  let C : BooleanNetwork w (s*w) := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  have hm' : 2 ≤ (bitsValue (m.eval x)).toNat := hm
  have hl := cyclicPowerOn_value (cyclicAddNet X C m) m e x hw hm'
  have hX := cyclicPowerOn_value X m e x hw hm'
  have ha' := cyclicAddNet_correct X C m x (by omega)
  have hr := cyclicAddNet_correct (cyclicPowerOn X m e) C m x (by omega)
  have hrc := cyclicAddNet_canonical (cyclicPowerOn X m e) C m x (by omega)
  have he : horner (e.eval x) w le_rfl=(bitsValue x).toNat := horner_reverse x
  have hx : decodeCyclic (bitsValue (m.eval x)).toNat (X.eval x)=cyclicX s := cyclicXNet_value hw x
  have hc : decodeCyclic (bitsValue x).toNat (C.eval x)=cyclicC s (a : ZMod (bitsValue x).toNat) :=
    cyclicCNet_value ha x
  have hmval : m.eval x=x := by simp [m]
  rw [hmval] at hl hX ha' hr hrc hx
  have hleft : decodeCyclic (bitsValue x).toNat (lhs.eval x)=
      (cyclicX s+cyclicC s (a : ZMod (bitsValue x).toNat))^(bitsValue x).toNat := by
    change decodeCyclic (bitsValue x).toNat ((cyclicPowerOn (cyclicAddNet X C m) m e).eval x)=_
    rw [hl.1,ha',hx,hc,he]
  have hright : decodeCyclic (bitsValue x).toNat (rhs.eval x)=
      cyclicX s^(bitsValue x).toNat+cyclicC s (a : ZMod (bitsValue x).toNat) := by
    change decodeCyclic (bitsValue x).toNat ((cyclicAddNet (cyclicPowerOn X m e) C m).eval x)=_
    rw [hr,hX.1,hx,hc,he]
  change ((lhs.pair rhs).comp (wordEq (s*w))).eval x 0=true ↔ _
  rw [eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  rw [show bitsValue (lhs.eval x)=bitsValue (rhs.eval x) ↔ lhs.eval x=rhs.eval x from
    (bitsEquiv (s*w)).injective.eq_iff]
  constructor
  · intro h
    have hh := congrArg (decodeCyclic (bitsValue x).toNat) h
    simpa only [hleft,hright] using hh
  · intro h
    apply decodeCyclic_injective (by omega) hl.2 hrc
    change decodeCyclic (bitsValue x).toNat (lhs.eval x)=decodeCyclic (bitsValue x).toNat (rhs.eval x)
    rw [hleft,hright]
    exact h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PerfectPowerCircuit
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

lemma rootCheck_eval (w e : ℕ) (m g : Basis w) :
    (rootCheck w e).eval (Fin.append m g) 0=true ↔
      2 % 2^w ≤ (bitsValue g).toNat ∧
        (bitsValue g).toNat^e % 2^w = (bitsValue m).toNat := by
  rw [rootCheck,eval_band,wordLe_eval,wordConstant_eval,rootGuess_eval,
    eval_comp,eval_pair,wordEq_eval,eval_comp,staticPower_eval,rootGuess_eval,rootModulus_eval]
  simp only [Bool.and_eq_true,decide_eq_true_eq,BitVec.toNat_ofNat]
  constructor
  · rintro ⟨hle,h⟩
    refine ⟨hle,?_⟩
    simpa only [BitVec.toNat_pow] using congrArg BitVec.toNat h
  · rintro ⟨hle,h⟩
    refine ⟨hle,?_⟩
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_pow] using h

lemma exponentCheck_eval {n e : ℕ} (hn : 2 ≤ n) (he : 2 ≤ e) (hen : e ≤ n)
    (m : Basis (rootWidth n)) (hm : (bitsValue m).toNat < 2^n) :
    (exponentCheck n e).eval m 0=true ↔
      2 ≤ Primality.boundedRoot (bitsValue m).toNat e n ∧
      (Primality.boundedRoot (bitsValue m).toNat e n)^e=(bitsValue m).toNat := by
  rw [exponentCheck,eval_comp,eval_pair,eval_select,Function.comp_id,rootCheck_eval,
    boundedRootNet_value n e hen]
  have hp : 2 < 2^(rootWidth n) := by
    have hh : 1 < rootWidth n := by dsimp [rootWidth] <;> nlinarith
    exact lt_of_eq_of_lt (by norm_num : 2=2^1) (Nat.pow_lt_pow_right (by decide) hh)
  have hroot := (Primality.boundedRoot_spec (by omega : 0 < e) hm).1
  have hmn : n ≤ rootWidth n := by dsimp [rootWidth] <;> nlinarith
  rw [Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt
    (hroot.trans_lt (hm.trans_le (Nat.pow_le_pow_right (by decide) hmn)))]

/-- The complete first AKS rejection check, as an actual polynomial-size
Boolean circuit: exponents2..n and n exact bounded binary-root steps each. -/
theorem perfectPowerNet_correct {n : ℕ} (hn : 2 ≤ n) (m : Basis (rootWidth n))
    (hm : (bitsValue m).toNat < 2^n) :
    (perfectPowerNet n).eval m 0=true ↔ Primality.PerfectPower (bitsValue m).toNat := by
  rw [perfectPowerNet,any_eval]
  constructor
  · rintro ⟨c,hc,hv⟩
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hc
    by_cases he : 2 ≤ e.val
    · rw [ite_eq_left he] at hv
      have hh := (exponentCheck_eval hn he (by omega) m hm).mp hv
      exact ⟨_,e.val,hh.1,he,hh.2⟩
    · simp [he] at hv
  · rintro ⟨b,e,hb,he,hbm⟩
    have hen : e < n := Primality.perfectPower_exponent_lt hm hb hbm
    have hr := Primality.boundedRoot_pow_eq (by omega : 0 < e) hm hbm
    refine ⟨exponentCheck n e,?_,?_⟩
    · apply List.mem_ofFn.mpr
      exact ⟨⟨e,by omega⟩,ite_eq_left he⟩
    · rw [exponentCheck_eval hn he (by omega) m hm,hr]
      exact ⟨hb,hbm⟩

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityAuxiliaryPrime
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

/-- A quantitative bound at the manuscript's unchanged cutoff n^8. We reuse
Mathlib's proved Chebyshev bound instead of repeating its binomial argument. -/
lemma primorial_gt_cutoff {n : ℕ} (hn : 128 ≤ n) :
    2^(n^6) < primorial (n^8) := by
  have hnR : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hl2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hlog8 : Real.log ((n : ℝ)^8+1) ≤ 1+8*(n : ℝ) := by
    have h8 : (1 : ℝ) ≤ (n : ℝ)^8 := one_le_pow₀ hn1
    calc
      Real.log ((n : ℝ)^8+1) ≤ Real.log (2*(n : ℝ)^8) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + 8*Real.log (n : ℝ) := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      _ ≤ 1+8*(n : ℝ) := by linarith
  have hsqrt : Real.sqrt ((n : ℝ)^8) = (n : ℝ)^4 := by
    rw [show (n : ℝ)^8 = ((n : ℝ)^4)^2 by ring, Real.sqrt_sq (by positivity)]
  have ht := Chebyshev.theta_ge (n^8)
  simp only [Nat.cast_pow, hsqrt, Real.log_pow, Nat.cast_ofNat] at ht
  have h6pos : (0 : ℝ) < (n : ℝ)^6 := by positivity
  have h6one : (1 : ℝ) ≤ (n : ℝ)^6 := one_le_pow₀ hn1
  have hn6 : (n : ℝ) ≤ (n : ℝ)^6 := le_self_pow₀ hn1 (by decide : 6 ≠ 0)
  have h56 : (n : ℝ)^5 ≤ (n : ℝ)^6 := pow_le_pow_right₀ hn1 (by decide)
  have h86 : (128 : ℝ)^2*(n : ℝ)^6 ≤ (n : ℝ)^8 := by
    calc
      (128 : ℝ)^2*(n : ℝ)^6 ≤ (n : ℝ)^2*(n : ℝ)^6 := by gcongr
      _ = (n : ℝ)^8 := by ring
  have hmain : (n : ℝ)^6 < Chebyshev.theta (n^8) := by
    have hmul := mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ (n : ℝ)^8 by positivity)
    have hlogmul := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 16*(n : ℝ)^4 by positivity)
    have hlogmul' : 16*(n : ℝ)^4*Real.log (n : ℝ) ≤ 16*(n : ℝ)^5 := by
      calc
        _ ≤ 16*(n : ℝ)^4*(n : ℝ) := hlogmul
        _ = _ := by ring
    nlinarith only [ht, hmul, hlogmul', hlog8, h86, h6one, hn6, h56]
  have hlogpow : Real.log ((2^(n^6) : ℕ) : ℝ) <
      Real.log (primorial (n^8) : ℝ) := by
    rw [Chebyshev.theta_eq_log_primorial] at hmain
    simp only [← Nat.cast_pow, Nat.floor_natCast] at hmain
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    exact (mul_lt_mul_of_pos_left hl2' h6pos).trans_le (by simpa only [Nat.cast_pow, mul_one] using hmain.le)
  have := (Real.log_lt_log_iff (by positivity) (by exact_mod_cast primorial_pos (n^8))).mp hlogpow
  exact_mod_cast this

lemma badProduct_pos {n m : ℕ} (hm : 2 ≤ m) : 0 < badProduct n m := by
  apply Nat.mul_pos (by omega)
  apply Finset.prod_pos
  intro j hj
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjm : 2 ≤ m^j := by
    exact hm.trans (Nat.le_pow (by omega))
  omega

lemma badProduct_lt_cutoff {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n) :
    badProduct n m < 2^(n^6) := by
  have hp : ∏ j ∈ Finset.Icc 1 (n^2), (m^j-1) ≤ m^(n^4) := by
    calc
      ∏ j ∈ Finset.Icc 1 (n^2), (m^j-1) ≤ ∏ _j ∈ Finset.Icc 1 (n^2), m^(n^2) := by
        apply Finset.prod_le_prod'
        intro j hj
        exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) (Finset.mem_Icc.mp hj).2)
      _ = m^(n^4) := by simp [← pow_mul]; congr 1; ring
  have hexp : n*(1+n^4) < n^6 := by
    have hn1 : 1 ≤ n := by omega
    have hn4 : 1 ≤ n^4 := Nat.one_le_pow _ _ hn1
    have hn2 : 2*n ≤ n^2 := by nlinarith
    have h56 : n^5 < n^6 := Nat.pow_lt_pow_right (by omega) (by decide)
    have h46 : 2*n^5 ≤ n^6 := by
      calc
        2*n^5 = (2*n)*n^4 := by ring
        _ ≤ n^2*n^4 := Nat.mul_le_mul_right _ hn2
        _ = n^6 := by ring
    have hn5 : n < n^5 := by simpa using Nat.pow_lt_pow_right (by omega : 1 < n) (by decide : 1 < 5)
    nlinarith
  calc
    badProduct n m ≤ m^(1+n^4) := by simpa [badProduct, pow_add] using Nat.mul_le_mul_left m hp
    _ < (2^n)^(1+n^4) := Nat.pow_lt_pow_left hmb (by omega)
    _ = 2^(n*(1+n^4)) := (pow_mul _ _ _).symm
    _ < 2^(n^6) := Nat.pow_lt_pow_right (by decide) hexp

/-- The auxiliary prime searched for by the source algorithm exists within n^8;
no number-theoretic existence oracle is included in the algorithm. -/
theorem auxiliary_prime_exists {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n) :
    ∃ s : ℕ, s.Prime ∧ s ≤ n^8 ∧ s.Coprime m ∧ n^2 < orderOf (m : ZMod s) := by
  have hpgt := primorial_gt_cutoff hn
  have hb := badProduct_lt_cutoff hn hm hmb
  have hex : ∃ s ∈ Nat.primesLE (n^8), ¬ s ∣ badProduct n m := by
    by_contra h
    have hall : ∀ s ∈ Nat.primesLE (n^8), s ∣ badProduct n m := by simpa using h
    have hd : primorial (n^8) ∣ badProduct n m := by
      rw [primorial_eq_prod_primesLE]
      exact Finset.prod_primes_dvd _ (fun s hs => (Nat.mem_primesLE.mp hs).2.prime) hall
    exact (not_lt_of_ge (Nat.le_of_dvd (badProduct_pos hm) hd)) (hb.trans hpgt)
  obtain ⟨s,hs,hbad⟩ := hex
  have hs' := (Nat.mem_primesLE.mp hs).2
  have hsm : ¬ s ∣ m := fun hd => hbad (dvd_mul_of_dvd_left hd _)
  have hcop := hs'.coprime_iff_not_dvd.mpr hsm
  refine ⟨s,hs',(Nat.mem_primesLE.mp hs).1,hcop,?_⟩
  let : Fact s.Prime := ⟨hs'⟩
  have hopos : 0 < orderOf (m : ZMod s) :=
    ((ZMod.isUnit_iff_coprime m s).mpr hcop.symm).isOfFinOrder.orderOf_pos
  by_contra h
  have ho : orderOf (m : ZMod s) ∈ Finset.Icc 1 (n^2) := Finset.mem_Icc.mpr ⟨hopos,by omega⟩
  have hpow : s ∣ m^(orderOf (m : ZMod s))-1 := by
    rw [← ZMod.natCast_eq_zero_iff (b := s)]
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_one, Nat.cast_pow,
      pow_orderOf_eq_one, sub_self]
  exact hbad (dvd_mul_of_dvd_right (hpow.trans (Finset.dvd_prod_of_mem (fun j => m^j-1) ho)) m)

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedAKS
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
open BooleanNetwork Primality

/-- All static search parameters and constants fit polynomial-width words. -/
lemma aks_constants_fit {n : ℕ} (hn : 128 ≤ n) : 8*n^8 < 2^(rootWidth n) := by
  have hp : n < 2^n := Nat.lt_pow_self (by decide)
  have hp8 : n^8 < (2^n)^8 := Nat.pow_lt_pow_left hp (by decide)
  have he : 3+n*8 ≤ rootWidth n := by dsimp [rootWidth] <;> nlinarith
  calc
    8*n^8 < 8*(2^n)^8 := Nat.mul_lt_mul_of_pos_left hp8 (by decide)
    _ = 2^(3+n*8) := by rw [pow_add,pow_mul]; norm_num
    _ ≤ 2^(rootWidth n) := Nat.pow_le_pow_right (by decide) he

lemma allCongruences_value (s w : ℕ) [NeZero s] (x : Basis w) (hw : 0 < w)
    (hm : 2 ≤ (bitsValue x).toNat) (hs : 8*s < 2^w) :
    (allCongruences s w).eval x 0=true ↔
      ∀ a : ℕ, 1 ≤ a → a ≤ 8*s →
        (cyclicX (R := ZMod (bitsValue x).toNat) s+cyclicC s (a : ZMod (bitsValue x).toNat))^
          (bitsValue x).toNat=cyclicX s^(bitsValue x).toNat+cyclicC s (a : ZMod (bitsValue x).toNat) := by
  rw [allCongruences,all_ofFn_eval]
  constructor
  · intro h a ha has
    have hh := (cyclicTest_correct s w (a-1+1) x hw hm (by omega)).mp
      (h (⟨a-1,by omega⟩ : Fin (8*s)))
    simpa only [show a-1+1=a by omega] using hh
  · intro h i
    rw [cyclicTest_correct s w (i.val+1) x hw hm (by omega)]
    exact h _ (by omega) (by omega)

lemma aksBranch_sound {n s : ℕ} [NeZero s] (hn : 128 ≤ n) (hs : s.Prime) (hsn : s ≤ n^8)
    (x : Basis (rootWidth n)) (hm : 2 ≤ (bitsValue x).toNat) (hmb : (bitsValue x).toNat < 2^n)
    (hpow : ¬ PerfectPower (bitsValue x).toNat) (h : (aksBranch n s).eval x 0=true) :
    (bitsValue x).toNat.Prime := by
  have hfit := aks_constants_fit hn
  have hsfit : 8*s < 2^(rootWidth n) := (Nat.mul_le_mul_left 8 hsn).trans_lt hfit
  have hsfit' : s < 2^(rootWidth n) := by omega
  have hkfit : n^2 < 2^(rootWidth n) := by
    have hh : rootWidth n < 2^(rootWidth n) := Nat.lt_pow_self (by decide)
    dsimp [rootWidth] at *
    nlinarith
  rw [aksBranch,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,dividesNet_value _ _ _ hsfit',
    orderTests_value _ _ _ _ hs.two_le hsfit' hkfit,
    noSmallDivisor_value _ _ _ hsfit,
    allCongruences_value _ _ _ (by dsimp [rootWidth];omega) hm hsfit] at h
  have hcop : s.Coprime (bitsValue x).toNat := hs.coprime_iff_not_dvd.mpr h.1.1
  have ho := (order_tests_iff hs hcop).mp h.1.2
  by_cases hb : (bitsValue x).toNat ≤ 8*s
  · exact prime_of_no_small_divisor hm hb h.2.1
  · exact cyclic_large_branch_prime hn hm hmb hs hcop ho hpow
      (fun d hd hdB => h.2.1 d hd hdB (by omega)) h.2.2

lemma aksBranch_complete {n s : ℕ} [NeZero s] (hn : 128 ≤ n) (hs : s.Prime) (hsn : s ≤ n^8)
    (x : Basis (rootWidth n)) (hm : (bitsValue x).toNat.Prime)
    (hcop : s.Coprime (bitsValue x).toNat) (ho : n^2 < orderOf ((bitsValue x).toNat : ZMod s)) :
    (aksBranch n s).eval x 0=true := by
  have hfit := aks_constants_fit hn
  have hsfit : 8*s < 2^(rootWidth n) := (Nat.mul_le_mul_left 8 hsn).trans_lt hfit
  have hsfit' : s < 2^(rootWidth n) := by omega
  have hkfit : n^2 < 2^(rootWidth n) := by
    have hh : rootWidth n < 2^(rootWidth n) := Nat.lt_pow_self (by decide)
    dsimp [rootWidth] at *
    nlinarith
  rw [aksBranch,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,dividesNet_value _ _ _ hsfit',
    orderTests_value _ _ _ _ hs.two_le hsfit' hkfit,
    noSmallDivisor_value _ _ _ hsfit,
    allCongruences_value _ _ _ (by dsimp [rootWidth];omega) hm.two_le hsfit]
  refine ⟨⟨hs.coprime_iff_not_dvd.mp hcop,(order_tests_iff hs hcop).mpr ho⟩,?_,?_⟩
  · intro d hd _hdb hdm hdiv
    have := hm.eq_one_or_self_of_dvd d hdiv
    omega
  · intro a _ha _has
    exact cyclic_prime_test hm a

/-- Full exact bounded AKS primality circuit, not an assumed decision procedure. -/
theorem primalityNet_correct {n : ℕ} (hn : 128 ≤ n) (x : Basis (rootWidth n))
    (hm : 2 ≤ (bitsValue x).toNat) (hmb : (bitsValue x).toNat < 2^n) :
    (primalityNet n).eval x 0=true ↔ (bitsValue x).toNat.Prime := by
  rw [primalityNet,eval_band,Bool.and_eq_true,bnot_value,perfectPowerNet_correct (by omega) _ hmb,
    any_ofFn_eval]
  constructor
  · rintro ⟨hpow,s,h⟩
    by_cases hs : s.val.Prime
    · let : NeZero s.val := ⟨hs.ne_zero⟩
      have he : aksStaticBranch n s.val=aksBranch n s.val := dite_eq_left hs
      rw [he] at h
      exact aksBranch_sound hn hs (by omega) x hm hmb hpow h
    · simp [aksStaticBranch,hs] at h
  · intro hp
    obtain ⟨s,hs,hsn,hcop,ho⟩ := auxiliary_prime_exists hn hm hmb
    let : NeZero s := ⟨hs.ne_zero⟩
    refine ⟨prime_not_perfectPower hp,⟨s,by omega⟩,?_⟩
    have he : aksStaticBranch n s=aksBranch n s := dite_eq_left hs
    change (aksStaticBranch n s).eval x 0=true
    rw [he]
    exact aksBranch_complete hn hs hsn x hp hcop ho

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedStack
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork

lemma block_stackEncoding (s w : ℕ) (xs : List (Basis w)) (i : Fin s) :
    block (stackEncoding s w xs) i = xs[i.val]?.getD (fun _ => false) := by
  funext j
  simp [block,stackEncoding]

lemma stackPop_value {s w : ℕ} (x : Basis (s*w)) (i : Fin s) :
    block ((stackPop s w).eval x) i =
      if h : i.val+1 < s then block x ⟨i.val+1,h⟩ else (fun _ => false) := by
  rw [stackPop,wordBlocks_eval]
  split_ifs
  · rfl
  · funext j
    simp [wordConstant]

lemma stackPush_value {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w))
    (x : Basis k) (i : Fin s) :
    block ((stackPush a v).eval x) i =
      if _h : i.val=0 then a.eval x else block (v.eval x) ⟨i.val-1,by omega⟩ := by
  rw [stackPush,wordBlocks_eval]
  split_ifs <;> rfl

lemma block_ext {s w : ℕ} {x y : Basis (s*w)}
    (h : ∀ i : Fin s, block x i=block y i) : x=y := by
  funext j
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective j
  exact congrFun (h i) k

lemma stackPop_encoding {s w : ℕ} (xs : List (Basis w)) (h : xs.length ≤ s) :
    (stackPop s w).eval (stackEncoding s w xs)=stackEncoding s w xs.tail := by
  apply block_ext
  intro i
  rw [stackPop_value,block_stackEncoding]
  split_ifs with hi
  · rw [block_stackEncoding]
    cases xs <;> simp
  · have hh : xs.tail[i.val]?=none := by
      apply List.getElem?_eq_none
      simp only [List.length_tail]
      omega
    rw [hh]
    rfl

lemma stackPush_encoding {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w))
    (x : Basis k) (xs : List (Basis w)) (hv : v.eval x=stackEncoding s w xs) :
    (stackPush a v).eval x=stackEncoding s w (a.eval x::xs) := by
  apply block_ext
  intro i
  rw [stackPush_value,block_stackEncoding]
  split_ifs with hi
  · simp [hi]
  · rw [hv,block_stackEncoding]
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
    simp [hj]

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorEncoding
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

lemma paddedOrder_append (ps : List ℕ) (k : ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hs : ps.Pairwise (·≤·)) : (ps++List.replicate k 0).Pairwise PaddedOrder := by
  rw [List.pairwise_append]
  refine ⟨hs.imp_of_mem ?_,?_,?_⟩
  · intro a b ha _hab hab
    exact Or.inr ⟨(hp a ha).ne_zero,hab⟩
  · apply List.pairwise_replicate.mpr
    exact Or.inr (Or.inl rfl)
  · intro a _ b hb
    have hb0 : b=0 := by simpa using (List.mem_replicate.mp hb).2
    exact Or.inl hb0

lemma unpadProduct_append (ps : List ℕ) (k : ℕ) (hp : ∀ p ∈ ps, p≠0) :
    unpadProduct (ps++List.replicate k 0)=ps.prod := by
  unfold unpadProduct
  rw [List.map_append,List.prod_append,List.map_replicate]
  simp only [ite_true, if_true,List.prod_replicate,one_pow,mul_one]
  congr 1
  conv_rhs => rw [← List.map_id ps]
  exact List.map_congr_left (fun p hp' => ite_eq_right (hp p hp'))

lemma FactorListValid.decompose {N : ℕ} {xs : List ℕ} (h : FactorListValid N xs) :
    ∃ ps : List ℕ, (∀ p ∈ ps, p.Prime) ∧ ps.Pairwise (·≤·) ∧ ps.prod=N ∧
      ps.length≤xs.length ∧ xs=ps++List.replicate (xs.length-ps.length) 0 := by
  rcases h with ⟨hp,hs,hprod⟩
  induction xs generalizing N with
  | nil => exact ⟨[],by simp,by simp,by simpa [unpadProduct] using hprod,by simp,by simp⟩
  | cons a xs ih =>
    have hpa : a=0 ∨ a.Prime := hp a (by simp)
    have hps : ∀ p ∈ xs, p=0 ∨ p.Prime := fun p h => hp p (by simp [h])
    have hsw := List.pairwise_cons.mp hs
    rcases hpa with rfl | ha
    · have hz : ∀ b ∈ xs, b=0 := by
        intro b hb
        rcases hsw.1 b hb with h | h
        · exact h
        · exact (h.1 rfl).elim
      have he : xs=List.replicate xs.length 0 := List.eq_replicate_of_mem hz
      have hn : N=1 := by
        rw [he] at hprod
        simpa [unpadProduct] using hprod.symm
      refine ⟨[],by simp,by simp,by simpa using hn.symm,by simp,?_⟩
      simp only [List.length_cons,List.length_nil,Nat.sub_zero,List.nil_append]
      rw [List.replicate_succ,← he]
    · obtain ⟨ps,hpp,hpsort,hpprod,hplen,hxeq⟩ :=
        ih hps hsw.2 (rfl : unpadProduct xs=unpadProduct xs)
      refine ⟨a::ps,?_,?_,?_,by simpa using hplen,?_⟩
      · intro p hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact ha
        · exact hpp p hp'
      · rw [List.pairwise_cons]
        refine ⟨?_,hpsort⟩
        intro p hpm
        have hpx : p ∈ xs := by rw [hxeq]; exact List.mem_append_left _ hpm
        rcases hsw.1 p hpx with he | he
        · exact ((hpp p hpm).ne_zero he).elim
        · exact he.2
      · simp only [List.prod_cons,hpprod]
        simpa only [unpadProduct,List.map_cons,List.prod_cons,ite_eq_right ha.ne_zero] using hprod
      · simpa only [List.length_cons,Nat.add_sub_add_right,List.cons_append] using congrArg (List.cons a) hxeq

lemma factorListValid_iff {N n : ℕ} {xs : List ℕ} (hlen : xs.length=n) :
    FactorListValid N xs ↔ CorrectEncoding N n xs := by
  constructor
  · intro h
    simpa only [hlen,CorrectEncoding] using h.decompose
  · rintro ⟨ps,hp,hs,hprod,hplen,rfl⟩
    refine ⟨?_,paddedOrder_append ps _ hp hs,?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inr (hp a ha)
      · exact Or.inl (List.mem_replicate.mp ha).2
    · exact (unpadProduct_append ps _ (fun p hp' => (hp p hp').ne_zero)).trans hprod

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

lemma rootWidth_ge (n : ℕ) : n ≤ rootWidth n := by
  dsimp [rootWidth]
  nlinarith

lemma primeWord_value {n : ℕ} (hn : 128≤n) (x : Basis n) :
    (primeWord n).eval x 0=true ↔ (bitsValue x).toNat.Prime := by
  have hfit : 2<2^n := by
    have := Nat.pow_le_pow_right (n:=2) (by decide) hn
    norm_num at this
    omega
  rw [primeWord,eval_band,Bool.and_eq_true,wordLe_eval,wordConstant_eval,
    eval_select,Function.comp_id,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hfit,decide_eq_true_eq,
    eval_comp]
  by_cases h : 2≤(bitsValue x).toNat
  · rw [and_iff_right h,primalityNet_correct hn _ (by
      rw [resizeWord_toNat (rootWidth_ge n)];exact h) (by
      rw [resizeWord_toNat (rootWidth_ge n)];exact (bitsValue x).isLt),
      resizeWord_toNat (rootWidth_ge n)]
  · constructor
    · exact fun hh => (h hh.1).elim
    · exact fun hh => (h hh.two_le).elim

lemma zeroWord_value {k n : ℕ} (a : BooleanNetwork k n) (x : Basis k) :
    (zeroWord a).eval x 0=true ↔ (bitsValue (a.eval x)).toNat=0 := by
  rw [zeroWord,equalOn_value,wordConstant_eval]
  simp

lemma primeOrZero_value {k n : ℕ} (hn : 128≤n) (a : BooleanNetwork k n) (x : Basis k) :
    (primeOrZero a).eval x 0=true ↔
      (bitsValue (a.eval x)).toNat=0 ∨ (bitsValue (a.eval x)).toNat.Prime := by
  rw [primeOrZero,eval_bor,Bool.or_eq_true,zeroWord_value,eval_comp,primeWord_value hn]

lemma paddedPair_value {k n : ℕ} (a b : BooleanNetwork k n) (x : Basis k) :
    (paddedPair a b).eval x 0=true ↔
      PaddedOrder (bitsValue (a.eval x)).toNat (bitsValue (b.eval x)).toNat := by
  rw [paddedPair,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,bnot_value,
    zeroWord_value,zeroWord_value,wordLe_eval,decide_eq_true_eq]
  rfl

lemma unpadWord_value {k n : ℕ} (hn : 0<n) (a : BooleanNetwork k n) (x : Basis k) :
    (bitsValue ((unpadWord a).eval x)).toNat=
      if (bitsValue (a.eval x)).toNat=0 then 1 else (bitsValue (a.eval x)).toNat := by
  have hp : 1<2^n := Nat.one_lt_pow (by omega) (by decide)
  rw [unpadWord,wordMux_eval]
  by_cases h : (bitsValue (a.eval x)).toNat=0
  · rw [ite_eq_left h,ite_eq_left ((zeroWord_value a x).mpr h),wordConstant_eval]
    simpa using (Nat.mod_eq_of_lt hp)
  · rw [ite_eq_right h,ite_eq_right (by simpa only [zeroWord_value] using h)]

lemma productNet_nat {k w : ℕ} (as : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((productNet as).eval x)).toNat=
      (as.map (fun a => (bitsValue (a.eval x)).toNat)).prod % 2^w := by
  induction as with
  | nil => simp [productNet,wordConstant_eval]
  | cons a as ih =>
    simp only [productNet,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,ih,
      List.map_cons,List.prod_cons,Nat.mul_mod_mod]

lemma candidateProduct_value {k n : ℕ} (hn : 0<n) (as : Fin n→BooleanNetwork k n) (x : Basis k) :
    (bitsValue ((candidateProduct as).eval x)).toNat=unpadProduct (candidateWords as x) := by
  have he : ((List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n)))).map
      (fun a => (bitsValue (a.eval x)).toNat)) =
      (candidateWords as x).map (fun a => if a=0 then 1 else a) := by
    simp only [List.map_ofFn,candidateWords]
    congr 1
    funext i
    simp only [Function.comp_apply,eval_comp,resizeWord_toNat (rootWidth_ge n),
      unpadWord_value hn]
  have hb : unpadProduct (candidateWords as x)≤(2^n)^n := by
    have hh := List.prod_le_pow_card ((candidateWords as x).map (fun a => if a=0 then 1 else a))
      (2^n) (by
        intro a ha
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
        split
        · exact Nat.one_le_pow _ _ (by decide)
        · exact (bitsValue ((as i).eval x)).isLt.le)
    simpa only [unpadProduct,List.length_map,candidateWords,List.length_ofFn] using hh
  have hpow : (2^n)^n<2^(rootWidth n) := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) (by dsimp [rootWidth] <;> nlinarith)
  rw [candidateProduct,productNet_nat,he]
  change unpadProduct (candidateWords as x) % 2^rootWidth n = _
  exact Nat.mod_eq_of_lt (hb.trans_lt hpow)

lemma factorVerifierOn_correct {k n : ℕ} (hn : 128≤n) (N : BooleanNetwork k n)
    (as : Fin n→BooleanNetwork k n) (x : Basis k) :
    (factorVerifierOn N as).eval x 0=true ↔
      CorrectEncoding (bitsValue (N.eval x)).toNat n (candidateWords as x) := by
  rw [← factorListValid_iff (by simp [candidateWords]),FactorListValid]
  rw [factorVerifierOn,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    all_ofFn_eval,all_ofFn_eval,equalOn_value]
  rw [candidateProduct_value (by omega),eval_comp,resizeWord_toNat (rootWidth_ge n)]
  have hp : (∀ i : Fin n, (primeOrZero (as i)).eval x 0=true) ↔
      ∀ a ∈ candidateWords as x, a=0 ∨ a.Prime := by
    simp only [candidateWords,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
      primeOrZero_value hn]
  have hs : (∀ i : Fin (n*n),
      (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
        paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
        else constant true).eval x 0=true) ↔ (candidateWords as x).Pairwise PaddedOrder := by
    rw [candidateWords,List.pairwise_ofFn]
    constructor
    · intro h i j hij
      have hh := h (finProdFinEquiv (i,j))
      simp only [Equiv.symm_apply_apply,ite_eq_left hij] at hh
      exact (paddedPair_value _ _ _).mp hh
    · intro h i
      split_ifs with hij
      · exact (paddedPair_value _ _ _).mpr (h hij)
      · simp
  rw [hp,hs]
  tauto

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorGuess
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
open BitArithmetic BooleanNetwork Exactness

lemma guessVerifier_correct {n : ℕ} (hn : 128≤n) (a : Basis n) (x : Basis (n*n)) :
    (guessVerifier n).eval (Fin.append a x) 0=true ↔
      CorrectEncoding (bitsValue a).toNat n (guessWords n x) := by
  rw [guessVerifier,factorVerifierOn_correct hn]
  have hN : (select (Fin.castAdd (n*n))).eval (Fin.append a x)=a := by
    funext i
    exact Fin.append_left a x i
  rw [hN]
  apply iff_of_eq
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 2
  funext j
  exact Fin.append_right a x (finProdFinEquiv (i,j))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalRounding
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ifLe _root_.OAI.ExactQuantumFactoring.IntExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifIntLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_inv _root_.OAI.ExactQuantumFactoring.RatExpr.eval_neg _root_.OAI.ExactQuantumFactoring.RatExpr.eval_num _root_.OAI.ExactQuantumFactoring.RatExpr.eval_over _root_.OAI.ExactQuantumFactoring.RatExpr.eval_power _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.RatExpr.eval_times
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_CanonicalTransition
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
open Exactness RepeatedTrials

lemma canonicalList_good {m n K : ℕ} (hm : m≠0) (hb : m<2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) (hK : 0<K) :
    GoodList hm hb p₀ K (canonicalList hm p₀ K) := by
  let : NeZero m := ⟨hm⟩
  refine ⟨⟨0,hK⟩,canonicalUnit hm p₀,?_,canonicalUnit_favorable hm hb hodd p₀ p₁ hne⟩
  simp only [canonicalList,bitsEquiv,Equiv.coe_fn_symm_mk,bitsValue_bits,
    BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt ((ZMod.val_lt _).trans_le (Nat.le_pow_clog (by decide : 1<2) m))).symm

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SortedWords
attribute [-instance] _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
namespace SortedWords

lemma le_total {w : ℕ} (a b : Basis w) : LEWord a b ∨ LEWord b a := by
  dsimp only [LEWord,PaddedOrder]
  omega
lemma le_trans {w : ℕ} {a b c : Basis w} (h : LEWord a b) (h' : LEWord b c) : LEWord a c := by
  dsimp only [LEWord,PaddedOrder] at *
  omega

lemma insert_perm {w : ℕ} (a : Basis w) (bs : List (Basis w)) : (insert a bs).Perm (a::bs) := by
  induction bs generalizing a with
  | nil=>rfl
  | cons b bs ih=>
    rw [insert]
    split_ifs
    · exact (ih b).cons a
    · exact ((ih a).cons b).trans (List.Perm.swap b a bs).symm
lemma sort_perm {w : ℕ} (bs : List (Basis w)) : (sort bs).Perm bs := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>exact (insert_perm b (sort bs)).trans (ih.cons b)
lemma sort_length {w : ℕ} (bs : List (Basis w)) : (sort bs).length=bs.length := (sort_perm bs).length_eq

lemma insert_sorted {w : ℕ} (a : Basis w) (bs : List (Basis w)) (hs : bs.Pairwise LEWord) :
    (insert a bs).Pairwise LEWord := by
  induction bs generalizing a with
  | nil=>simp [insert]
  | cons b bs ih=>
    obtain ⟨hfirst,htail⟩ := List.pairwise_cons.mp hs
    rw [insert]
    split_ifs with hab
    · rw [List.pairwise_cons]
      refine ⟨?_,ih b htail⟩
      intro c hc
      rcases List.mem_cons.mp ((insert_perm b bs).mem_iff.mp hc) with rfl | hc
      · exact hab
      · exact le_trans hab (hfirst c hc)
    · rw [List.pairwise_cons]
      refine ⟨?_,ih a htail⟩
      intro c hc
      rcases List.mem_cons.mp ((insert_perm a bs).mem_iff.mp hc) with rfl | hc
      · exact (le_total _ _).resolve_left hab
      · exact hfirst c hc
lemma sort_sorted {w : ℕ} (bs : List (Basis w)) : (sort bs).Pairwise LEWord := by
  induction bs with
  | nil=>simp [sort]
  | cons b bs ih=>exact insert_sorted b (sort bs) ih

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SortedEncoding
attribute [-instance] _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons
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


namespace ExactQuantumFactoring.BitArithmetic.SortedWords

lemma zero_number (w : ℕ) : (bitsValue (fun _ : Fin w=>false)).toNat=0 := by
  have hz : bitsValue (fun _ : Fin w=>false)=(0 : BitVec w) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [bitsValue_bit _ ⟨i,hi⟩]
    simp
  rw [hz]
  rfl
lemma numbers_pad {w : ℕ} (xs : List (Basis w)) (k : ℕ) :
    numbers (xs++List.replicate k (fun _=>false))=numbers xs++List.replicate k 0 := by
  simp only [numbers,List.map_append,List.map_replicate,zero_number]

/-- Literal compare-exchange sorting gives the exact source sorted padded
encoding, not just an arbitrary prime multiset. -/
theorem sort_correct {w N r : ℕ} (xs : List (Basis w))
    (hp : ∀ p∈numbers xs,p.Prime) (hprod : (numbers xs).prod=N) (hlen : xs.length ≤ r) :
    CorrectEncoding N r (numbers (sort (xs++List.replicate (r-xs.length) (fun _=>false)))) := by
  let zs := xs++List.replicate (r-xs.length) (fun _ : Fin w=>false)
  have hlen' : (numbers (sort zs)).length=r := by
    simp only [numbers,List.length_map,sort_length,zs,List.length_append,List.length_replicate]
    omega
  apply (factorListValid_iff hlen').mp
  have hperm : (numbers (sort zs)).Perm (numbers zs) := (sort_perm zs).map _
  refine ⟨?_,?_,?_⟩
  · intro p hpm
    have hz := hperm.mem_iff.mp hpm
    simp only [zs,numbers_pad] at hz
    rcases List.mem_append.mp hz with hx | hx
    · exact Or.inr (hp p hx)
    · exact Or.inl (List.mem_replicate.mp hx).2
  · exact List.pairwise_map.mpr (sort_sorted zs)
  · calc
      unpadProduct (numbers (sort zs))=unpadProduct (numbers zs) := (hperm.map _).prod_eq
      _ = N := by
        simp only [zs,numbers_pad]
        rw [unpadProduct_append _ _ (fun p hp'=> (hp p hp').ne_zero),hprod]

end ExactQuantumFactoring.BitArithmetic.SortedWords


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CanonicalWords
attribute [-instance] _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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
open OrderTrial SortedWords

lemma natBasis_number {n : ℕ} (a : Basis n) : natBasis n (bitsValue a).toNat=a := by
  apply (bitsEquiv n).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue (natBasis n (bitsValue a).toNat)).toNat=(bitsValue a).toNat
  rw [natBasis_value,Nat.mod_eq_of_lt (bitsValue a).isLt]

lemma canonical_numbers {n : ℕ} (xs : List (Basis n)) : canonicalWords n (numbers xs)=xs := by
  simp only [canonicalWords,numbers,List.map_map,Function.comp_def,natBasis_number]
  exact List.map_id xs

lemma canonical_length (n : ℕ) (xs : List ℕ) : (canonicalWords n xs).length=xs.length := List.length_map (natBasis n)
lemma canonical_append (n : ℕ) (xs ys : List ℕ) :
    canonicalWords n (xs++ys)=canonicalWords n xs++canonicalWords n ys := List.map_append

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ChildQueue
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork
namespace ChildQueue

lemma wordMember_eval {k w : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) (x : Basis k) :
    (wordMember a as).eval x 0=true ↔ a.eval x∈as.map (fun b=>b.eval x) := by
  rw [wordMember,any_eval]
  constructor
  · rintro ⟨c,hc,ht⟩
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    rw [eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq] at ht
    exact List.mem_map.mpr ⟨b,hb,((bitsEquiv w).injective ht).symm⟩
  · rintro hm
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
    refine ⟨(a.pair b).comp (wordEq w),List.mem_map.mpr ⟨b,hb,rfl⟩,?_⟩
    rw [eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq,he]


lemma source_eval (k s w : ℕ) (x : Basis k) (y : Basis (s*w)) :
    (source k s w).eval (Fin.append x y)=x := by
  funext i
  exact Fin.append_left _ _ _
lemma queue_eval (k s w : ℕ) (x : Basis k) (y : Basis (s*w)) :
    (queue k s w).eval (Fin.append x y)=y := by
  funext i
  exact Fin.append_right _ _ _

lemma active_eval {k w : ℕ} (hw : 2 ≤ w) (a : BooleanNetwork k w)
    (as : List (BooleanNetwork k w)) (x : Basis k) :
    (active a as).eval x 0=true ↔ 2<(bitsValue (a.eval x)).toNat ∧ a.eval x∉as.map (fun b=>b.eval x) := by
  have hb : 2<2^w := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  simp only [active,eval_band,Bool.and_eq_true,eval_bnot,Bool.not_eq_true',wordLt_eval,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb,decide_eq_true_eq]
  have hm := wordMember_eval a as x
  cases hh : (wordMember a as).eval x 0 <;> simp_all

lemma pushOne_eval {k w : ℕ} (hw : 2 ≤ w) (s : ℕ) (a : BooleanNetwork k w)
    (as : List (BooleanNetwork k w)) (x : Basis k) (ys : List (Basis w)) :
    (pushOne s a as).eval (Fin.append x (stackEncoding s w ys))=
      Fin.append x (stackEncoding s w
        (if 2<(bitsValue (a.eval x)).toNat ∧ a.eval x∉as.map (fun b=>b.eval x)
          then predBits (a.eval x)::ys else ys)) := by
  have hv : ((((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w)).eval
      (Fin.append x (stackEncoding s w ys)))=predBits (a.eval x) := by
    rw [eval_comp,eval_pair,liftWord,eval_comp,source_eval]
    unfold predBits
    congr 2
    funext i
    simp [wordConstant,eval_vector,eval_constant]
  have hs := stackPush_encoding
    (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))
    (queue k s w) (Fin.append x (stackEncoding s w ys)) ys (queue_eval k s w x _)
  rw [hv] at hs
  rw [pushOne,eval_pair,source_eval,wordMux_eval,eval_comp,source_eval,hs,queue_eval]
  by_cases hc : 2<(bitsValue (a.eval x)).toNat ∧ a.eval x∉as.map (fun b=>b.eval x)
  · rw [ite_eq_left ((active_eval hw a as x).mpr hc),ite_eq_left hc]
  · rw [ite_eq_right (fun h=>hc ((active_eval hw a as x).mp h)),ite_eq_right hc]

lemma pushAll_eval {k w : ℕ} (hw : 2 ≤ w) (s : ℕ) (as : List (BooleanNetwork k w))
    (x : Basis k) (ys : List (Basis w)) :
    (pushAll s as).eval (Fin.append x (stackEncoding s w ys))=
      Fin.append x (stackEncoding s w (kids (as.map (fun a=>a.eval x))++ys)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [pushAll,eval_comp,ih,pushOne_eval hw,List.map_cons,kids]
    split_ifs <;> rfl

lemma predBits_value {w : ℕ} (hw : 1 ≤ w) (a : Basis w) (ha : 1 ≤ (bitsValue a).toNat) :
    (bitsValue (predBits a)).toNat=(bitsValue a).toNat-1 := by
  have hb : 1<2^w := Nat.one_lt_pow (by omega) (by decide)
  rw [predBits,sub_word]
  have hv : bitsValue (fun i : Fin w => (BitVec.ofNat w 1).getLsbD i.val)=BitVec.ofNat w 1 := bitsValue_bits _
  rw [hv,BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]
  · simpa only [BitVec.le_def,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb] using ha

end ChildQueue
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ChildQueueCorrect
attribute [-instance] _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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


namespace ExactQuantumFactoring.BitArithmetic.ChildQueue
open SortedWords

lemma naturalKids_cons (a : ℕ) (as : List ℕ) :
    naturalKids (a::as) = if 2<a ∧ a∉as then (a-1)::naturalKids as else naturalKids as := by
  by_cases hm : a∈as <;> by_cases ha : 2<a <;>
    simp [naturalKids,hm,ha]

lemma number_injective {w : ℕ} : Function.Injective (fun a : Basis w=>(bitsValue a).toNat) := by
  intro a b h
  exact (bitsEquiv w).injective (BitVec.eq_of_toNat_eq h)

lemma kids_numbers {w : ℕ} (hw : 2 ≤ w) (xs : List (Basis w)) :
    numbers (kids xs)=naturalKids (numbers xs) := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    have hm : (bitsValue a).toNat∈numbers as ↔ a∈as :=
      List.mem_map_of_injective number_injective
    simp only [numbers,List.map_cons] at ih ⊢
    rw [naturalKids_cons,kids]
    by_cases hc : 2<(bitsValue a).toNat ∧ a∉as
    · have hd : 2<(bitsValue a).toNat ∧ (bitsValue a).toNat∉numbers as := ⟨hc.1,fun h=>hc.2 (hm.mp h)⟩
      dsimp only [numbers] at hd
      rw [ite_eq_left hc,ite_eq_left hd,List.map_cons,predBits_value (by omega) a (by omega),ih]
    · have hd : ¬(2<(bitsValue a).toNat ∧ (bitsValue a).toNat∉numbers as) := by
        rintro ⟨h1,h2⟩
        exact hc ⟨h1,fun h=>h2 (hm.mpr h)⟩
      dsimp only [numbers] at hd
      rw [ite_eq_right hc,ite_eq_right hd,ih]

/-- No factorization oracle is used in the queue circuit: the child list obtained
from the ACTUAL correct sorted prime fields is the source's exact ordered child
list, with distinct primes within one node and occurrence multiplicity outside it. -/
lemma naturalKids_correct {N n : ℕ} {xs : List ℕ} (hN : 2 ≤ N)
    (hx : CorrectEncoding N n xs) : naturalKids xs=AuxiliaryTree.children N := by
  obtain ⟨ps,hp,hs,hprod,_,rfl⟩ := hx
  let ys := (ps++List.replicate (n-ps.length) 0).dedup.filter (fun a=>2<a)
  have hmem (p : ℕ) : p∈ys ↔ p.Prime ∧ p∣N ∧ 2<p := by
    have hperm := Nat.primeFactorsList_unique hprod hp
    dsimp only [ys]
    simp only [List.mem_filter,List.mem_dedup,decide_eq_true_eq,List.mem_append]
    constructor
    · rintro ⟨hm,ht⟩
      have hps : p∈ps := by
        rcases hm with hm | hm
        · exact hm
        · have hz := (List.mem_replicate.mp hm).2
          omega
      exact ⟨hp p hps,by rw [←hprod];exact List.dvd_prod hps,ht⟩
    · rintro ⟨hprime,hdvd,ht⟩
      exact ⟨Or.inl (hperm.mem_iff.mpr ((Nat.mem_primeFactorsList (by omega)).mpr ⟨hprime,hdvd⟩)),ht⟩
  have hn : ys.Nodup := (List.nodup_dedup _).filter _
  have hsorted : ys.Pairwise (·≤·) := by
    have hpad := paddedOrder_append ps (n-ps.length) hp hs
    have hsub : List.Sublist ys (ps++List.replicate (n-ps.length) 0) :=
      List.filter_sublist.trans (List.dedup_sublist _)
    apply (hpad.sublist hsub).imp_of_mem
    intro a b _ hb hab
    have hb2 := (hmem b).mp hb
    rcases hab with hb0 | hab
    · omega
    · exact hab.2
  have hfin : ys.toFinset=N.primeFactors.filter (fun p=>2<p) := by
    ext p
    simp only [List.mem_toFinset,hmem,Finset.mem_filter,
      Nat.mem_primeFactors_of_ne_zero (by omega : N≠0)]
    tauto
  have he : (N.primeFactors.filter (fun p=>2<p)).sort (·≤·)=ys := by
    rw [←hfin]
    exact (List.toFinset_sort (·≤·) hn).mpr hsorted
  change ys.map (·-1)=AuxiliaryTree.children N
  rw [AuxiliaryTree.children,he]

theorem kids_correct {w N n : ℕ} (hw : 2 ≤ w) (hN : 2 ≤ N)
    (xs : List (Basis w)) (hx : CorrectEncoding N n (numbers xs)) :
    numbers (kids xs)=AuxiliaryTree.children N := by
  rw [kids_numbers hw,naturalKids_correct hN hx]

end ExactQuantumFactoring.BitArithmetic.ChildQueue


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DyadicCompletion
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open Exactness OrderTrial

namespace Completion

lemma passed_good {α : Type*} {W t d : ℕ} (ordinary : α→Basis W) (P : Basis W→Prop)
    (y₀ : Basis W) (s z : ℚ) (hy : P y₀) (r : Raw α W t d)
    (h : passed (P∘ordinary) y₀ s z r) : P (output ordinary r) := by
  rcases h with h | h
  · simpa only [output,ite_eq_right h.1,Function.comp_def] using h.2.1
  · simpa only [output,ite_eq_left h.1,h.2.1] using hy

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletedOrderSlots
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


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial

namespace OrderSlots

lemma unitOrder_lt {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) :
    unitOrder a m < 2^n := by
  classical
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  unfold unitOrder
  split_ifs with h
  · have hh := orderOf_le_card (x:=h.2.unit)
    rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] at hh
    exact (hh.trans (Nat.totient_le _)).trans_lt (bitsValue m).isLt
  · positivity

lemma passed_output {n : ℕ} (a m : Basis n) (r : Result n) (hp : passed a m r) :
    output a m r=canonical a m := by
  classical
  unfold passed at hp
  split_ifs at hp with h
  · rcases hp with hp | hp
    · simp only [output,Completion.output,ite_eq_right hp.1,ordinary,ite_eq_left h,canonical,
        unitOrder,dite_eq_left h,hp.2.1]
    · simp only [output,Completion.output,ite_eq_left hp.1,hp.2.1]
  · rcases hp with hp | hp
    · simp only [output,Completion.output,ite_eq_right hp.1,ordinary,ite_eq_right h,canonical,
        unitOrder,dite_eq_right h]
    · simp only [output,Completion.output,ite_eq_left hp.1,hp.2.1]

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RuntimeListPreparation
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
open Exactness BitArithmetic BooleanNetwork

lemma padBits_value {b n : ℕ} (hb : b ≤ n) (x : Basis b) :
    (bitsValue (padBits hb x)).toNat=(bitsValue x).toNat := by
  have he : bitsValue (padBits hb x)=(bitsValue x).setWidth n := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (bitsValue (padBits hb x)).getLsbD i=padBits hb x ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
      BitVec.getLsbD_setWidth]
    simp only [hi,decide_true,Bool.true_and,padBits]
    split_ifs with hib
    · exact (bitsValue_bit x ⟨i,hib⟩).symm
    · exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm
  rw [he,setWidth_toNat_of_le hb]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionWords
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
open Exactness RepeatedTrials

namespace TransitionWords

lemma read_encode {n K : ℕ} (a : Fin K→Basis n) (i : Fin K) : read (encode a) i=a i := by
  funext j
  simp only [read,encode,Fin.cast_cast,Fin.cast_eq_self,Equiv.symm_apply_apply,Fin.val_castSucc]
  rw [dite_eq_left i.isLt]

lemma pow_width_le (n K : ℕ) : 2^n ≤ 2^(n*(K+1)) := by
  apply Nat.pow_le_pow_right (by decide : 1≤2)
  nlinarith

end TransitionWords

namespace ListSlots

lemma ordinary_good {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m)
    (x : Ordinary n m) (hh : GoodList hm hb p₀ (K n) x) :
    GoodOutput hm hb p₀ (ordinary hb x) := by
  obtain ⟨i,u,hu,hf⟩ := hh
  refine ⟨i,u,?_,hf⟩
  change (bitsValue (TransitionWords.read (TransitionWords.encode _) i)).toNat=_
  rw [TransitionWords.read_encode,padBits_value]
  exact hu.symm

lemma canonical_good {n m : ℕ} (hn : 128 ≤ n) (hm : m ≠ 0) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) : GoodOutput hm hb p₀ (canonical hm hb p₀) := by
  apply ordinary_good
  exact canonicalList_good hm hb hodd p₀ p₁ hne (pow_pos (by omega) _)

end ListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletedSplit
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
open Exactness RepeatedTrials OrderTrial

namespace OrderSlots

lemma unitOrder_eq {n : ℕ} (a m : Basis n) (u : (ZMod (bitsValue m).toNat)ˣ)
    (hlt : (bitsValue a).toNat < (bitsValue m).toNat)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat)) :
    unitOrder a m=orderOf u := by
  classical
  have hu : IsUnit ((bitsValue a).toNat : ZMod (bitsValue m).toNat) := ha.symm ▸ u.isUnit
  have hva : Usable a m := ⟨hlt,hu⟩
  rw [unitOrder,dite_eq_left hva]
  congr 1
  apply Units.ext
  exact hu.unit_spec.trans ha

lemma passed_value {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) (r : Result n)
    (hp : passed a m r) : (bitsValue (output a m r)).toNat=unitOrder a m := by
  rw [passed_output a m r hp,canonical,natBasis_value,Nat.mod_eq_of_lt]
  exact (unitOrder_lt a m hm).trans_le (TransitionWords.pow_width_le n (n^5))

lemma passed_order {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (u : (ZMod (bitsValue m).toNat)ˣ)
    (hlt : (bitsValue a).toNat < (bitsValue m).toNat)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (r : Result n) (hp : passed a m r) : (bitsValue (output a m r)).toNat=orderOf u := by
  rw [passed_value a m hm r hp,unitOrder_eq a m u hlt ha]

end OrderSlots

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorPreparation
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
open Exactness RepeatedTrials

lemma tensorLayout_succ (q K : ℕ) (x : Fin (K+1)→Basis q) :
    tensorLayout q (K+1) x=Fin.append (x 0) (tensorLayout q K (Fin.tail x)) := rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListSlots
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
open Exactness RepeatedTrials
namespace PhysicalListSlots

lemma passed_good {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Result n) (hp : passed m hm p₀ r) : ListSlots.GoodOutput hm (bitsValue m).isLt p₀ (output r) :=
  Completion.passed_good ordinary _ _ _ _
    (ListSlots.canonical_good hn hm (bitsValue m).isLt hodd p₀ p₁ hne) r hp

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FixedSplit
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
open Exactness RepeatedTrials OrderTrial

namespace FixedSplit

lemma passed_pair {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw n) (hp : passed m (by omega) p₀ r) :
    ∃ u : (ZMod (bitsValue m).toNat)ˣ,
      FavorableUnit (by omega : (bitsValue m).toNat≠0) (bitsValue m).isLt p₀ u ∧
        ((u : ZMod (bitsValue m).toNat).val,orderOf u)∈pairs m r := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  obtain ⟨i,u,ha,hf⟩ := PhysicalListSlots.passed_good hn m (by omega) hodd p₀ p₁ hne r.1 hp.1
  have haz : ((bitsValue (bases r.1 i)).toNat : ZMod (bitsValue m).toNat)=u := by
    rw [show (bitsValue (bases r.1 i)).toNat=(u : ZMod (bitsValue m).toNat).val from ha]
    exact ZMod.natCast_zmod_val _
  have ho := OrderSlots.passed_order (bases r.1 i) m hm u (by change (bitsValue (TransitionWords.read (PhysicalListSlots.output r.1) i)).toNat < _; rw [ha]; exact (u : ZMod (bitsValue m).toNat).val_lt) haz (r.2 i) (hp.2 i)
  refine ⟨u,hf,?_⟩
  exact List.mem_ofFn.mpr ⟨i,Prod.ext ha ho⟩

/-- The output is the actual guarded even/root/order divisor scan, not a chosen
mathematical divisor. Both ordinary and guessed good list outputs are covered. -/
theorem passed_divisor {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hc : ¬(bitsValue m).toNat.Prime) (hodd : Odd (bitsValue m).toNat)
    (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw n) (hp : passed m (by omega) p₀ r) :
    FactorController.ProperDivisor (bitsValue m).toNat (divisor m r) := by
  obtain ⟨u,hf,hu⟩ := passed_pair hn m hm hodd p₀ p₁ hne r hp
  exact suppliedDivisor_good hm (bitsValue m).isLt hc (pairs m r) (fun _ _ => ⟨p₀,u,hf,hu⟩)

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_HardCofactor
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

/-- The randomized splitter is invoked only after the prime and perfect-power
cases. Such an input has two genuinely different prime-power components. -/
lemma exists_distinct_components {m : ℕ} (hm : 2 ≤ m) (hc : ¬m.Prime)
    (hp : ¬Primality.PerfectPower m) : ∃ p₀ p₁ : Component m, p₁≠p₀ := by
  obtain ⟨p,hp₀⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < m)
  by_cases hh : ∀ q∈m.primeFactors,q=p
  · have hs : m.factorization.support ⊆ {p} := by
      intro q hq
      rw [Nat.support_factorization] at hq
      exact Finset.mem_singleton.mpr (hh q hq)
    have hpow : p^(m.factorization p)=m := by
      have he := m.factorization.prod_of_support_subset hs (fun p e => p^e)
        (by intro i _; simp)
      simpa only [Finset.prod_singleton] using he.symm.trans (Nat.prod_factorization_pow_eq_self (by omega))
    have hprime := (Nat.mem_primeFactors.mp hp₀).1
    have hexp : m.factorization p≠0 := by
      apply Finsupp.mem_support_iff.mp
      simpa only [Nat.support_factorization] using hp₀
    by_cases he : m.factorization p=1
    · rw [he,pow_one] at hpow
      exact False.elim (hc (hpow ▸ hprime))
    · exact False.elim (hp ⟨p,m.factorization p,hprime.two_le,by omega,hpow⟩)
  · push Not at hh
    obtain ⟨q,hq,hne⟩ := hh
    exact ⟨⟨p,hp₀⟩,⟨q,hq⟩,fun h => hne (congrArg Subtype.val h)⟩

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

namespace NodeCircuit

@[simp] lemma top_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (top s w).eval (pack xs d)=xs.head?.getD (fun _=>false) := by
  rw [top,eval_comp,pending_pack,blockNet_eval,block_stackEncoding]
  cases xs <;> rfl

lemma popped_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) (h : xs.length ≤ s+1) :
    (popped s w).eval (pack xs d)=stackEncoding (s+1) w xs.tail := by
  rw [popped,eval_comp,pending_pack,stackPop_encoding xs h]

lemma quotient_pack {s w : ℕ} (a d : Basis w) (xs : List (Basis w)) :
    (bitsValue ((quotient s w).eval (pack (a::xs) d))).toNat =
      (bitsValue a).toNat/(bitsValue d).toNat := by
  rw [quotient,eval_comp,eval_pair,div_word,top_pack,divisor_pack]
  rfl

lemma split_pack {s w : ℕ} (a d : Basis w) (xs : List (Basis w)) (h : xs.length ≤ s) :
    (split s w).eval (pack (a::xs) d)=stackEncoding (s+1) w
      (d::(quotient s w).eval (pack (a::xs) d)::xs) := by
  rw [split,stackPush_encoding _ _ _ _
    (stackPush_encoding _ _ _ _ (popped_pack (a::xs) d (by simp;omega))),divisor_pack]
  rfl

lemma isPrime_pack {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w)) :
    (isPrime s w).eval (pack (a::xs) d) 0=true ↔ (bitsValue a).toNat.Prime := by
  rw [isPrime,eval_comp,top_pack]
  exact primeWord_value hw _

lemma isProper_pack {s w : ℕ} (hw : 0<w) (a d : Basis w) (xs : List (Basis w)) :
    (isProper s w).eval (pack (a::xs) d) 0=true ↔
      ProperDivisor (bitsValue a).toNat (bitsValue d).toNat := by
  rw [isProper,properOn_value hw,top_pack,divisor_pack]
  rfl

lemma isDone_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (isDone s w).eval (pack xs d) 0=true ↔
      (bitsValue (xs.head?.getD (fun _=>false))).toNat=0 := by
  rw [isDone,zeroWord_value,top_pack]

/-- Literal guarded stack update for one node of the recursive producer.
The source primality test is the Boolean AKS circuit, and division is a full
word division circuit. No semantic factorization operation is used here. -/
lemma next_pack_cons {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w))
    (h : xs.length ≤ s) (ha : 2 ≤ (bitsValue a).toNat) :
    (next s w).eval (pack (a::xs) d)=
      if (bitsValue a).toNat.Prime then stackEncoding (s+1) w xs
      else if ProperDivisor (bitsValue a).toNat (bitsValue d).toNat then
        stackEncoding (s+1) w (d::(quotient s w).eval (pack (a::xs) d)::xs)
      else stackEncoding (s+1) w (a::xs) := by
  rw [next,wordMux_eval,ite_eq_right (by
    rw [isDone_pack]
    simp only [List.head?_cons,Option.getD_some]
    omega),wordMux_eval,wordMux_eval,pending_pack,
    popped_pack (a::xs) d (by simp;omega),split_pack a d xs h]
  simp only [List.tail_cons]
  simp only [isPrime_pack hw,isProper_pack (by omega : 0<w)]

lemma emitted_pack_cons {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w)) :
    (emitted s w).eval (pack (a::xs) d)=
      if (bitsValue a).toNat.Prime then a else (fun _=>false) := by
  rw [emitted,wordMux_eval,top_pack]
  simp only [List.head?_cons,Option.getD_some,isPrime_pack hw]
  split_ifs
  · rfl
  · funext i
    simp [wordConstant]

lemma failed_pack_cons {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w))
    (ha : 2 ≤ (bitsValue a).toNat) :
    (failed s w).eval (pack (a::xs) d) 0=true ↔
      ¬(bitsValue a).toNat.Prime ∧ ¬ProperDivisor (bitsValue a).toNat (bitsValue d).toNat := by
  rw [failed,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,bnot_value,bnot_value,
    bnot_value,isDone_pack,isPrime_pack hw,isProper_pack (by omega : 0<w)]
  simp only [List.head?_cons,Option.getD_some]
  have h0 : (bitsValue a).toNat≠0 := by omega
  simp only [h0,not_false_eq_true,true_and]

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeStateCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
namespace NodeStateCircuit

lemma top_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (top s w).eval (pack xs ys b)=xs.head?.getD (fun _=>false) := by
  rw [top,eval_comp,pending_pack,blockNet_eval,block_stackEncoding]
  cases xs <;> rfl

lemma old_append {s w : ℕ} (x : Basis (width s w)) (d : Basis w) :
    (old s w).eval (Fin.append x d)=x := by
  funext i
  exact Fin.append_left _ _ i
lemma supplied_append {s w : ℕ} (x : Basis (width s w)) (d : Basis w) :
    (supplied s w).eval (Fin.append x d)=d := by
  funext i
  exact Fin.append_right _ _ i
lemma nodeInput_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) (d : Basis w) :
    (nodeInput s w).eval (Fin.append (pack xs ys b) d)=NodeCircuit.pack xs d := by
  rw [nodeInput,eval_pair,eval_comp,old_append,pending_pack,supplied_append]
  rfl

lemma nextBad_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) (d : Basis w)
    (hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack xs d) 0=false) :
    (nextBad s w).eval (Fin.append (pack xs ys b) d)=(fun _=>b) := by
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rw [nextBad,eval_bor,eval_comp,old_append,bad_pack,eval_comp,nodeInput_pack,hf,Bool.or_false]

lemma step_prime {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs ys : List (Basis w))
    (b : Bool) (hx : xs.length ≤ s) (hp : (bitsValue a).toNat.Prime) :
    (step s w).eval (Fin.append (pack (a::xs) ys b) d)=pack xs (a::ys) b := by
  have ha : 2 ≤ (bitsValue a).toNat := hp.two_le
  have he : (emission s w).eval (Fin.append (pack (a::xs) ys b) d)=a := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_pack_cons hw,ite_eq_left hp]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack (a::xs) ys b) d) 0 ≠ true := by
    intro hz
    have hh := (zeroWord_value (emission s w) _).mp hz
    rw [he] at hh
    omega
  have hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack (a::xs) d) 0=false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    exact ((NodeCircuit.failed_pack_cons hw a d xs ha).mp hh).1 hp
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_pack_cons hw _ _ _ hx ha,ite_eq_left hp,nextOutput,wordMux_eval,ite_eq_right hz,
    stackPush_encoding _ _ _ ys (by rw [eval_comp,old_append,output_pack]),he,
    nextBad_pack _ _ _ _ hf]
  rfl

lemma step_split {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs ys : List (Basis w))
    (b : Bool) (hx : xs.length ≤ s) (ha : 2 ≤ (bitsValue a).toNat) (hp : ¬(bitsValue a).toNat.Prime)
    (hd : ProperDivisor (bitsValue a).toNat (bitsValue d).toNat) :
    (step s w).eval (Fin.append (pack (a::xs) ys b) d)=
      pack (d::(NodeCircuit.quotient s w).eval (NodeCircuit.pack (a::xs) d)::xs) ys b := by
  have he : (emission s w).eval (Fin.append (pack (a::xs) ys b) d)=(fun _=>false) := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_pack_cons hw,ite_eq_right hp]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack (a::xs) ys b) d) 0=true := by
    rw [zeroWord_value,he]
    have hh : bitsValue (fun _ : Fin w=>false)=(0 : BitVec w) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [bitsValue_bit _ ⟨i,hi⟩]
      simp
    rw [hh]
    rfl
  have hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack (a::xs) d) 0=false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    exact ((NodeCircuit.failed_pack_cons hw a d xs ha).mp hh).2 hd
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_pack_cons hw _ _ _ hx ha,ite_eq_right hp,ite_eq_left hd,nextOutput,wordMux_eval,ite_eq_left hz,
    eval_comp,old_append,output_pack,nextBad_pack _ _ _ _ hf]
  rfl

end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


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

lemma rareNet_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (rareNet q W t d).eval (layout q W t d r) 0=true ↔ rare r.1 := by
  rw [rareNet,equalOn_value,rareWires_eval,wordConstant_eval]
  simp only [BitVec.toNat_ofNat,Nat.zero_mod,rare]
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
lemma tensorNetwork_eval {n q K : ℕ} (f : Fin K → BooleanNetwork n q) (x : Basis n) :
    (tensorNetwork f).eval x=tensorLayout q K (fun i => (f i).eval x) := by
  induction K with
  | zero => exact Subsingleton.elim _ _
  | succ K ih => rw [tensorNetwork,eval_pair,ih,tensorLayout_succ]; rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalMachine
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

namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

lemma current_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.currentNet t).eval (M.encoded x t h)=M.config x t h := by
  cases t with
  | zero=>rfl
  | succ t=>exact packed_targetRegister _ _

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

end BitArithmetic
end ExactQuantumFactoring


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
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_UniversalSplit
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
open Exactness RepeatedTrials OrderTrial
namespace UniversalSplit

lemma secondComponent {m : ℕ} (hm : Hard m) :
    ∃ p₁ : Component m,p₁≠firstComponent hm.1 := by
  classical
  obtain ⟨a,b,hne⟩ := exists_distinct_components hm.1 hm.2.1 hm.2.2.2
  by_cases ha : a=firstComponent hm.1
  · exact ⟨b,by simpa only [←ha] using hne⟩
  · exact ⟨a,ha⟩

lemma passed_divisor {n : ℕ} (hn : 128 ≤ n) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hc : ¬(bitsValue m).toNat.Prime)
    (r : Raw n) (hr : passed m r) :
    FactorController.ProperDivisor (bitsValue m).toNat (FixedSplit.divisor m r) := by
  classical
  have hh := hr
  unfold passed at hh
  split_ifs at hh with h
  · obtain ⟨p₁,hne⟩ := secondComponent h
    exact FixedSplit.passed_divisor hn m hm hc h.2.2.1 (firstComponent h.1) p₁ hne r hh
  · apply suppliedDivisor_good hm (bitsValue m).isLt hc
    intro ho hpow
    exact False.elim (h ⟨hm,hc,ho,hpow⟩)

end UniversalSplit
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

lemma query_pack (n s : ℕ) (a : Basis (n+1)) (xs ys : List (Basis (n+1))) (b : Bool) :
    (query n s).eval (NodeStateCircuit.pack (a::xs) ys b)=
      (resizeWord (n+1) n).eval a := by
  rw [query,eval_comp,NodeStateCircuit.top_pack]
  rfl
lemma query_value {n s : ℕ} (a : Basis (n+1)) (xs ys : List (Basis (n+1))) (b : Bool)
    (ha : (bitsValue a).toNat < 2^n) :
    (bitsValue ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b))).toNat=(bitsValue a).toNat := by
  rw [query_pack,resizeWord_value,BitVec.toNat_setWidth,Nat.mod_eq_of_lt ha]

lemma next_eq {n s : ℕ} (x : Basis (configWidth n s)) (r : FixedSplit.Raw n) :
    (machine n s).next x r=(NodeStateCircuit.step s (n+1)).eval
      (Fin.append x (decoded ((query n s).eval x) r)) := by
  rw [SplitMachine.next]
  change (update n s).eval _=_
  rw [update,eval_comp,eval_pair,eval_select,eval_comp,eval_select]
  apply congrArg (NodeStateCircuit.step s (n+1)).eval
  apply congrArg₂ Fin.append
  · funext i
    exact Fin.append_left _ _ i
  · change (FixedSplit.divisorNet n).eval _=(FixedSplit.divisorNet n).eval _
    apply congrArg (FixedSplit.divisorNet n).eval
    funext i
    exact Fin.append_right _ _ i

lemma next_prime {n s : ℕ} (hn : 128 ≤ n) (a : Basis (n+1)) (xs ys : List (Basis (n+1)))
    (b : Bool) (hx : xs.length ≤ s) (hp : (bitsValue a).toNat.Prime) (r : FixedSplit.Raw n) :
    (machine n s).next (NodeStateCircuit.pack (a::xs) ys b) r=
      NodeStateCircuit.pack xs (a::ys) b := by
  rw [next_eq]
  exact NodeStateCircuit.step_prime (by omega) _ _ _ _ _ hx hp

/-- A passed actual split advances the bounded node stack. Its inputs are the
runtime stack top and this very clock tick's retained raw outcome. -/
lemma next_split {n s : ℕ} (hn : 128 ≤ n) (a : Basis (n+1)) (xs ys : List (Basis (n+1)))
    (b : Bool) (hx : xs.length ≤ s) (ha : 2 ≤ (bitsValue a).toNat) (hb : (bitsValue a).toNat < 2^n)
    (hp : ¬(bitsValue a).toNat.Prime) (r : FixedSplit.Raw n)
    (hr : UniversalSplit.passed ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b)) r) :
    let q := (query n s).eval (NodeStateCircuit.pack (a::xs) ys b)
    let d := decoded q r
    (machine n s).next (NodeStateCircuit.pack (a::xs) ys b) r=
      NodeStateCircuit.pack (d::(NodeCircuit.quotient s (n+1)).eval
        (NodeCircuit.pack (a::xs) d)::xs) ys b ∧
      FactorController.ProperDivisor (bitsValue a).toNat (bitsValue d).toNat := by
  dsimp only
  have hq := query_value (s:=s) a xs ys b hb
  have hqm : 2 ≤ (bitsValue ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b))).toNat := by
    rw [hq]
    exact ha
  have he := decoded_value (by omega : 2 ≤ n) ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b)) r hqm
  have hd := UniversalSplit.passed_divisor hn ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b)) hqm
    (by rw [hq];exact hp) r hr
  rw [hq,←he] at hd
  refine ⟨?_,hd⟩
  rw [next_eq]
  exact NodeStateCircuit.step_split (by omega) _ _ _ _ _ hx ha hp hd

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeStateNil
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork

lemma zeroBasis_value (w : ℕ) : bitsValue (fun _ : Fin w=>false)=(0 : BitVec w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bitsValue_bit _ ⟨i,hi⟩]
  simp

namespace NodeCircuit
lemma done_nil (s w : ℕ) (d : Basis w) : (isDone s w).eval (pack [] d) 0=true := by
  rw [isDone_pack]
  simp only [List.head?_nil,Option.getD_none,zeroBasis_value]
  rfl
lemma notPrime_nil {s w : ℕ} (hw : 128 ≤ w) (d : Basis w) :
    (isPrime s w).eval (pack [] d) 0≠true := by
  intro h
  rw [isPrime,eval_comp] at h
  have hp := (primeWord_value hw ((top s w).eval (pack [] d))).mp h
  rw [top_pack] at hp
  simp only [List.head?_nil,Option.getD_none,zeroBasis_value] at hp
  exact Nat.not_prime_zero hp
lemma next_nil (s w : ℕ) (d : Basis w) :
    (next s w).eval (pack [] d)=stackEncoding (s+1) w [] := by
  rw [next,wordMux_eval,ite_eq_left (done_nil s w d),pending_pack]
lemma emitted_nil {s w : ℕ} (hw : 128≤w) (d : Basis w) :
    (emitted s w).eval (pack [] d)=(fun _=>false) := by
  rw [emitted,wordMux_eval,ite_eq_right (notPrime_nil hw d)]
  funext i
  simp [wordConstant]
lemma failed_nil (s w : ℕ) (d : Basis w) :
    (failed s w).eval (pack [] d) 0=false := by
  rw [failed,eval_band,eval_band,eval_bnot,done_nil]
  rfl
end NodeCircuit

namespace NodeStateCircuit
lemma step_nil {s w : ℕ} (hw : 128 ≤ w) (d : Basis w) (ys : List (Basis w)) (b : Bool) :
    (step s w).eval (Fin.append (pack [] ys b) d)=pack [] ys b := by
  have he : (emission s w).eval (Fin.append (pack [] ys b) d)=(fun _=>false) := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_nil hw]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack [] ys b) d) 0=true := by
    rw [zeroWord_value,he,zeroBasis_value]
    rfl
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_nil,nextOutput,wordMux_eval,ite_eq_left hz,eval_comp,old_append,output_pack,
    nextBad_pack _ _ _ _ (NodeCircuit.failed_nil s w d)]
  rfl
end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeProgress
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open BooleanNetwork BitArithmetic FactorController
namespace PhysicalNode

lemma length_le_weight (ms : List ℕ) (hm : ∀ m ∈ ms,2 ≤ m) : ms.length ≤ weight ms := by
  induction ms with
  | nil=>simp [weight]
  | cons m ms ih=>
    have hp := splitWeight_pos (hm m (by simp))
    have ht := ih (fun a ha=>hm a (by simp [ha]))
    simp only [List.length_cons,weight,List.map_cons,List.sum_cons] at *
    omega

lemma Good.length_le {n N f : ℕ} {xs ys : List (Basis (n+1))} (h : Good n N f xs ys) :
    xs.length ≤ f := by
  have hh := length_le_weight (values xs) (by
    intro m hm
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact (h.bounded a ha).1)
  have hl : (values xs).length=xs.length := List.length_map _
  rw [hl] at hh
  exact hh.trans h.clock

lemma next_nil {n s : ℕ} (hn : 128 ≤ n) (ys : List (Basis (n+1))) (b : Bool) (r : FixedSplit.Raw n) :
    (machine n s).next (NodeStateCircuit.pack [] ys b) r=NodeStateCircuit.pack [] ys b := by
  rw [next_eq]
  exact NodeStateCircuit.step_nil (by omega) _ _ _

/-- One literal machine step consumes one unit of the genuine prime-factor
weight whenever pending work is nonempty. Empty work stays empty. -/
theorem next_good {n N s k : ℕ} (hn : 128 ≤ n) (hk : k ≤ s)
    (xs ys : List (Basis (n+1))) (h : Good n N (k+1) xs ys) (r : FixedSplit.Raw n)
    (hr : UniversalSplit.passed ((query n s).eval (NodeStateCircuit.pack xs ys false)) r) :
    ∃ xs' ys', (machine n s).next (NodeStateCircuit.pack xs ys false) r=
      NodeStateCircuit.pack xs' ys' false ∧ Good n N k xs' ys' := by
  cases xs with
  | nil=>
    refine ⟨[],ys,next_nil hn ys false r,⟨h.bounded,h.primes,h.product,?_⟩⟩
    simp [weight]
  | cons a xs=>
    have ha := h.bounded a (by simp)
    have ht : ∀ x ∈ xs,2 ≤ (bitsValue x).toNat ∧ (bitsValue x).toNat<2^n :=
      fun x hx=>h.bounded x (by simp [hx])
    have hcap : xs.length ≤ s := by have hh:=h.length_le; simp only [List.length_cons] at hh;omega
    by_cases hp : (bitsValue a).toNat.Prime
    · refine ⟨xs,a::ys,next_prime hn a xs ys false hcap hp r,⟨ht,?_,?_,?_⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hp
        · exact h.primes z hz
      · have he := h.product
        simp only [values_cons,List.prod_cons] at he ⊢
        calc
          (values xs).prod*((bitsValue a).toNat*(values ys).prod)=
            ((bitsValue a).toNat*(values xs).prod)*(values ys).prod := by ac_rfl
          _=N := he
      · have hw := h.clock
        rw [values_cons,weight_prime _ _ hp] at hw
        omega
    · let q := (query n s).eval (NodeStateCircuit.pack (a::xs) ys false)
      let d := decoded q r
      let b := (NodeCircuit.quotient s (n+1)).eval (NodeCircuit.pack (a::xs) d)
      obtain ⟨he,hd⟩ := next_split hn a xs ys false hcap ha.1 ha.2 hp r hr
      change (machine n s).next (NodeStateCircuit.pack (a::xs) ys false) r=
        NodeStateCircuit.pack (d::b::xs) ys false at he
      change ProperDivisor (bitsValue a).toNat (bitsValue d).toNat at hd
      have hb : (bitsValue b).toNat=(bitsValue a).toNat/(bitsValue d).toNat :=
        NodeCircuit.quotient_pack a d xs
      have hquot := hd.quotient
      refine ⟨d::b::xs,ys,he,⟨?_,h.primes,?_,?_⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨by have hh:=hd.1;omega,hd.2.1.trans ha.2⟩
        · rcases List.mem_cons.mp hz with rfl | hz
          · rw [hb]
            exact ⟨hquot.1,hquot.2.1.trans ha.2⟩
          · exact ht z hz
      · have hh := h.product
        simp only [values_cons,List.prod_cons] at hh ⊢
        rw [hb,←Nat.mul_assoc,hd.quotient.2.2]
        exact hh
      · have hw := h.clock
        rw [values_cons,weight_split hd] at hw
        simpa only [values_cons,hb] using (show weight
          ((bitsValue d).toNat::(bitsValue a).toNat/(bitsValue d).toNat::values xs) ≤ k by omega)

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalNodeLaunch
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
namespace PhysicalNode

lemma startNet_eval (n : ℕ) (a : Basis n) :
    (startNet n).eval a=NodeStateCircuit.pack [natBasis (n+1) (bitsValue a).toNat] [] false := by
  have hr : (resizeWord n (n+1)).eval a=natBasis (n+1) (bitsValue a).toNat := by
    apply (bitsEquiv (n+1)).injective
    apply BitVec.eq_of_toNat_eq
    change (bitsValue ((resizeWord n (n+1)).eval a)).toNat=
      (bitsValue (natBasis (n+1) (bitsValue a).toNat)).toNat
    rw [resizeWord_value,BitVec.toNat_setWidth,natBasis_value]
  have hz : (Completion.zeros n ((2*n+1)*(n+1))).eval a=stackEncoding (2*n+1) (n+1) [] := by
    rw [Completion.zeros_eval]
    rfl
  rw [startNet,eval_pair,eval_pair,stackPush_encoding _ _ _ [] hz,hr,hz]
  apply congrArg (Fin.append _)
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  exact eval_constant false a 0

end PhysicalNode
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalNodeCompletion
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open BooleanNetwork BitArithmetic FactorController AuxiliaryTree OrderTrial
namespace PhysicalNode

lemma config_good {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (ht : t ≤ 2*n) (h : SplitMachine.Trace n t)
    (hp : (machine n (2*n)).passed (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h) :
    ∃ xs ys, (machine n (2*n)).config (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h=
      NodeStateCircuit.pack xs ys false ∧ Good n N (2*n-t) xs ys := by
  have hbw : N<2^(n+1) := hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have ha : (bitsValue (natBasis (n+1) N)).toNat=N := by
    rw [natBasis_value,Nat.mod_eq_of_lt hbw]
  induction t with
  | zero=>
    refine ⟨[natBasis (n+1) N],[],rfl,⟨?_,?_,?_,?_⟩⟩
    · intro a ha'
      have he : a=natBasis (n+1) N := List.mem_singleton.mp ha'
      subst a
      rw [ha]
      exact ⟨hN,hb⟩
    · simp
    · simp only [values_cons,values_nil,List.prod_cons,List.prod_nil,ha,mul_one]
    · have hs := splitWeight_bound (by omega : 0<N) hb
      simp only [values_cons,values_nil,ha,weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega
  | succ t ih=>
    obtain ⟨xs,ys,he,hg⟩ := ih (by omega) h.1 hp.1
    have hg' : Good n N ((2*n-(t+1))+1) xs ys := by
      convert hg using 1 <;> first | (with_reducible_and_instances rfl) | (omega)
    have hpass : UniversalSplit.passed ((query n (2*n)).eval (NodeStateCircuit.pack xs ys false)) h.2 := by
      have hh := hp.2
      change UniversalSplit.passed ((query n (2*n)).eval ((machine n (2*n)).config _ t h.1)) h.2 at hh
      rw [he] at hh
      exact hh
    obtain ⟨xs',ys',he',hg'⟩ := next_good hn (by omega : 2*n-(t+1) ≤ 2*n) xs ys hg' h.2 hpass
    refine ⟨xs',ys',?_,hg'⟩
    change (machine n (2*n)).next ((machine n (2*n)).config _ t h.1) h.2=_
    rw [he,he']

/-- Every passing actual history of the literal 2n-clock machine ends in a
complete prime list, without sticky failure. The input and all next queries are
actual measured-word encodings, not an oracle call to mathematical factorization. -/
theorem complete {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (h : SplitMachine.Trace n (2*n))
    (hp : (machine n (2*n)).passed (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h) :
    ∃ ys, (machine n (2*n)).config (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h=
      NodeStateCircuit.pack [] ys false ∧
      (∀ p ∈ values ys,p.Prime) ∧ (values ys).prod=N ∧ ys.length<n := by
  obtain ⟨xs,ys,he,hg⟩ := config_good hn hN hb (2*n) (le_refl _) h hp
  have hl := hg.length_le
  have hxs : xs=[] := List.length_eq_zero_iff.mp (by omega)
  subst xs
  have hpr : ∀ p ∈ values ys,p.Prime := by
    intro p hp'
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp'
    exact hg.primes a ha
  have hprod : (values ys).prod=N := by simpa only [values_nil,List.prod_nil,one_mul] using hg.product
  have hlen : (values ys).length=splitWeight N := (Nat.primeFactorsList_unique hprod hpr).length_eq
  have hlen' : ys.length<n := by
    have hb' := splitWeight_bound (by omega : 0<N) hb
    rw [values,List.length_map] at hlen
    omega
  exact ⟨ys,he,hpr,hprod,hlen'⟩

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SortingCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork
namespace SortedWords

lemma headNet_eval (w r : ℕ) (a : Basis w) (x : Basis (tensorWidth w r)) :
    (headNet w r).eval (Fin.append a x)=a := by
  funext i
  exact Fin.append_left _ _ _
lemma tailNet_eval (w r : ℕ) (a : Basis w) (x : Basis (tensorWidth w r)) :
    (tailNet w r).eval (Fin.append a x)=x := by
  funext i
  exact Fin.append_right _ _ _

lemma keepHead_eval {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r))
    (a : Basis w) (x : Basis (tensorWidth w r)) :
    (keepHead c).eval (Fin.append a x)=Fin.append a (c.eval x) := by
  rw [keepHead,eval_pair,eval_comp,headNet_eval,tailNet_eval]

lemma compareStep_eval (w r : ℕ) (a b : Basis w) (x : Basis (tensorWidth w r)) :
    (compareStep w r).eval (Fin.append a (Fin.append b x))=
      if LEWord a b then Fin.append a (Fin.append b x) else Fin.append b (Fin.append a x) := by
  have hc : (paddedPair (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))).eval
      (Fin.append a (Fin.append b x)) 0=true ↔ LEWord a b := by
    rw [paddedPair_value,headNet_eval,eval_comp,tailNet_eval,headNet_eval]
    rfl
  simp only [compareStep,eval_pair,wordMux_eval,eval_comp,headNet_eval,tailNet_eval]
  by_cases hab : LEWord a b
  · have ht := hc.mpr hab
    simp only [ite_eq_left ht,ite_eq_left hab]
  · have ht : ¬(paddedPair (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))).eval
        (Fin.append a (Fin.append b x)) 0=true := fun h=>hab (hc.mp h)
    simp only [ite_eq_right ht,ite_eq_right hab]

lemma insertNet_eval (w r : ℕ) (a : Basis w) (xs : List (Basis w)) (hx : xs.length=r) :
    (insertNet w r).eval (layout w (r+1) (a::xs))=layout w (r+1) (insert a xs) := by
  induction r generalizing a xs with
  | zero=>have he : xs=[] := List.length_eq_zero_iff.mp hx;subst xs;rfl
  | succ r ih=>
    cases xs with
    | nil=>simp at hx
    | cons b bs=>
      have hb : bs.length=r := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hx
      change (insertNet w (r+1)).eval (Fin.append a (Fin.append b (layout w r bs)))=_
      rw [insertNet,eval_comp,compareStep_eval,insert]
      split_ifs with hab
      · rw [keepHead_eval]
        change Fin.append a ((insertNet w r).eval (layout w (r+1) (b::bs)))=_
        rw [ih b bs hb]
        rfl
      · rw [keepHead_eval]
        change Fin.append b ((insertNet w r).eval (layout w (r+1) (a::bs)))=_
        rw [ih a bs hb]
        rfl
lemma sortNet_eval (w r : ℕ) (xs : List (Basis w)) (hx : xs.length=r) :
    (sortNet w r).eval (layout w r xs)=layout w r (sort xs) := by
  induction r generalizing xs with
  | zero=>have he : xs=[] := List.length_eq_zero_iff.mp hx;subst xs;rfl
  | succ r ih=>
    cases xs with
    | nil=>simp at hx
    | cons a as=>
      have ha : as.length=r := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hx
      change (sortNet w (r+1)).eval (Fin.append a (layout w r as))=_
      rw [sortNet,eval_comp,keepHead_eval,ih as ha]
      change (insertNet w r).eval (layout w (r+1) (a::sort as))=_
      rw [insertNet_eval w r a (sort as) ((sort_length as).trans ha)]
      rfl

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorList
attribute [-instance] _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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


namespace ExactQuantumFactoring.BitArithmetic.SortedWords

lemma layout_ofFn (w r : ℕ) (f : Fin r→Basis w) :
    layout w r (List.ofFn f)=tensorLayout w r f := by
  induction r with
  | zero=>rfl
  | succ r ih=>
    rw [List.ofFn_succ,layout,tensorLayout_succ]
    simp only [List.head?_cons,Option.getD_some,List.tail_cons]
    rw [ih]
    rfl

lemma ofFn_getD_pad {α : Type} (xs : List α) (d : α) (r : ℕ) (hlen : xs.length ≤ r) :
    List.ofFn (fun i : Fin r=>xs[i.val]?.getD d)=xs++List.replicate (r-xs.length) d := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_append,List.length_replicate]
    omega
  · intro i hi hj
    rw [List.getElem_ofFn]
    by_cases hx : i<xs.length
    · rw [List.getElem?_eq_getElem hx,Option.getD_some,List.getElem_append_left hx]
    · have hle : xs.length ≤ i := by omega
      rw [List.getElem?_eq_none hle,Option.getD_none,List.getElem_append_right hle,List.getElem_replicate]

lemma ofFn_map_getD_pad {α β : Type} (xs : List α) (d : α) (r : ℕ) (hlen : xs.length ≤ r) (f : α→β) :
    List.ofFn (fun i : Fin r=>f (xs[i.val]?.getD d))=
      xs.map f++List.replicate (r-xs.length) (f d) := by
  have h := congrArg (List.map f) (ofFn_getD_pad xs d r hlen)
  simpa only [List.map_ofFn,List.map_append,List.map_replicate,Function.comp_def] using h

end ExactQuantumFactoring.BitArithmetic.SortedWords


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalNodeOutput
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
namespace PhysicalNode

lemma resultField_pack (n : ℕ) (xs ys : List (Basis (n+1))) (b : Bool) (i : Fin n) :
    (resultField n i).eval (NodeStateCircuit.pack xs ys b)=
      shrink n (ys[i.val]?.getD (fun _=>false)) := by
  rw [resultField,eval_comp,eval_comp,NodeStateCircuit.output_pack,blockNet_eval,block_stackEncoding]
  rfl
lemma shrink_zero (n : ℕ) : shrink n (fun _=>false)=(fun _=>false) := by
  funext i
  simp only [shrink,resizeWord,eval_vector]
  rw [dite_eq_left (by omega)]
  rfl

lemma sortedOutput_pack (n : ℕ) (xs ys : List (Basis (n+1))) (b : Bool) (hlen : ys.length ≤ n) :
    (sortedOutput n).eval (NodeStateCircuit.pack xs ys b)=SortedWords.layout n n
      (SortedWords.sort (ys.map (shrink n)++List.replicate (n-ys.length) (fun _=>false))) := by
  rw [sortedOutput,eval_comp,tensorNetwork_eval]
  simp_rw [resultField_pack]
  rw [←SortedWords.layout_ofFn]
  rw [SortedWords.sortNet_eval _ _ _ List.length_ofFn,
    SortedWords.ofFn_map_getD_pad ys (fun _=>false) n hlen,shrink_zero]

lemma shrink_values {n : ℕ} (ys : List (Basis (n+1))) (hb : ∀ a∈ys,(bitsValue a).toNat<2^n) :
    SortedWords.numbers (ys.map (shrink n))=values ys := by
  simp only [SortedWords.numbers,values,List.map_map]
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_apply,shrink,resizeWord_value,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (hb a ha)]

/-- The actual retained node configuration admits an explicit polynomial
Boolean sorting/readout network. Its output is the LITERAL main-theorem
encoding, with exactly n fields, zero padding and multiplicities. -/
theorem complete_output {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (h : SplitMachine.Trace n (2*n))
    (hp : (machine n (2*n)).passed (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (sortedOutput n).eval
        ((machine n (2*n)).config (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h)=
          SortedWords.layout n n zs := by
  obtain ⟨ys,he,hpr,hprod,hlen⟩ := complete hn hN hb h hp
  have hyb : ∀ a∈ys,(bitsValue a).toNat<2^n := by
    intro a ha
    have hm : (bitsValue a).toNat∈values ys := List.mem_map.mpr ⟨a,ha,rfl⟩
    have hd : (bitsValue a).toNat∣N := by rw [←hprod];exact List.dvd_prod hm
    exact (Nat.le_of_dvd (by omega) hd).trans_lt hb
  have hv := shrink_values ys hyb
  refine ⟨SortedWords.sort (ys.map (shrink n)++List.replicate (n-ys.length) (fun _=>false)),?_,?_,?_⟩
  · simp only [SortedWords.sort_length,List.length_append,List.length_map,List.length_replicate]
    omega
  · have hc := SortedWords.sort_correct (N:=N) (r:=n) (ys.map (shrink n)) (by rw [hv];exact hpr)
      (by rw [hv];exact hprod) (by simp only [List.length_map];omega : (ys.map (shrink n)).length ≤ n)
    simpa only [List.length_map] using hc
  · rw [he,sortedOutput_pack _ _ _ _ hlen.le]

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeQueue
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
namespace PhysicalTree

lemma query_encoding (n : ℕ) (a : Basis n) (xs : List (Basis n)) :
    (query n).eval (stackEncoding (capacity n) n (a::xs))=a := by
  rw [query,blockNet_eval,block_stackEncoding]
  rfl
lemma old_append (n : ℕ) (x : Basis (configWidth n)) (y : Basis (NodeKernel.width n)) :
    (old n).eval (Fin.append x y)=x := by
  funext i
  exact Fin.append_left _ _ i
lemma localNode_append (n : ℕ) (x : Basis (configWidth n)) (y : Basis (NodeKernel.width n)) :
    (localNode n).eval (Fin.append x y)=y := by
  funext i
  exact Fin.append_right _ _ i

lemma fields_eval {n : ℕ} (z : Basis (NodeKernel.width n)) (xs : List (Basis n))
    (hlen : xs.length=n) (he : (nodeResult n).eval z=SortedWords.layout n n xs) :
    (fields n).map (fun a=>a.eval z)=xs := by
  have hpad := SortedWords.ofFn_getD_pad xs (fun _=>false) n hlen.le
  simp only [hlen,Nat.sub_self,List.replicate_zero,List.append_nil] at hpad
  have hl : SortedWords.layout n n xs=tensorLayout n n
      (fun i : Fin n=>xs[i.val]?.getD (fun _=>false)) := by
    calc
      _ = SortedWords.layout n n (List.ofFn (fun i : Fin n=>xs[i.val]?.getD (fun _=>false))) :=
        congrArg (SortedWords.layout n n) hpad.symm
      _ = _ := SortedWords.layout_ofFn _ _ _
  simp only [fields,List.map_ofFn,Function.comp_def,eval_comp,he,hl,tensorSelect_eval]
  exact hpad

lemma pushed_eval {n : ℕ} (hn : 2 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (z : Basis (NodeKernel.width n)) :
    (pushed n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) z)=
      stackEncoding (capacity n) n
        (ChildQueue.kids ((fields n).map (fun b=>b.eval z))++as) := by
  rw [pushed,eval_comp,eval_comp,eval_pair,localNode_append,eval_comp,old_append,
    stackPop_encoding _ hlen,ChildQueue.pushAll_eval hn,ChildQueue.queue_eval]
  rfl

lemma update_eval {n : ℕ} (hn : 2 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (ha : 2 ≤ (bitsValue a).toNat) (z : Basis (NodeKernel.width n)) :
    (update n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) z)=
      stackEncoding (capacity n) n
        (ChildQueue.kids ((fields n).map (fun b=>b.eval z))++as) := by
  have htest : (zeroWord ((old n).comp (query n))).eval
      (Fin.append (stackEncoding (capacity n) n (a::as)) z) 0≠true := by
    intro h
    rw [zeroWord_value,eval_comp,old_append,query_encoding] at h
    omega
  rw [update,wordMux_eval,ite_eq_right htest,pushed_eval hn a as hlen z]

lemma update_nil (n : ℕ) (z : Basis (NodeKernel.width n)) :
    (update n).eval (Fin.append (stackEncoding (capacity n) n []) z)=
      stackEncoding (capacity n) n [] := by
  have hq : (query n).eval (stackEncoding (capacity n) n [])=fun _=>false := by
    rw [query,blockNet_eval,block_stackEncoding]
    rfl
  have ht : (zeroWord ((old n).comp (query n))).eval
      (Fin.append (stackEncoding (capacity n) n []) z) 0=true := by
    rw [zeroWord_value,eval_comp,old_append,hq,zeroBasis_value]
    rfl
  rw [update,wordMux_eval,ite_eq_left ht,old_append]

/-- Passed physical local computation produces EXACT canonical children in the
physical outer queue. It does not use trueData to select or initialize_ a query. -/
theorem update_passed {n : ℕ} (hn : 128 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (ha : 2 ≤ (bitsValue a).toNat)
    (r : NodeKernel.Raw n) (hp : NodeKernel.passed a r) :
    ∃ kids : List (Basis n), SortedWords.numbers kids=AuxiliaryTree.children (bitsValue a).toNat ∧
      (update n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) (NodeKernel.encoding a r))=
        stackEncoding (capacity n) n (kids++as) := by
  have hp' : (PhysicalNode.machine n (2*n)).passed
      (NodeStateCircuit.pack [natBasis (n+1) (bitsValue a).toNat] [] false) (2*n) r := by
    simpa only [NodeKernel.passed,NodeKernel.start,PhysicalNode.startNet_eval] using hp
  obtain ⟨zs,hl,hc,he⟩ := PhysicalNode.complete_output hn ha (bitsValue a).isLt r hp'
  have hf : (fields n).map (fun b=>b.eval (NodeKernel.encoding a r))=zs := by
    apply fields_eval _ zs hl
    rw [nodeResult,eval_comp,NodeKernel.encoding,SplitMachine.current_encoded,
      NodeKernel.start,PhysicalNode.startNet_eval]
    exact he
  refine ⟨ChildQueue.kids zs,ChildQueue.kids_correct (by omega) ha zs hc,?_⟩
  rw [update_eval (by omega : 2 ≤ n) a as hlen ha,hf]

end PhysicalTree
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
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

lemma fields_nodeWords (n : ℕ) (z : Basis (NodeKernel.width n)) :
    (fields n).map (fun a=>a.eval z)=nodeWords n z := by
  rw [fields,List.map_ofFn]
  rfl
lemma numbers_nodeWords (n : ℕ) (z : Basis (NodeKernel.width n)) :
    SortedWords.numbers (nodeWords n z)=candidateWords (resultFields n) z := by
  simp only [SortedWords.numbers,nodeWords,candidateWords,List.map_ofFn,Function.comp_def]

lemma node_verified_of_passed {n : ℕ} (hn : 128 ≤ n) (q : Basis n)
    (hq : (bitsValue q).toNat=0 ∨ 2 ≤ (bitsValue q).toNat)
    (r : NodeKernel.Raw n) (hp : NodeKernel.passed q r) : NodeVerified q r := by
  rcases hq with hz | ha
  · exact Or.inl hz
  · right
    have hp' : (PhysicalNode.machine n (2*n)).passed
        (NodeStateCircuit.pack [natBasis (n+1) (bitsValue q).toNat] [] false) (2*n) r := by
      simpa only [NodeKernel.passed,NodeKernel.start,PhysicalNode.startNet_eval] using hp
    obtain ⟨zs,hl,hc,he⟩ := PhysicalNode.complete_output hn ha (bitsValue q).isLt r hp'
    have hf : nodeWords n (NodeKernel.encoding q r)=zs := by
      rw [←fields_nodeWords]
      apply fields_eval _ zs hl
      rw [nodeResult,eval_comp,NodeKernel.encoding,SplitMachine.current_encoded,
        NodeKernel.start,PhysicalNode.startNet_eval]
      exact he
    rw [hf]
    exact hc

/-- The queue remains canonical for ANY retrospectively verified local result,
not only for results obtained on the all-good event. -/
theorem update_verified {n : ℕ} (hn : 128 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (ha : 2 ≤ (bitsValue a).toNat)
    (r : NodeKernel.Raw n) (hv : NodeVerified a r) :
    ∃ kids : List (Basis n), SortedWords.numbers kids=AuxiliaryTree.children (bitsValue a).toNat ∧
      (update n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) (NodeKernel.encoding a r))=
        stackEncoding (capacity n) n (kids++as) := by
  rcases hv with hz | hc
  · omega
  · refine ⟨ChildQueue.kids (nodeWords n (NodeKernel.encoding a r)),
      ChildQueue.kids_correct (by omega) ha _ hc,?_⟩
    rw [update_eval (by omega : 2 ≤ n) a as hlen ha,fields_nodeWords]

end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma rowQuery_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.rowQuery t).eval (M.encoded x (t+1) (h,r))=M.query.eval (M.config x t h) := by
  rw [rowQuery,eval_comp,eval_comp,M.previousNet_encoded,M.current_encoded]
lemma rowFields_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) (i : Fin n) :
    (M.rowFields t i).eval (M.encoded x (t+1) (h,r))=
      (PhysicalTree.resultFields n i).eval (NodeKernel.encoding (M.query.eval (M.config x t h)) r) := by
  rw [rowFields,eval_comp,M.lastNodeNet_encoded]
lemma rowVerifiedNet_encoded (hn : 128 ≤ n) (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.rowVerifiedNet t).eval (M.encoded x (t+1) (h,r)) 0=true ↔
      PhysicalTree.NodeVerified (M.query.eval (M.config x t h)) r := by
  rw [rowVerifiedNet,eval_bor,Bool.or_eq_true,zeroWord_value,
    factorVerifierOn_correct hn,M.rowQuery_encoded,PhysicalTree.NodeVerified,
    PhysicalTree.numbers_nodeWords]
  simp only [candidateWords,M.rowFields_encoded]

/-- A literal, bounded Boolean verifier of every actual retained root/node
factor list. No predicate is silently converted to an oracle gate. -/
theorem verifiedNet_encoded (hn : 128 ≤ n) (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.verifiedNet t).eval (M.encoded x t h) 0=true ↔ M.verified x t h := by
  induction t with
  | zero=>simp [verifiedNet,verified]
  | succ t ih=>
    rw [verifiedNet,eval_band,Bool.and_eq_true,eval_comp,M.previousNet_encoded,
      ih,M.rowVerifiedNet_encoded hn]
    rfl

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TraceBounds
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

namespace AuxiliaryTree

lemma sum_map_range (xs : List ℕ) (f : ℕ→ℕ→ℕ) (d : ℕ) :
    (xs.map (fun a => ∑ k∈Finset.range d, f a k)).sum =
      ∑ k∈Finset.range d, (xs.map (fun a => f a k)).sum := by
  induction xs with
  | nil => simp
  | cons a as ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

lemma visits_length (depth m : ℕ) :
    (visits depth m).length = ∑ k∈Finset.range depth, (level m k).length := by
  induction depth generalizing m with
  | zero => simp [visits]
  | succ d ih =>
    rw [visits,List.length_cons,List.length_flatMap]
    simp_rw [ih]
    rw [sum_map_range,Finset.sum_range_succ']
    simp only [level,List.length_flatMap,List.length_singleton]

lemma visits_length_le {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (depth : ℕ) :
    (visits depth m).length  ≤  depth*n := by
  rw [visits_length]
  calc
    _  ≤  ∑ _k∈Finset.range depth,n := Finset.sum_le_sum (fun k _ => (level_length_lt (k:=k) hm hb).le)
    _ = depth*n := by simp

end AuxiliaryTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OccurrenceQueue
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


namespace ExactQuantumFactoring.AuxiliaryTree

lemma preorder_eq (m : ℕ) : preorder m=m::(children m).flatMap preorder := by
  rw [preorder]
  congr 1
  rw [List.flatMap_subtype (g:=preorder) (fun _ _=>rfl),List.unattach_attach]

lemma visits_eq_preorder {m depth : ℕ} (hd : level m depth=[]) :
    visits depth m=preorder m := by
  induction depth generalizing m with
  | zero=>simp only [level,List.cons_ne_self] at hd
  | succ d ih=>
    rw [visits,preorder_eq]
    congr 1
    apply List.flatMap_congr
    intro a ha
    exact ih (DataProducer.child_level_empty hd ha)

lemma preorder_length_le {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) :
    (preorder m).length ≤ 2*n^2 := by
  rw [←visits_eq_preorder (level_empty hm hb)]
  simpa only [pow_two,Nat.mul_assoc] using visits_length_le hm hb (2*n)

lemma forest_advance (m : ℕ) (ms : List ℕ) :
    forest (m::ms)=m::forest (advance (m::ms)) := by
  simp only [forest,List.flatMap_cons,preorder_eq,List.cons_append,advance,List.flatMap_append]

lemma queue_length_le (xs : List ℕ) : xs.length ≤ (forest xs).length := by
  induction xs with
  | nil=>simp [forest]
  | cons m ms ih=>
    rw [forest_advance,List.length_cons,List.length_cons]
    have he : (forest (advance (m::ms))).length=
        ((children m).flatMap preorder).length+(forest ms).length := by
      simp only [forest,advance,List.flatMap_append,List.length_append]
    rw [he]
    omega

lemma forest_run (t : ℕ) (xs : List ℕ) : forest (run t xs)=(forest xs).drop t := by
  induction t generalizing xs with
  | zero=>rfl
  | succ t ih=>
    rw [run,ih]
    cases xs with
    | nil=>simp [advance,forest]
    | cons m ms=>rw [forest_advance,List.drop_succ_cons]

lemma forest_eq_nil_iff {xs : List ℕ} : forest xs=[] ↔ xs=[] := by
  constructor
  · intro h
    have hh := queue_length_le xs
    rw [h,List.length_nil] at hh
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rintro rfl
    rfl

/-- Exactly the polynomial clock used by the physical queue suffices for EVERY
occurrence, not just every distinct label. -/
theorem run_complete {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) : run (2*n^2) [m]=[] := by
  apply forest_eq_nil_iff.mp
  rw [forest_run]
  have he : forest [m]=preorder m := by simp [forest]
  rw [he]
  exact List.drop_eq_nil_of_le (preorder_length_le hm hb)

lemma run_queue_length {m n t : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) :
    (run t [m]).length ≤ 2*n^2 := by
  have h := queue_length_le (run t [m])
  rw [forest_run] at h
  have he : forest [m]=preorder m := by simp [forest]
  rw [he,List.length_drop] at h
  exact h.trans ((Nat.sub_le _ _).trans (preorder_length_le hm hb))

lemma advance_bounds {xs : List ℕ} {B : ℕ} (hx : ∀ a∈xs,2 ≤ a ∧ a < B) :
    ∀ a∈advance xs,2 ≤ a ∧ a < B := by
  cases xs with
  | nil=>simp [advance]
  | cons m ms=>
    intro a ha
    have hm := hx m (by simp)
    rcases List.mem_append.mp ha with hd | ht
    · have hb := child_bounds hd
      exact ⟨hb.1,hb.2.trans hm.2⟩
    · exact hx a (by simp [ht])

lemma run_bounds {xs : List ℕ} {B : ℕ} (hx : ∀ a∈xs,2 ≤ a ∧ a < B) (t : ℕ) :
    ∀ a∈run t xs,2 ≤ a ∧ a < B := by
  induction t generalizing xs with
  | zero=>exact hx
  | succ t ih=>exact ih (advance_bounds hx)

lemma run_succ_right (t : ℕ) (xs : List ℕ) : run (t+1) xs=advance (run t xs) := by
  induction t generalizing xs with
  | zero=>rfl
  | succ t ih=>rw [run,ih];rfl

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QueueCoverage
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


namespace ExactQuantumFactoring.AuxiliaryTree

lemma head_or_advance {xs : List ℕ} {a : ℕ} (ha : a∈xs) :
    a=xs.headD 0 ∨ a∈advance xs := by
  cases xs with
  | nil=>simp at ha
  | cons b bs=>
    rcases List.mem_cons.mp ha with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_append_right _ h)
lemma children_head (xs : List ℕ) {a : ℕ} (ha : a∈children (xs.headD 0)) : a∈advance xs := by
  cases xs with
  | nil=>simp [children] at ha
  | cons b bs=>exact List.mem_append_left _ ha

/-- Everything pending before a step is either the recorded head or remains
pending afterwards. This assertion does not search the mathematical tree. -/
lemma seen_or_pending_step {xs : List ℕ} {t a : ℕ}
    (h : a∈seen xs t ∨ a∈run t xs) : a∈seen xs (t+1) ∨ a∈run (t+1) xs := by
  rcases h with h | h
  · exact Or.inl (List.mem_cons_of_mem _ h)
  · rcases head_or_advance h with h | h
    · exact Or.inl (List.mem_cons.mpr (Or.inl h))
    · exact Or.inr (by rw [run_succ_right];exact h)

lemma original_covered (xs : List ℕ) (t : ℕ) {a : ℕ} (ha : a∈xs) :
    a∈seen xs t ∨ a∈run t xs := by
  induction t with
  | zero=>exact Or.inr ha
  | succ t ih=>exact seen_or_pending_step ih

/-- Every required p−1 child of every already visited node is itself either
visited or still on the actual occurrence queue. -/
lemma children_covered (xs : List ℕ) (t : ℕ) {m a : ℕ}
    (hm : m∈seen xs t) (ha : a∈children m) : a∈seen xs t ∨ a∈run t xs := by
  induction t with
  | zero=>simp [seen] at hm
  | succ t ih=>
    rcases List.mem_cons.mp hm with hm | hm
    · have hx : a∈advance (run t xs) := children_head _ (by simpa only [←hm] using ha)
      exact Or.inr (by rw [run_succ_right];exact hx)
    · exact seen_or_pending_step (ih hm)

lemma completed_root {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) : m∈seen [m] (2*n^2) := by
  have h:=original_covered [m] (2*n^2) (by simp : m∈[m])
  rw [run_complete hm hb] at h
  simpa only [List.not_mem_nil,or_false] using h
lemma completed_children {m n a b : ℕ} (hm : 2 ≤ m) (hb : m < 2^n)
    (ha : a∈seen [m] (2*n^2)) (hc : b∈children a) : b∈seen [m] (2*n^2) := by
  have h:=children_covered [m] (2*n^2) ha hc
  rw [run_complete hm hb] at h
  simpa only [List.not_mem_nil,or_false] using h
end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeCompletion
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
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

/-- On the actual all-passed raw history, the literal physical pending queue is
exactly the remaining canonical occurrence preorder. This is a proof invariant,
not a precomputed queue or advice to the circuit. -/
theorem queue_invariant {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hp : (machine n).passed (initialQueue n N) t h) :
    (machine n).config (initialQueue n N) t h=
      stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.run t [N])) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    obtain ⟨h,r⟩ := h
    have hi := ih h hp.1
    have hbounds := AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n)
      (by
        intro a ha
        have he : a=N := by simpa using ha
        subst a
        exact ⟨hN,hb⟩) t
    have hlen := AuxiliaryTree.run_queue_length (t:=t) hN hb
    rw [NodeMachine.config,NodeMachine.next,hi]
    change (update n).eval (Fin.append _ (NodeKernel.encoding ((query n).eval _) r))=_
    cases he : AuxiliaryTree.run t [N] with
    | nil=>
      change (update n).eval (Fin.append (stackEncoding (capacity n) n []) _)=_
      rw [update_nil,AuxiliaryTree.run_succ_right,he]
      rfl
    | cons m ms=>
      have hm := hbounds m (by rw [he];simp)
      have hv : (bitsValue (natBasis n m)).toNat=m := by rw [natBasis_value,Nat.mod_eq_of_lt hm.2]
      have hc : (natBasis n m::canonicalWords n ms).length ≤ capacity n := by
        rw [he,List.length_cons] at hlen
        simp only [List.length_cons,canonical_length]
        unfold capacity
        omega
      have hr : NodeKernel.passed (natBasis n m) r := by
        have hh := hp.2
        change NodeKernel.passed ((query n).eval ((machine n).config (initialQueue n N) t h)) r at hh
        rw [hi,he] at hh
        change NodeKernel.passed ((query n).eval (stackEncoding (capacity n) n
          (natBasis n m::canonicalWords n ms))) r at hh
        rw [query_encoding] at hh
        exact hh
      obtain ⟨ks,hk,hu⟩ := update_passed hn (natBasis n m) (canonicalWords n ms) hc
        (by rw [hv];exact hm.1) r hr
      have hks : ks=canonicalWords n (AuxiliaryTree.children m) := by
        rw [hv] at hk
        rw [←canonical_numbers ks,hk]
      change (update n).eval (Fin.append (stackEncoding (capacity n) n
        (natBasis n m::canonicalWords n ms))
          (NodeKernel.encoding ((query n).eval (stackEncoding (capacity n) n
            (natBasis n m::canonicalWords n ms))) r))=_
      rw [query_encoding,hu,hks,AuxiliaryTree.run_succ_right,he]
      change stackEncoding (capacity n) n
        (canonicalWords n (AuxiliaryTree.children m)++canonicalWords n ms)=
        stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.children m++ms))
      rw [canonical_append]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_VerifiedTreeCompletion
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
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

/-- On any retrospectively verified raw history, the literal physical pending queue is
exactly the remaining canonical occurrence preorder. This is a proof invariant,
not a precomputed queue or advice to the circuit. -/
theorem verified_queue_invariant {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hp : (machine n).verified (initialQueue n N) t h) :
    (machine n).config (initialQueue n N) t h=
      stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.run t [N])) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    obtain ⟨h,r⟩ := h
    have hi := ih h hp.1
    have hbounds := AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n)
      (by
        intro a ha
        have he : a=N := by simpa using ha
        subst a
        exact ⟨hN,hb⟩) t
    have hlen := AuxiliaryTree.run_queue_length (t:=t) hN hb
    rw [NodeMachine.config,NodeMachine.next,hi]
    change (update n).eval (Fin.append _ (NodeKernel.encoding ((query n).eval _) r))=_
    cases he : AuxiliaryTree.run t [N] with
    | nil=>
      change (update n).eval (Fin.append (stackEncoding (capacity n) n []) _)=_
      rw [update_nil,AuxiliaryTree.run_succ_right,he]
      rfl
    | cons m ms=>
      have hm := hbounds m (by rw [he];simp)
      have hv : (bitsValue (natBasis n m)).toNat=m := by rw [natBasis_value,Nat.mod_eq_of_lt hm.2]
      have hc : (natBasis n m::canonicalWords n ms).length ≤ capacity n := by
        rw [he,List.length_cons] at hlen
        simp only [List.length_cons,canonical_length]
        unfold capacity
        omega
      have hr : NodeVerified (natBasis n m) r := by
        have hh := hp.2
        change NodeVerified ((query n).eval ((machine n).config (initialQueue n N) t h)) r at hh
        rw [hi,he] at hh
        change NodeVerified ((query n).eval (stackEncoding (capacity n) n
          (natBasis n m::canonicalWords n ms))) r at hh
        rw [query_encoding] at hh
        exact hh
      obtain ⟨ks,hk,hu⟩ := update_verified hn (natBasis n m) (canonicalWords n ms) hc
        (by rw [hv];exact hm.1) r hr
      have hks : ks=canonicalWords n (AuxiliaryTree.children m) := by
        rw [hv] at hk
        rw [←canonical_numbers ks,hk]
      change (update n).eval (Fin.append (stackEncoding (capacity n) n
        (natBasis n m::canonicalWords n ms))
          (NodeKernel.encoding ((query n).eval (stackEncoding (capacity n) n
            (natBasis n m::canonicalWords n ms))) r))=_
      rw [query_encoding,hu,hks,AuxiliaryTree.run_succ_right,he]
      change stackEncoding (capacity n) n
        (canonicalWords n (AuxiliaryTree.children m)++canonicalWords n ms)=
        stackEncoding (capacity n) n (canonicalWords n (AuxiliaryTree.children m++ms))
      rw [canonical_append]


/-- Every good chronological run passes the literal complete-node verification.
The converse is deliberately NOT asserted: local filters still must be checked. -/
theorem passed_verified {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hp : (machine n).passed (initialQueue n N) t h) :
    (machine n).verified (initialQueue n N) t h := by
  induction t with
  | zero=>trivial
  | succ t ih=>
    refine ⟨ih h.1 hp.1,?_⟩
    apply node_verified_of_passed hn _ _ h.2 hp.2
    have hi := queue_invariant hn hN hb t h.1 hp.1
    change (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h.1))).toNat=0 ∨
      2 ≤ (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h.1))).toNat
    rw [hi]
    have hbounds := AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n) (by
      intro a ha
      have he : a=N := by simpa using ha
      subst a
      exact ⟨hN,hb⟩) t
    cases he : AuxiliaryTree.run t [N] with
    | nil=>
      left
      change (bitsValue ((query n).eval (stackEncoding (capacity n) n []))).toNat=0
      rw [query,blockNet_eval,block_stackEncoding]
      simp only [List.getElem?_nil,Option.getD_none,zeroBasis_value]
      rfl
    | cons a as=>
      right
      have ha := hbounds a (by rw [he];simp)
      change 2 ≤ (bitsValue ((query n).eval (stackEncoding (capacity n) n
        (natBasis n a::canonicalWords n as)))).toNat
      rw [query_encoding,natBasis_value,Nat.mod_eq_of_lt ha.2]
      exact ha.1

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalDataLog
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
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma dataLog_correct (x : Basis c) (t : ℕ) (h : Trace n t) (hv : M.verified x t h) :
    ∀ a∈M.dataLog x t h, a.1=0 ∨ CorrectEncoding a.1 n a.2 := by
  induction t with
  | zero=>simp only [dataLog,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ t ih=>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hv.2
    · exact ih h.1 hv.1 a ha
end NodeMachine
namespace PhysicalTree

lemma verified_query_value {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t h) :
    (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h))).toNat=
      (AuxiliaryTree.run t [N]).headD 0 := by
  rw [verified_queue_invariant hn hN hb t h hv]
  have hbounds:=AuxiliaryTree.run_bounds (xs:=[N]) (B:=2^n) (by
    intro a ha
    have he : a=N := by simpa using ha
    subst a
    exact ⟨hN,hb⟩) t
  cases he : AuxiliaryTree.run t [N] with
  | nil=>
    change (bitsValue ((query n).eval (stackEncoding (capacity n) n []))).toNat=0
    rw [query,blockNet_eval,block_stackEncoding]
    simp only [List.getElem?_nil,Option.getD_none,zeroBasis_value]
    rfl
  | cons a as=>
    have ha:=hbounds a (by rw [he];simp)
    change (bitsValue ((query n).eval (stackEncoding (capacity n) n
      (natBasis n a::canonicalWords n as)))).toNat=a
    rw [query_encoding,natBasis_value,Nat.mod_eq_of_lt ha.2]

/-- The labels on the actual verified physical history are exactly the
occurrence-preserving canonical traversal, including its zero padding. -/
lemma verified_dataLog_labels {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (t : ℕ) (h : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t h) :
    ((machine n).dataLog (initialQueue n N) t h).map Prod.fst=AuxiliaryTree.seen [N] t := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    change (bitsValue ((query n).eval ((machine n).config (initialQueue n N) t h.1))).toNat::
      List.map Prod.fst ((machine n).dataLog (initialQueue n N) t h.1)=_
    rw [verified_query_value hn hN hb t h.1 hv.1,ih h.1 hv.1]
    rfl

theorem verified_complete_log {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N < 2^n)
    (h : NodeMachine.Trace n (2*n^2))
    (hv : (machine n).verified (initialQueue n N) (2*n^2) h) :
    CompleteLog n N ((machine n).dataLog (initialQueue n N) (2*n^2) h) := by
  have he:=verified_dataLog_labels hn hN hb (2*n^2) h hv
  refine ⟨?_,(machine n).dataLog_correct _ _ _ hv,?_⟩
  · rw [he]
    exact AuxiliaryTree.completed_root hN hb
  · intro a ha d hd
    rw [he]
    apply AuxiliaryTree.completed_children hN hb (a:=a.1) _ hd
    rw [←he]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedTreeFilter
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
namespace PhysicalTree

/-- A fully assembled same-history Boolean flag on the actual physical tree.
Completeness of the factor table is derived from its literal verification;
it is not a hypothesis of this flag specification. -/
theorem acceptedNet_iff_passed {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (h : NodeMachine.Trace n (2*n^2)) :
    ((machine n).acceptedNet (by omega) (2*n^2)).eval
      ((machine n).encoded (initialQueue n N) (2*n^2) h) 0=true ↔
      (machine n).passed (initialQueue n N) (2*n^2) h := by
  rw [NodeMachine.acceptedNet,eval_band,Bool.and_eq_true,(machine n).verifiedNet_encoded hn]
  constructor
  · rintro ⟨hv,hf⟩
    exact (treePrefixFilter_passed hn hN hb (2*n^2) (2*n^2) h h (select id)
      (verified_complete_log hn hN hb h hv) hv (fun _ ha=>ha) (by rfl)).mp hf
  · intro hp
    have hv:=passed_verified hn hN hb (2*n^2) h hp
    refine ⟨hv,?_⟩
    exact (treePrefixFilter_passed hn hN hb (2*n^2) (2*n^2) h h (select id)
      (verified_complete_log hn hN hb h hv) hv (fun _ ha=>ha) (by rfl)).mpr hp

lemma acceptedNet_iff_accepted {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (h : NodeMachine.Trace n (2*n^2)) :
    ((machine n).acceptedNet (by omega) (2*n^2)).eval
      ((machine n).encoded (initialQueue n N) (2*n^2) h) 0=true ↔ accepted (N:=N) (by omega) h :=
  (acceptedNet_iff_passed hn hN hb h).trans (accepted_iff_passed hn hN hb h).symm
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedQuarterFilter
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
namespace PhysicalTree

lemma paddedHistory_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedHistory n).eval (paddedEncoding n N r)=
      (machine n).encoded (initialQueue n N) (2*n^2) r.1 := by
  simp only [paddedHistory,eval_comp,eval_select,Function.comp_def,paddedEncoding,
    Fin.append_left,launchHistory,launchEncoding]
  exact packed_targetRegister _ _
lemma paddedInput_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedInput n).eval (paddedEncoding n N r)=natBasis n N := by
  simp only [paddedInput,eval_comp,eval_select,Function.comp_def,paddedEncoding,
    Fin.append_left,launchInput,launchEncoding]
  exact packed_first _ _
lemma paddedPad_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedPad n).eval (paddedEncoding n N r)=tensorLayout n (padding n) r.2 := by
  funext i
  simp only [paddedPad,eval_select,Function.comp_apply,paddedEncoding,Fin.append_right]

lemma padFlag_eval (n : ℕ) (r : PadRaw n) :
    (padFlag n).eval (tensorLayout n (padding n) r) 0=true ↔ padPassed r := by
  simp only [padFlag,all_eval,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
    bnot_value,zeroWord_value,tensorSelect_eval,padPassed,Completion.rare]

lemma paddedFlag_eval {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : PaddedRaw n) :
    (paddedFlag n (by omega)).eval (paddedEncoding n N r) 0=true ↔
      paddedAccepted (N:=N) (by omega) r := by
  rw [paddedFlag,eval_band,Bool.and_eq_true,eval_comp,paddedHistory_eval,
    acceptedNet_iff_accepted hn hN hb,eval_comp,paddedPad_eval,padFlag_eval]
  rfl

lemma quarterOrd_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterOrd n).eval (quarterEncoding n N r)=paddedEncoding n N r.2.1 :=
  Completion.ordinaryWires_eval (r.1,paddedEncoding n N r.2.1,r.2.2)
lemma quarterGuess_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterGuess n).eval (quarterEncoding n N r)=r.2.2.1 :=
  Completion.guessWires_eval (r.1,paddedEncoding n N r.2.1,r.2.2)
lemma quarterCoin_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterCoin n).eval (quarterEncoding n N r)=r.2.2.2 :=
  Completion.retentionWires_eval (r.1,paddedEncoding n N r.2.1,r.2.2)
lemma quarterRare_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterRare n).eval (quarterEncoding n N r) 0=true ↔ Completion.rare r.1 :=
  Completion.rareNet_eval (r.1,paddedEncoding n N r.2.1,r.2.2)

lemma quarterKeep_eval (n N : ℕ) (p : ℚ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterKeep n p).eval (quarterEncoding n N r) 0=true ↔
      Completion.threshold p r.2.2.2 := by
  rw [quarterKeep,retentionNet_value]
  simp only [RatExpr.eval_const,NatExpr.eval,quarterCoin_eval,Completion.threshold]

lemma quarterGuessFlag_eval {n N : ℕ} (hn : 128≤n) (hb : N<2^n)
    (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterGuessFlag n).eval (quarterEncoding n N r) 0=true ↔
      CorrectEncoding N n (guessWords n r.2.2.1) := by
  rw [quarterGuessFlag,eval_comp,eval_pair,eval_comp,quarterOrd_eval,paddedInput_eval,
    quarterGuess_eval,guessVerifier_correct hn,natBasis_value,Nat.mod_eq_of_lt hb]

/-- The literal Boolean flag for the source's exact quarter event. All factor
and order tests read the actual retained history, not an ideal initialized table. -/
theorem quarterFlag_eval_oai {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterFlag n (by omega)).eval (quarterEncoding n N r) 0=true ↔
      Quarter.passed N (paddedAccepted (N:=N) (by omega)) r := by
  simp only [quarterFlag,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    bnot_value,quarterRare_eval,eval_comp,quarterOrd_eval,
    paddedFlag_eval hn hN hb,quarterKeep_eval,quarterGuessFlag_eval hn hb,
    Quarter.passed,Quarter.ordinaryPass,Quarter.guessPass]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.PhysicalTree.quarterFlag_eval_oai := @OAI.ExactQuantumFactoring.PhysicalTree.quarterFlag_eval_oai
