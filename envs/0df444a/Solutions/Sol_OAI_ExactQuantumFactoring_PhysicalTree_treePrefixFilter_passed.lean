-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:13:07.274976+00:00
-- url     : https://prove2.me/submissions/f98ae756-6c11-406f-8737-674148e3e17a

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
import Theorems.Thm_OAI_ExactQuantumFactoring_NodeMachine_retainedOrderFilter_exact

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_LevelIndependence
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
namespace ExactQuantumFactoring

/-- Exact product formula used in the source's retrospective F computation. -/
theorem allEqualLevel_card {ι T : Type*} {G : ι → Type*} [Fintype ι] [Fintype T]
    [∀ i, Fintype (G i)] [DecidableEq T] [DecidableEq ι] (i₀ : ι) (f : ∀ i, G i → T) :
    Fintype.card {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} =
      ∑ t : T, ∏ i : ι, Fintype.card {x : G i // f i x = t} := by
  classical
  rw [Fintype.card_congr (allEqualLevelEquiv i₀ f), Fintype.card_sigma]
  congr 1
  funext t
  exact Fintype.card_pi

end ExactQuantumFactoring


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

/-- Divisibility cannot increase the 2-adic valuation. -/
theorem level_le_of_dvd {d r : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) :
    padicValNat 2 d ≤ padicValNat 2 r := by
  rcases hdr with ⟨k, rfl⟩
  rw [padicValNat.mul (left_ne_zero_of_mul hr) (right_ne_zero_of_mul hr)]
  omega

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LevelCounts
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
namespace ExactQuantumFactoring

/-- Dividing a positive multiple by a power of two preserves exactly the
order divisors with enough 2-adic slack. -/
theorem dvd_div_pow_two_iff {d r k : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) (hk : 2 ^ k ∣ r) :
    d ∣ r / 2 ^ k ↔ padicValNat 2 d + k ≤ padicValNat 2 r := by
  have hkle : k ≤ padicValNat 2 r := (padicValNat_dvd_iff_le hr).mp hk
  constructor
  · intro h
    have hquot : r / 2 ^ k ≠ 0 := by
      have : 2 ^ k ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hk
      have : 0 < r / 2 ^ k := Nat.div_pos this (by positivity)
      omega
    have hh := level_le_of_dvd hquot h
    rw [padicValNat.div_pow hk] at hh
    omega
  · intro h
    rcases hdr with ⟨a, rfl⟩
    have hd : d ≠ 0 := left_ne_zero_of_mul hr
    have ha : a ≠ 0 := right_ne_zero_of_mul hr
    rw [padicValNat.mul hd ha] at h
    have hp : 2 ^ k ∣ a := (padicValNat_dvd_iff_le ha).mpr (by omega)
    apply (Nat.dvd_div_iff_mul_dvd hk).mpr
    simpa only [Nat.mul_comm (2 ^ k) d] using Nat.mul_dvd_mul_left d hp

/-- For a divisor, an exact valuation cutoff is a single ordinary divisibility
test; hence its size is a cyclic-group root count, not residue enumeration. -/
theorem level_le_iff_dvd_cutoff {d r t : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) :
    padicValNat 2 d ≤ t ↔ d ∣ r / 2 ^ (padicValNat 2 r - t) := by
  have hle := level_le_of_dvd hr hdr
  have hp : 2 ^ (padicValNat 2 r - t) ∣ r :=
    (padicValNat_dvd_iff_le hr).mpr (Nat.sub_le _ _)
  rw [dvd_div_pow_two_iff hr hdr hp]
  omega

/-- The cumulative law of levels in every finite cyclic group. -/
theorem cumulativeLevelCount_eq (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    cumulativeLevelCount G t = Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - t) := by
  classical
  let r := Fintype.card G
  have hr : r ≠ 0 := Fintype.card_ne_zero
  let e := r / 2 ^ (padicValNat 2 r - t)
  have hediv : e ∣ r := Nat.div_dvd_of_dvd
    ((padicValNat_dvd_iff_le hr).mpr (Nat.sub_le _ _))
  have heq : ∀ x : G, padicValNat 2 (orderOf x) ≤ t ↔ x ∈ (powMonoidHom e : G →* G).ker := by
    intro x
    rw [level_le_iff_dvd_cutoff hr (show orderOf x ∣ r from orderOf_dvd_card)]
    exact orderOf_dvd_iff_pow_eq_one
  let E : {x : G // padicValNat 2 (orderOf x) ≤ t} ≃ (powMonoidHom e : G →* G).ker :=
    Equiv.subtypeEquivRight heq
  change Fintype.card _ = e
  rw [Fintype.card_congr E, ← Nat.card_eq_fintype_card, IsCyclic.card_powMonoidHom_ker]
  rw [Nat.card_eq_fintype_card]
  exact Nat.gcd_eq_right hediv

/-- Fibers are obtained by differencing two consecutive cumulative counts. -/
theorem levelCount_eq_cumulative (G : Type*) [Group G] [Fintype G] (t : ℕ) :
    levelCount G t = if t = 0 then cumulativeLevelCount G 0
      else cumulativeLevelCount G t - cumulativeLevelCount G (t - 1) := by
  classical
  by_cases ht : t = 0
  · subst t
    simp [levelCount, cumulativeLevelCount]
  · have hpartition : (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t)) =
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) = t)) ∪
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t - 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdis : Disjoint (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) = t))
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t - 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      omega
    simp only [levelCount, cumulativeLevelCount, ht, ↓reduceIte, Fintype.card_subtype]
    rw [hpartition, Finset.card_union_of_disjoint hdis]
    omega

/-- Exact level counts use only cardinal arithmetic, powers of two and division. -/
theorem levelCount_cyclic (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    levelCount G t = if t = 0 then
      Fintype.card G / 2 ^ padicValNat 2 (Fintype.card G)
    else Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - t) -
      Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - (t - 1)) := by
  rw [levelCount_eq_cumulative]
  simp only [cumulativeLevelCount_eq, Nat.sub_zero]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LevelBounds
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


namespace ExactQuantumFactoring

lemma div_lower_power_two {r v t : ℕ} (hdiv : 2^v ∣ r) (ht : t ≤ v) :
    r / 2^(v-t) = 2^t * (r / 2^v) := by
  have hpow : 2^(v-t) * 2^t = 2^v := by rw [← pow_add, Nat.sub_add_cancel ht]
  calc
    r / 2^(v-t) = (2^(v-t) * (2^t * (r / 2^v))) / 2^(v-t) := by
      rw [← mul_assoc, hpow, Nat.mul_div_cancel' hdiv]
    _ = 2^t * (r / 2^v) := Nat.mul_div_right _ (by positivity)

/-- The traditional cyclic-group level law u, u, 2u, 4u, ... . -/
theorem levelCount_closed (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    levelCount G t = if t = 0 then Fintype.card G / 2^padicValNat 2 (Fintype.card G)
      else if t ≤ padicValNat 2 (Fintype.card G) then
        2^(t-1) * (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) else 0 := by
  have hr : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hd : 2^padicValNat 2 (Fintype.card G) ∣ Fintype.card G :=
    (padicValNat_dvd_iff_le hr).mpr le_rfl
  rw [levelCount_cyclic]
  by_cases ht : t = 0
  · simp [ht]
  · simp only [ht, ↓reduceIte]
    by_cases htv : t ≤ padicValNat 2 (Fintype.card G)
    · rw [ite_eq_left htv, div_lower_power_two hd htv,
        div_lower_power_two hd (by omega : t-1 ≤ padicValNat 2 (Fintype.card G))]
      have he : t = (t-1)+1 := by omega
      nth_rw 1 [he]
      rw [pow_succ]
      have heq : 2 ^ (t-1) * 2 * (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) =
          2 * (2^(t-1) * (Fintype.card G / 2^padicValNat 2 (Fintype.card G))) := by ring
      rw [heq]
      omega
    · have hv : padicValNat 2 (Fintype.card G) ≤ t-1 := by omega
      simp [htv, Nat.sub_eq_zero_of_le hv, Nat.sub_eq_zero_of_le (by omega :
        padicValNat 2 (Fintype.card G) ≤ t)]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimePowerLevels
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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


namespace ExactQuantumFactoring

/-- Exact prime-power level counts from the already fully proved cyclicity of
odd prime-power unit groups in Mathlib. -/
theorem primePowerLevelCard_eq {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 0 < e) (t : ℕ) :
    primePowerLevelCard p e t = closedLevelCount (primePowerUnitCount p e) t := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsCyclic (ZMod (p^e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have hc : Fintype.card (ZMod (p^e))ˣ = primePowerUnitCount p e := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp he]
    simp [primePowerUnitCount, mul_comm]
  classical
  change Nat.card {x : (ZMod (p^e))ˣ // padicValNat 2 (orderOf x) = t} = _
  rw [Nat.card_eq_fintype_card]
  change levelCount (ZMod (p^e))ˣ t = _
  rw [levelCount_closed, hc]
  rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CRTLevels
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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

lemma componentLevel_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (t : Fin (n+1)) :
    Fintype.card {a : ComponentUnits m p // componentLevel hm hmn p a = t} =
      primePowerLevelCard p.val (m.factorization p.val) t.val := by
  classical
  rw [primePowerLevelCard, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun a => Fin.ext_iff)

lemma equal_component_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) :
    Fintype.card {a : ∀ p : Component m, ComponentUnits m p //
      ∀ p, componentLevel hm hmn p (a p) = componentLevel hm hmn p₀ (a p₀)} =
    ∑ t : Fin (n+1), ∏ p : Component m,
      closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val := by
  classical
  rw [allEqualLevel_card p₀]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.prod_congr rfl
  intro p hp
  rw [componentLevel_card]
  have pp := Nat.mem_primeFactors.mp p.property
  exact primePowerLevelCard_eq pp.1 (by
    intro h
    apply (Nat.not_even_iff_odd.mpr hodd)
    exact even_iff_two_dvd.mpr (h ▸ pp.2.1))
    (pp.1.factorization_pos_of_dvd hm pp.2.1) _

end ExactQuantumFactoring


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

lemma canonicalUnit_component {m : ℕ} (hm : m≠0) (p₀ p : Component m) :
    unitCRT m hm (canonicalUnit hm p₀) p=if p=p₀ then 1 else -1 := by
  rw [canonicalUnit,MulEquiv.apply_symm_apply]

end ExactQuantumFactoring


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
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimeComponentCircuit
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
open BooleanNetwork

lemma prime_component_gcd {m p n : ℕ} (hm : m≠0) (hp : p.Prime) (hb : m≤2^n) :
    Nat.gcd m (p^n)=p^(m.factorization p) := by
  have he : m.factorization p≤n :=
    Nat.factorization_le_of_le_pow (hb.trans (Nat.pow_le_pow_left hp.two_le n))
  apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left hm) (pow_ne_zero _ hp.ne_zero)
  intro q
  rw [Nat.factorization_gcd hm (pow_ne_zero _ hp.ne_zero),hp.factorization_pow,
    hp.factorization_pow,Finsupp.inf_apply]
  by_cases h : q=p
  · subst q
    simp only [Finsupp.single_eq_same]
    exact min_eq_left he
  · simp only [Finsupp.single_eq_of_ne h,Nat.min_zero]

namespace BitArithmetic

lemma primeComponent_value {k n : ℕ} (m p : BooleanNetwork k n) (x : Basis k)
    (hm : (bitsValue (m.eval x)).toNat≠0) (hp : ((bitsValue (p.eval x)).toNat).Prime) :
    (bitsValue ((primeComponent m p).eval x)).toNat=
      (bitsValue (p.eval x)).toNat^((bitsValue (m.eval x)).toNat.factorization
        (bitsValue (p.eval x)).toNat) := by
  have hn : n ≤ componentWidth n := by dsimp only [componentWidth] <;> nlinarith
  have hpB : (bitsValue (p.eval x)).toNat^n<2^(componentWidth n) := by
    have h₁ := Nat.pow_le_pow_left (bitsValue (p.eval x)).isLt.le n
    rw [←pow_mul] at h₁
    exact h₁.trans_lt (by rw [componentWidth,pow_succ];have := Nat.two_pow_pos (n*n);omega)
  have hh : (bitsValue ((productNet (List.replicate n
      (p.comp (resizeWord n (componentWidth n))))).eval x)).toNat=(bitsValue (p.eval x)).toNat^n := by
    rw [productNet_nat,List.map_replicate,List.prod_replicate,eval_comp,resizeWord_toNat hn,
      Nat.mod_eq_of_lt hpB]
  rw [primeComponent,eval_comp,resizeWord_value,BitVec.toNat_setWidth,eval_comp,
    eval_pair,gcdNet_value,eval_comp,resizeWord_toNat hn,hh]
  rw [prime_component_gcd hm hp (bitsValue (m.eval x)).isLt.le]
  exact Nat.mod_eq_of_lt ((Nat.le_of_dvd (Nat.pos_of_ne_zero hm)
    (Nat.ordProj_dvd _ _)).trans_lt (bitsValue (m.eval x)).isLt)

end BitArithmetic
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_OracleLayout
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifIntLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_inv _root_.OAI.ExactQuantumFactoring.RatExpr.eval_neg _root_.OAI.ExactQuantumFactoring.RatExpr.eval_num _root_.OAI.ExactQuantumFactoring.RatExpr.eval_over _root_.OAI.ExactQuantumFactoring.RatExpr.eval_power _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower _root_.OAI.ExactQuantumFactoring.RatExpr.eval_times
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_NaturalExpressionCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionTemplateCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ceilRatioNat _root_.OAI.ExactQuantumFactoring.IntExpr.eval_floorRatio _root_.OAI.ExactQuantumFactoring.IntExpr.eval_iteLe _root_.OAI.ExactQuantumFactoring.IntExpr.eval_ofNat _root_.OAI.ExactQuantumFactoring.IntExpr.eval_scale _root_.OAI.ExactQuantumFactoring.NatExpr.eval_max _root_.OAI.ExactQuantumFactoring.NatExpr.eval_min _root_.OAI.ExactQuantumFactoring.NatExpr.eval_pow _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ifNatLe _root_.OAI.ExactQuantumFactoring.RatExpr.eval_ofNat
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveStatistics
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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

lemma recordFavorable_factorization {m : ℕ} (hm : m≠0) (n : ℕ) :
    recordFavorable n m.factorization=favorableCount m n := by
  rw [recordFavorable,recordPhi_factorization hm,favorableCount]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact (Finset.prod_coe_sort _ _).symm

lemma dataRecord_correct {M m : ℕ} (hM : 0 < M) (hd : m∣M) :
    dataRecord (trueData M) m = m.factorization := by
  have hh := dataDivisorPrimes_correct hM hd
  rw [dataRecord,primeRecord_eq_factorization _ hh.1,hh.2]

lemma dataPhi_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) :
    dataPhi (trueData M) m=m.totient := by
  rw [dataPhi,dataRecord_correct hM hd,recordPhi_factorization hm.ne']

lemma dataFavorable_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) (n : ℕ) :
    dataFavorable (trueData M) m n=favorableCount m n := by
  rw [dataFavorable,dataRecord_correct hM hd,recordFavorable_factorization hm.ne']

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

lemma dataListSuccess_correct {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (hd : m∣M) (n K : ℕ) :
    dataListSuccess (trueData M) m n K=Completion.listSuccess m n K := by
  rw [dataListSuccess,dataFavorable_correct hM hm hd]
  rfl

lemma dataOrderSuccess_correct {M m a : ℕ} (hM : 0 < M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) (K : ℕ) :
    dataOrderSuccess (trueData M) a m K=Completion.orderSuccess (orderOf u) K := by
  rw [dataOrderSuccess,dataOrder_correct hM hm hd u ha]

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

end TransitionWords

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveResidues
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

lemma recordFirst_factorization {m : ℕ} (hm : 2 ≤ m) :
    recordFirst m.factorization=m.minFac := by
  have hp : m.minFac∈m.factorization.support :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd m,by omega⟩
  rw [recordFirst,dite_eq_left ⟨_,hp⟩]
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨hp,?_⟩
  intro p h
  obtain ⟨hprime,hd,_⟩ := Nat.mem_primeFactors.mp h
  exact Nat.minFac_le_of_dvd hprime.two_le hd

lemma component_two_le {m : ℕ} (p : Component m) : 2 ≤ p.val^m.factorization p.val := by
  have hp := Nat.mem_primeFactors.mp p.property
  exact hp.1.two_le.trans (Nat.le_pow (hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1))

lemma equivPi_natCast {m : ℕ} (hm : m≠0) (p : Component m) (a : ℕ) :
    ZMod.equivPi m hm (a : ZMod m) p=(a : ZMod (p.val^m.factorization p.val)) := by
  exact map_natCast ((Pi.evalRingHom _ p).comp (ZMod.equivPi m hm).toRingHom) a

lemma unitCRT_natCast {m : ℕ} (hm : m≠0) (p : Component m) (u : (ZMod m)ˣ) (a : ℕ)
    (ha : (a : ZMod m)=u) :
    ((unitCRT m hm u p : ComponentUnits m p) : ZMod (p.val^m.factorization p.val))=a := by
  change ZMod.equivPi m hm (u : ZMod m) p=_
  rw [←ha,equivPi_natCast]

lemma data_component_order {M m a : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=u) (p : Component m) :
    dataOrder (trueData M) a (p.val^m.factorization p.val)=
      orderOf (unitCRT m (by omega) u p) := by
  exact dataOrder_correct hM (component_two_le p) ((Nat.ordProj_dvd m p.val).trans hd)
    (unitCRT m (by omega) u p) (unitCRT_natCast (by omega) p u a ha).symm

/-- The retrospective favorable test is a scan of supplied prime-power factors
and prime-stripping computations. It agrees with the CRT event on every actual
requested cofactor, including those below a node of the auxiliary tree. -/
lemma dataResidueGood_correct {M m n a : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) (u : (ZMod m)ˣ) (ha : a=(u : ZMod m).val) :
    dataResidueGood (trueData M) a m ↔
      FavorableUnit (by omega) hb (UniversalSplit.firstComponent hm) u := by
  let : NeZero m := ⟨by omega⟩
  have haz : (a : ZMod m)=u := by rw [ha,ZMod.natCast_zmod_val]
  have hac : a.Coprime m := (ZMod.isUnit_iff_coprime a m).mp (haz ▸ u.isUnit)
  have hal : a < m := ha ▸ (u : ZMod m).val_lt
  rw [dataResidueGood,and_iff_right hal,and_iff_right hac,dataRecord_correct hM hd,
    recordFirst_factorization hm]
  apply not_congr
  constructor
  · intro h p
    apply Fin.ext
    change padicValNat 2 (orderOf (unitCRT m _ u p))=_
    have he := h p.val p.property
    change padicValNat 2 (dataOrder (trueData M) a (p.val^m.factorization p.val))=
      padicValNat 2 (dataOrder (trueData M) a
        ((UniversalSplit.firstComponent hm).val^m.factorization (UniversalSplit.firstComponent hm).val)) at he
    rw [data_component_order hM hm hd u haz p,
      data_component_order hM hm hd u haz (UniversalSplit.firstComponent hm)] at he
    exact he
  · intro h p hp
    let pp : Component m := ⟨p,hp⟩
    change padicValNat 2 (dataOrder (trueData M) a (pp.val^m.factorization pp.val))=
      padicValNat 2 (dataOrder (trueData M) a
        ((UniversalSplit.firstComponent hm).val^m.factorization (UniversalSplit.firstComponent hm).val))
    rw [data_component_order hM hm hd u haz pp,
      data_component_order hM hm hd u haz (UniversalSplit.firstComponent hm)]
    exact congrArg Fin.val (h pp)

lemma canonical_component_val {m : ℕ} (hm : m≠0) (p₀ p : Component m) :
    ((unitCRT m hm (canonicalUnit hm p₀) p : ComponentUnits m p) :
      ZMod (p.val^m.factorization p.val)).val=
      if p.val=p₀.val then 1 else p.val^m.factorization p.val-1 := by
  classical
  rw [canonicalUnit_component]
  by_cases h : p=p₀
  · subst p
    simp only [ite_true, if_true,Units.val_one]
    exact ZMod.val_one'' (n:=p₀.val^m.factorization p₀.val) (by have := component_two_le p₀; omega)
  · have hn : p.val≠p₀.val := fun hh=>h (Subtype.ext hh)
    simp only [ite_eq_right h,ite_eq_right hn,Units.val_neg,Units.val_one]
    have hq := component_two_le p
    generalize p.val^m.factorization p.val=q at *
    cases q with
    | zero => omega
    | succ q => simpa only [Nat.add_sub_cancel] using ZMod.val_neg_one q

lemma dataCanonicalResidue_correct {M m : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hd : m∣M) (a : ℕ) :
    dataCanonicalResidue (trueData M) a m ↔
      a=(canonicalUnit (by omega) (UniversalSplit.firstComponent hm) : ZMod m).val := by
  let : NeZero m := ⟨by omega⟩
  let u := canonicalUnit (by omega : m≠0) (UniversalSplit.firstComponent hm)
  rw [dataCanonicalResidue,dataRecord_correct hM hd,recordFirst_factorization hm]
  constructor
  · rintro ⟨hal,h⟩
    have hz : (a : ZMod m)=u := by
      apply (ZMod.equivPi m (by omega : m≠0)).injective
      funext p
      apply ZMod.val_injective
      rw [equivPi_natCast,ZMod.val_natCast]
      change _=((unitCRT m (by omega) u p : ComponentUnits m p) :
        ZMod (p.val^m.factorization p.val)).val
      rw [canonical_component_val]
      exact h p.val p.property
    have he := congrArg (fun z : ZMod m=>z.val) hz
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hal] using he
  · intro ha
    refine ⟨ha ▸ (u : ZMod m).val_lt,?_⟩
    intro p hp
    let pp : Component m := ⟨p,hp⟩
    have haz : (a : ZMod m)=u := by rw [ha,ZMod.natCast_zmod_val]
    have he := congrArg (fun z : ZMod (p^m.factorization p)=>z.val)
      (unitCRT_natCast (by omega) pp u a haz)
    rw [ZMod.val_natCast,canonical_component_val] at he
    exact he.symm

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TraceBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.trueData_descendants
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
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.trueData_descendants
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlCircuit
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolynomialFilterExpressions
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.RatExpr.eval_signedPower
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

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetentionExpressions
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
end ExactQuantumFactoring


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

namespace OrderSlots

lemma usableOn_value {k n : ℕ} (a m : BooleanNetwork k n) (x : Basis k) (hn : 1≤n) :
    (usableOn a m).eval x 0=true ↔ Usable (a.eval x) (m.eval x) := by
  have h1 : 1<2^n := Nat.one_lt_two_pow (by omega)
  simp only [usableOn,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,equalOn_value,
    eval_comp,eval_pair,gcdNet_value,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,
    Usable,ZMod.isUnit_iff_coprime,Nat.Coprime]

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

namespace BitArithmetic
open BooleanNetwork FactorController

lemma evenOn_value {k w : ℕ} (hw : 2≤w) (m : BooleanNetwork k w) (x : Basis k) :
    (evenOn m).eval x 0=true ↔ 2∣(bitsValue (m.eval x)).toNat := by
  have h2 : 2<2^w := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  rw [evenOn,zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2,Nat.dvd_iff_mod_eq_zero]

end BitArithmetic
end ExactQuantumFactoring


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
-- module Solutions.OAIQ222_QF.QuantumFactoring_ChildQueue
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

end NodeMachine
end ExactQuantumFactoring


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
-- module Solutions.OAIQ222_QF.QuantumFactoring_VerifiedTreeCompletion
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.trueData_descendants
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

end PhysicalTree
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_TablePrimeSupport
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

lemma tableFactors_cover {n N M m : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0)
    (_hm : m≠0) (hd : m∣M) : ∀ p : ℕ,p.Prime→p∣m→p∈tableFactors rows := by
  intro p hp hpm
  have hh:=lookupPrimes_correct h hM hM0
  have hpM : p∣(lookupPrimes rows M).prod := by rw [hh.2];exact hpm.trans hd
  obtain ⟨q,hq,hpq⟩:=(Nat.prime_iff.mp hp).dvd_prod_iff.mp hpM
  have he:=((hh.1 q hq).eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one
  have hpq' : p∈lookupPrimes rows M := by simpa only [he] using hq
  exact lookupPrimes_subset_table hM0 hpq'

end PhysicalTree

lemma leastDivisorIn_iff {ps : List ℕ} {m p : ℕ} (hm : 2 ≤ m)
    (hps : ∀ q∈ps,q.Prime) (hcover : ∀ q : ℕ,q.Prime→q∣m→q∈ps)
    (hp : p∈ps) (hpd : p∣m) : leastDivisorIn ps m p ↔ p=m.minFac := by
  have hmin : m.minFac∈ps := hcover _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m)
  constructor
  · intro h
    exact le_antisymm (h _ hmin (Nat.minFac_dvd m)) (Nat.minFac_le_of_dvd (hps p hp).two_le hpd)
  · rintro rfl q hq hqd
    exact Nat.minFac_le_of_dvd (hps q hq).two_le hqd

lemma tableCanonical_correct {ps : List ℕ} {M m n : ℕ} (hM : 0 < M) (hm : 2 ≤ m)
    (hb : m ≤ 2^n) (hd : m∣M) (hps : ∀ q∈ps,q.Prime)
    (hcover : ∀ q : ℕ,q.Prime→q∣m→q∈ps) (a : ℕ) :
    tableCanonical ps a m n ↔ dataCanonicalResidue (trueData M) a m := by
  rw [tableCanonical,dataCanonicalResidue,dataRecord_correct hM hd,recordFirst_factorization hm]
  apply and_congr_right
  intro _
  constructor
  · intro h p hp
    obtain ⟨hprime,hpd,_⟩:=Nat.mem_primeFactors.mp hp
    have hmem:=hcover p hprime hpd
    have hh:=h p hmem hpd
    simpa only [prime_component_gcd (by omega) hprime hb,
      leastDivisorIn_iff hm hps hcover hmem hpd] using hh
  · intro h p hp hpd
    have hh:=h p (Nat.mem_primeFactors.mpr ⟨hps p hp,hpd,by omega⟩)
    simpa only [prime_component_gcd (by omega) (hps p hp) hb,
      leastDivisorIn_iff hm hps hcover hp hpd] using hh
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CanonicalResidueCircuit
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
attribute [local instance] Classical.propDecidable

lemma dividesOn_value {k n : ℕ} (p m : BooleanNetwork k n) (x : Basis k) :
    (dividesOn p m).eval x 0=true ↔ (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat := by
  rw [dividesOn,zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,Nat.dvd_iff_mod_eq_zero]

lemma leastDivisorTest_value {k n : ℕ} (ps : List (BooleanNetwork k n))
    (m p : BooleanNetwork k n) (x : Basis k) :
    (leastDivisorTest ps m p).eval x 0=true ↔
      leastDivisorIn (ps.map (fun q=>(bitsValue (q.eval x)).toNat))
        (bitsValue (m.eval x)).toNat (bitsValue (p.eval x)).toNat := by
  simp only [leastDivisorTest,all_eval,List.forall_mem_map,eval_bor,Bool.or_eq_true,
    bnot_value,dividesOn_value,wordLe_eval,decide_eq_true_eq,leastDivisorIn,
    List.forall_mem_map,or_iff_not_imp_left,not_not]

lemma componentCongruence_value {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m p : BooleanNetwork k n) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hp : ((bitsValue (p.eval x)).toNat).Prime) :
    (componentCongruence ps a m p).eval x 0=true ↔
      (bitsValue (a.eval x)).toNat % Nat.gcd (bitsValue (m.eval x)).toNat
        ((bitsValue (p.eval x)).toNat^n)=
      if leastDivisorIn (ps.map (fun q=>(bitsValue (q.eval x)).toNat))
        (bitsValue (m.eval x)).toNat (bitsValue (p.eval x)).toNat
      then 1 else Nat.gcd (bitsValue (m.eval x)).toNat ((bitsValue (p.eval x)).toNat^n)-1 := by
  have h1 : 1<2^n := by have hh:=(bitsValue (m.eval x)).isLt;omega
  have hq : (bitsValue ((primeComponent m p).eval x)).toNat=
      Nat.gcd (bitsValue (m.eval x)).toNat ((bitsValue (p.eval x)).toNat^n) := by
    rw [primeComponent_value m p x (by omega) hp,
      prime_component_gcd (by omega) hp (bitsValue (m.eval x)).isLt.le]
  rw [componentCongruence,equalOn_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,hq,wordMux_eval]
  by_cases ht : (leastDivisorTest ps m p).eval x 0=true
  · rw [ite_eq_left ht,ite_eq_left ((leastDivisorTest_value ps m p x).mp ht),wordConstant_eval,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  · rw [ite_eq_right ht,ite_eq_right (fun h=>ht ((leastDivisorTest_value ps m p x).mpr h)),natSubOn_value,
      hq,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]

lemma tableCanonicalNet_value {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m : BooleanNetwork k n) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat)
    (hps : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime) :
    (tableCanonicalNet ps a m).eval x 0=true ↔
      tableCanonical (ps.map (fun p=>(bitsValue (p.eval x)).toNat))
        (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat n := by
  rw [tableCanonicalNet,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,tableCanonical]
  apply and_congr_right
  intro _
  simp only [all_eval,List.forall_mem_map,eval_bor,Bool.or_eq_true,bnot_value,dividesOn_value]
  constructor
  · intro h p hp hpd
    exact (componentCongruence_value ps a m p x hm (hps p hp)).mp ((h p hp).resolve_left (not_not.mpr hpd))
  · intro h p hp
    by_cases hpd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat
    · exact Or.inr ((componentCongruence_value ps a m p x hm (hps p hp)).mpr
        (h p hp hpd))
    · exact Or.inl hpd
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TwoAdicCircuit
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
open BooleanNetwork

lemma twoadic_lt_width {d n : ℕ} (hd : d≠0) (hb : d<2^n) : padicValNat 2 d<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hd)
    ((padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) hd).mpr le_rfl)).trans_lt hb

lemma twoadic_eq_iff {a b n : ℕ} (ha : a≠0) (hb : b≠0) (haB : a<2^n) (hbB : b<2^n) :
    padicValNat 2 a=padicValNat 2 b ↔ ∀ i : Fin n,2^i.val∣a ↔ 2^i.val∣b := by
  simp only [padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) ha,
    padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) hb]
  constructor
  · intro he i; rw [he]
  · intro h
    exact le_antisymm ((h ⟨_,twoadic_lt_width ha haB⟩).mp le_rfl)
      ((h ⟨_,twoadic_lt_width hb hbB⟩).mpr le_rfl)

namespace BitArithmetic

lemma bequiv_value {k : ℕ} (a b : BooleanNetwork k 1) (x : Basis k) :
    (bequiv a b).eval x 0=true ↔ (a.eval x 0=true ↔ b.eval x 0=true) := by
  rw [bequiv,bnot_value,eval_bxor]
  cases a.eval x 0 <;> cases b.eval x 0 <;> decide

lemma sameTwoVal_value {k n : ℕ} (a b : BooleanNetwork k n) (x : Basis k)
    (ha : (bitsValue (a.eval x)).toNat≠0) (hb : (bitsValue (b.eval x)).toNat≠0) :
    (sameTwoVal a b).eval x 0=true ↔
      padicValNat 2 (bitsValue (a.eval x)).toNat=padicValNat 2 (bitsValue (b.eval x)).toNat := by
  rw [twoadic_eq_iff ha hb (bitsValue (a.eval x)).isLt (bitsValue (b.eval x)).isLt]
  simp only [sameTwoVal,all_eval,List.forall_mem_ofFn_iff,bequiv_value,eval_comp,
    dividesNet_value _ _ _ (Nat.pow_lt_pow_right (by decide : 1<2) (Fin.isLt _))]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ClosedLevelCircuit
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
open BooleanNetwork
namespace BitArithmetic

lemma oddPartNet_value {k n : ℕ} (hn : 2 ≤ n) (a : BooleanNetwork k n)
    (x : Basis k) (ha : (bitsValue (a.eval x)).toNat≠0) :
    (bitsValue ((oddPartNet a).eval x)).toNat=
      (bitsValue (a.eval x)).toNat/2^padicValNat 2 (bitsValue (a.eval x)).toNat := by
  have h2 : 2<2^n := lt_of_lt_of_le (by decide : 2<2^2)
    (Nat.pow_le_pow_right (by decide : 0<2) hn)
  have hc : (bitsValue ((wordConstant (n:=k) (BitVec.ofNat n 2)).eval x)).toNat=2 := by
    rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2]
  have hh:=primeComponent_value a (wordConstant (BitVec.ofNat n 2)) x ha
    (by rw [hc];exact Nat.prime_two)
  rw [hc,Nat.factorization_def _ Nat.prime_two] at hh
  rw [oddPartNet,eval_comp,eval_pair,div_word,BitVec.toNat_udiv,hh]

lemma closedLevelNet_value {k n : ℕ} (hn : 2≤n) (a : BooleanNetwork k n)
    (x : Basis k) (ha : (bitsValue (a.eval x)).toNat≠0) (t : ℕ) :
    (bitsValue ((closedLevelNet a t).eval x)).toNat=
      closedLevelCount (bitsValue (a.eval x)).toNat t := by
  have hodd:=oddPartNet_value hn a x ha
  have hv:=twoadic_lt_width ha (bitsValue (a.eval x)).isLt
  rw [closedLevelNet,closedLevelCount]
  by_cases ht : t=0
  · rw [ite_eq_left ht,ite_eq_left ht,hodd]
  · rw [ite_eq_right ht,ite_eq_right ht]
    by_cases htn : t<n
    · rw [ite_eq_left htn,wordMux_eval]
      have hd : (a.comp (dividesNet n (2^t))).eval x 0=true ↔
          t≤padicValNat 2 (bitsValue (a.eval x)).toNat := by
        rw [eval_comp,dividesNet_value _ _ _ (Nat.pow_lt_pow_right (by decide : 1<2) htn),
          padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) ha]
      by_cases he : t≤padicValNat 2 (bitsValue (a.eval x)).toNat
      · rw [ite_eq_left (hd.mpr he),ite_eq_left he,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,hodd,
          wordConstant_eval,BitVec.toNat_ofNat]
        have hc : 2^(t-1)<2^n:=Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
        rw [Nat.mod_eq_of_lt hc]
        have hdvd : 2^padicValNat 2 (bitsValue (a.eval x)).toNat∣(bitsValue (a.eval x)).toNat :=
          (padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) ha).mpr le_rfl
        have hp : 2^(t-1)≤2^padicValNat 2 (bitsValue (a.eval x)).toNat :=
          Nat.pow_le_pow_right (by decide : 0<2) (by omega)
        have hb := Nat.mul_le_mul_left ((bitsValue (a.eval x)).toNat/
          2^padicValNat 2 (bitsValue (a.eval x)).toNat) hp
        rw [Nat.div_mul_cancel hdvd] at hb
        rw [Nat.mod_eq_of_lt (hb.trans_lt (bitsValue (a.eval x)).isLt),Nat.mul_comm]
      · rw [ite_eq_right (fun h=>he (hd.mp h)),ite_eq_right he,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod]
    · rw [ite_eq_right htn,ite_eq_right (by omega),wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod]

end BitArithmetic
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

lemma dataResidueGood_exists {M m n a : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) : dataResidueGood (trueData M) a m ↔
      ∃ u : (ZMod m)ˣ,a=(u : ZMod m).val ∧
        FavorableUnit (by omega) hb (UniversalSplit.firstComponent hm) u := by
  let : NeZero m := ⟨by omega⟩
  constructor
  · intro h
    have hu : IsUnit (a : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr h.2.1
    have hv : a=(hu.unit : ZMod m).val := by
      rw [hu.unit_spec,ZMod.val_natCast,Nat.mod_eq_of_lt h.1]
    exact ⟨hu.unit,hv,(dataResidueGood_correct hM hm hb hd hu.unit hv).mp h⟩
  · rintro ⟨u,ha,h⟩
    exact (dataResidueGood_correct hM hm hb hd u ha).mpr h

lemma dataGoodList_correct {M m n : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) (y : Basis (Completion.transitionWidth n)) :
    dataGoodList (trueData M) m n y ↔
      ListSlots.GoodOutput (by omega) hb (UniversalSplit.firstComponent hm) y := by
  unfold dataGoodList ListSlots.GoodOutput
  apply exists_congr
  intro i
  exact dataResidueGood_exists hM hm hb hd

/-- The source canonical list has the CRT unit in the first field and zero in
all remaining fields (including the final unused word). -/
lemma canonical_list_words {m n : ℕ} (hm : m≠0) (hb : m < 2^n) (p₀ : Component m) :
    ListSlots.canonical hm hb p₀=TransitionWords.encode
      (fun i : Fin (n^5) => natBasis n (if i.val=0 then (canonicalUnit hm p₀ : ZMod m).val else 0)) := by
  let : NeZero m := ⟨hm⟩
  unfold ListSlots.canonical ListSlots.ordinary
  congr 1
  funext i
  apply (bitsEquiv n).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue (padBits _ (canonicalList hm p₀ (n^5) i))).toNat=_
  rw [padBits_value]
  simp only [canonicalList,bitsEquiv,Equiv.coe_fn_symm_mk,bitsValue_bits,BitVec.toNat_ofNat,
    ]
  have hv : (if i.val=0 then (canonicalUnit hm p₀ : ZMod m).val else 0) < m := by
    split_ifs
    · exact ZMod.val_lt _
    · omega
  change _=(bitsValue (natBasis n _)).toNat
  rw [natBasis_value,Nat.mod_eq_of_lt (hv.trans_le (Nat.le_pow_clog (by decide) m)),Nat.mod_eq_of_lt (hv.trans hb)]

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

lemma dataCanonicalList_correct {M m n : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) (hn : 0<n) (y : Basis (Completion.transitionWidth n)) :
    dataCanonicalList (trueData M) m n hn y ↔
      y=ListSlots.canonical (by omega) hb (UniversalSplit.firstComponent hm) := by
  let : NeZero m := ⟨by omega⟩
  let u := canonicalUnit (by omega : m≠0) (UniversalSplit.firstComponent hm)
  have hu : (u : ZMod m).val<2^n := (ZMod.val_lt _).trans hb
  rw [dataCanonicalList,dataCanonicalResidue_correct hM hm hd,basis_eq_natBasis hu,
    canonical_list_words]
  have hshape : (fun i : Fin (n^5) => natBasis n (if i.val=0 then (u : ZMod m).val else 0))=
      (fun i : Fin (n^5) => if i.val=0 then natBasis n (u : ZMod m).val else natBasis n 0) := by
    funext i
    split_ifs <;> rfl
  change (_=natBasis n (u : ZMod m).val ∧ _) ↔ y=TransitionWords.encode _
  rw [hshape]
  constructor
  · rintro ⟨ha,hy⟩
    simpa only [ha] using hy
  · intro hy
    rw [hy,TransitionWords.read_encode]
    simp only [ite_true, if_true,eq_self]
    exact ⟨trivial,rfl⟩

namespace Completion
lemma test_eq_passed {α : Type*} {W t d : ℕ} (good : α→Prop) (guessGood : Basis W→Prop)
    (y₀ : Basis W) (s z : ℚ) (hg : ∀ y,guessGood y ↔ y=y₀) (r : Raw α W t d) :
    test good guessGood s z r ↔ passed good y₀ s z r := by
  simp only [test,passed,guessPass,hg]
end Completion

/-- Same integer, same raw outcome, same retention coin. A verified occurrence
record suffices even when the request is only a divisor of that occurrence. -/
lemma dataListPassed_correct {M n : ℕ} (hM : 0<M) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat∣M) (hn : 0<n)
    (r : PhysicalListSlots.Result n) :
    dataListPassed (trueData M) m hn r ↔
      PhysicalListSlots.passed m (by omega) (UniversalSplit.firstComponent hm) r := by
  have hg : (fun x => dataGoodList (trueData M) (bitsValue m).toNat n (PhysicalListSlots.ordinary x))=
      (ListSlots.GoodOutput (by omega) (bitsValue m).isLt (UniversalSplit.firstComponent hm) ∘
        PhysicalListSlots.ordinary) := by
    funext x
    exact propext (dataGoodList_correct hM hm (bitsValue m).isLt hd _)
  rw [dataListPassed,hg,dataListSuccess_correct hM (by omega) hd]
  exact Completion.test_eq_passed _ _ _ _ _
    (dataCanonicalList_correct hM hm (bitsValue m).isLt hd hn) r

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_ComponentPhiCircuit
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

lemma componentPhiNet_value {k n : ℕ} (m p : BooleanNetwork k n) (x : Basis k)
    (hm : (bitsValue (m.eval x)).toNat≠0) (hp : ((bitsValue (p.eval x)).toNat).Prime)
    (hd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat) :
    (bitsValue ((componentPhiNet m p).eval x)).toNat=
      primePowerUnitCount (bitsValue (p.eval x)).toNat
        ((bitsValue (m.eval x)).toNat.factorization (bitsValue (p.eval x)).toNat) := by
  have hq:=primeComponent_value m p x hm hp
  have he:=hp.factorization_pos_of_dvd hm hd
  rw [componentPhiNet,natSubOn_value,eval_comp,eval_pair,div_word,BitVec.toNat_udiv,hq]
  obtain ⟨e,he'⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  rw [he',primePowerUnitCount,Nat.succ_sub_one,pow_succ,Nat.mul_div_cancel _ hp.pos]
  simpa only [Nat.mul_one,Nat.one_mul,Nat.mul_comm] using
    (Nat.mul_sub_left_distrib ((bitsValue (p.eval x)).toNat^e) (bitsValue (p.eval x)).toNat 1).symm

lemma componentPhiNet_ne_zero {k n : ℕ} (m p : BooleanNetwork k n) (x : Basis k)
    (hm : (bitsValue (m.eval x)).toNat≠0) (hp : ((bitsValue (p.eval x)).toNat).Prime)
    (hd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat) :
    (bitsValue ((componentPhiNet m p).eval x)).toNat≠0 := by
  rw [componentPhiNet_value m p x hm hp hd,primePowerUnitCount]
  exact Nat.ne_of_gt (Nat.mul_pos (by have := hp.two_le;omega) (Nat.pow_pos hp.pos))

lemma componentLevelNet_value {k n : ℕ} (hn : 2≤n) (m p : BooleanNetwork k n)
    (x : Basis k) (hm : (bitsValue (m.eval x)).toNat≠0)
    (hp : ((bitsValue (p.eval x)).toNat).Prime) (t : ℕ) :
    (bitsValue ((componentLevelNet m p t).eval x)).toNat=
      if (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat then
        closedLevelCount (primePowerUnitCount (bitsValue (p.eval x)).toNat
          ((bitsValue (m.eval x)).toNat.factorization (bitsValue (p.eval x)).toNat)) t
      else 1 := by
  rw [componentLevelNet,wordMux_eval]
  by_cases hd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat
  · rw [ite_eq_left ((dividesOn_value p m x).mpr hd),ite_eq_left hd,
      closedLevelNet_value hn _ x (componentPhiNet_ne_zero m p x hm hp hd),
      componentPhiNet_value m p x hm hp hd]
  · rw [ite_eq_right (fun h=>hd ((dividesOn_value p m x).mp h)),ite_eq_right hd,
      wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) (by decide))]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DistinctProductCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open scoped BigOperators
namespace BitArithmetic

lemma occursLater_value {k n : ℕ} (p : BooleanNetwork k n) (ps : List (BooleanNetwork k n))
    (x : Basis k) : (occursLater p ps).eval x 0=true ↔
      (bitsValue (p.eval x)).toNat∈ps.map (fun q=>(bitsValue (q.eval x)).toNat) := by
  simp only [occursLater,any_eval,List.mem_map,exists_exists_and_eq_and,
    eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  constructor
  · rintro ⟨q,hq,he⟩
    exact ⟨q,hq,(congrArg BitVec.toNat he).symm⟩
  · rintro ⟨q,hq,he⟩
    exact ⟨q,hq,BitVec.eq_of_toNat_eq he.symm⟩

lemma distinctProductNet_value {k n : ℕ} (value : BooleanNetwork k n→BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (f : ℕ→ℕ)
    (hv : ∀ p∈ps,(bitsValue ((value p).eval x)).toNat=f (bitsValue (p.eval x)).toNat%2^n) :
    (bitsValue ((distinctProductNet value ps).eval x)).toNat=
      (∏ p∈(ps.map (fun q=>(bitsValue (q.eval x)).toNat)).toFinset,f p)%2^n := by
  induction ps with
  | nil=>simp [distinctProductNet,wordConstant_eval]
  | cons p ps ih=>
    have hp:=hv p (by simp)
    have hi:=ih (fun q hq=>hv q (by simp [hq]))
    rw [distinctProductNet,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,
      wordMux_eval,hi,List.map_cons,List.toFinset_cons]
    by_cases he : (bitsValue (p.eval x)).toNat∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)
    · rw [ite_eq_left ((occursLater_value p ps x).mpr he),wordConstant_eval,
        Finset.insert_eq_of_mem (List.mem_toFinset.mpr he),show (1 : BitVec n).toNat=1%2^n from rfl,Nat.mod_mul_mod,Nat.mul_mod_mod,one_mul]
    · rw [ite_eq_right (fun h=>he ((occursLater_value p ps x).mp h)),hp,
        Finset.prod_insert (by simpa only [List.mem_toFinset] using he),Nat.mod_mul_mod,Nat.mul_mod_mod]

end BitArithmetic
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_HardFilterCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
namespace UniversalSplit

lemma hardOn_value {k n : ℕ} (hn : 128≤n) (m : BooleanNetwork k n) (x : Basis k) :
    (hardOn m).eval x 0=true ↔ Hard (bitsValue (m.eval x)).toNat := by
  have hf : 2<2^n := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) (by omega : 2≤n))
  have hp : (((m.comp (resizeWord n (rootWidth n))).comp (perfectPowerNet n)).eval x 0=true) ↔
      Primality.PerfectPower (bitsValue (m.eval x)).toNat := by
    rw [eval_comp,perfectPowerNet_correct (by omega)]
    · rw [eval_comp,resizeWord_toNat (rootWidth_ge n)]
    · rw [eval_comp,resizeWord_toNat (rootWidth_ge n)]
      exact (bitsValue (m.eval x)).isLt
  rw [hardOn,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    wordLe_eval,decide_eq_true_eq,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hf,
    bnot_value,eval_comp,primeWord_value hn,eval_band,Bool.and_eq_true,bnot_value,
    evenOn_value (by omega),bnot_value,hp]
  rw [←even_iff_two_dvd,Nat.not_even_iff_odd]
  exact and_assoc
end UniversalSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeStateFailure
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
namespace NodeStateCircuit

/-- Failed candidates leave genuine pending factors unchanged and only set the
sticky verifier bit. They cannot introduce an unrelated query into the log. -/
lemma step_failure {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w)
    (xs ys : List (Basis w)) (b : Bool) (hx : xs.length ≤ s)
    (ha : 2 ≤ (bitsValue a).toNat) (hp : ¬(bitsValue a).toNat.Prime)
    (hd : ¬ProperDivisor (bitsValue a).toNat (bitsValue d).toNat) :
    (step s w).eval (Fin.append (pack (a::xs) ys b) d)=pack (a::xs) ys true := by
  have he : (emission s w).eval (Fin.append (pack (a::xs) ys b) d)=(fun _=>false) := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_pack_cons hw,ite_eq_right hp]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack (a::xs) ys b) d) 0=true := by
    rw [zeroWord_value,he,zeroBasis_value]
    rfl
  have hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack (a::xs) d) 0=true :=
    (NodeCircuit.failed_pack_cons hw a d xs ha).mpr ⟨hp,hd⟩
  have hb : (nextBad s w).eval (Fin.append (pack (a::xs) ys b) d)=(fun _=>true) := by
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rw [nextBad,eval_bor,eval_comp,old_append,bad_pack,eval_comp,nodeInput_pack,hf,Bool.or_true]
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_pack_cons hw _ _ _ hx ha,ite_eq_right hp,ite_eq_right hd,nextOutput,wordMux_eval,
    ite_eq_left hz,eval_comp,old_append,output_pack,hb]
  rfl
end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalNodeSafety
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
open BooleanNetwork BitArithmetic FactorController AuxiliaryTree OrderTrial
namespace PhysicalNode

lemma next_safe {n N s : ℕ} (hn : 128  ≤  n) (xs ys : List (Basis (n+1)))
    (b : Bool) (h : Good n N s xs ys) (r : FixedSplit.Raw n) :
    ∃ xs' ys' b', (machine n s).next (NodeStateCircuit.pack xs ys b) r=
      NodeStateCircuit.pack xs' ys' b' ∧ Good n N s xs' ys' := by
  cases xs with
  | nil=>exact ⟨[],ys,b,next_nil hn ys b r,h⟩
  | cons a xs=>
    have ha:=h.bounded a (by simp)
    have ht : ∀ x∈xs,2 ≤ (bitsValue x).toNat ∧ (bitsValue x).toNat < 2^n :=
      fun x hx=>h.bounded x (List.mem_cons_of_mem _ hx)
    have hcap : xs.length ≤ s := by have hh:=h.length_le; simp only [List.length_cons] at hh;omega
    by_cases hp : (bitsValue a).toNat.Prime
    · refine ⟨xs,a::ys,b,next_prime hn a xs ys b hcap hp r,⟨ht,?_,?_,?_⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hp
        · exact h.primes z hz
      · have hh:=h.product
        simp only [values_cons,List.prod_cons] at hh ⊢
        calc
          (values xs).prod*((bitsValue a).toNat*(values ys).prod)=
            ((bitsValue a).toNat*(values xs).prod)*(values ys).prod := by ac_rfl
          _=N := hh
      · have hw:=h.clock
        rw [values_cons,weight_prime _ _ hp] at hw
        omega
    · let q:=(query n s).eval (NodeStateCircuit.pack (a::xs) ys b)
      let d:=decoded q r
      by_cases hd : ProperDivisor (bitsValue a).toNat (bitsValue d).toNat
      · let z:=(NodeCircuit.quotient s (n+1)).eval (NodeCircuit.pack (a::xs) d)
        have hz : (bitsValue z).toNat=(bitsValue a).toNat/(bitsValue d).toNat :=
          NodeCircuit.quotient_pack a d xs
        have hquot:=hd.quotient
        refine ⟨d::z::xs,ys,b,?_,⟨?_,h.primes,?_,?_⟩⟩
        · rw [next_eq]
          exact NodeStateCircuit.step_split (by omega) _ _ _ _ _ hcap ha.1 hp hd
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact ⟨by have hh:=hd.1;omega,hd.2.1.trans ha.2⟩
          · rcases List.mem_cons.mp hv with rfl | hv
            · rw [hz]
              exact ⟨hquot.1,hquot.2.1.trans ha.2⟩
            · exact ht v hv
        · have hh:=h.product
          simp only [values_cons,List.prod_cons] at hh ⊢
          rw [hz,←Nat.mul_assoc,hd.quotient.2.2]
          exact hh
        · have hw:=h.clock
          rw [values_cons,weight_split hd] at hw
          simpa only [values_cons,hz] using
            (show weight ((bitsValue d).toNat::(bitsValue a).toNat/(bitsValue d).toNat::values xs) ≤ s by omega)
      · refine ⟨a::xs,ys,true,?_,h⟩
        rw [next_eq]
        exact NodeStateCircuit.step_failure (by omega) a d xs ys b hcap ha.1 hp hd

/-- Safety is unconditional on every raw quantum outcome. In particular even a
failed retained candidate only stalls; all subsequent nonzero queries divide
this node's original modulus. -/
theorem config_safe {n N : ℕ} (hn : 128  ≤  n) (hN : 2  ≤  N) (hb : N < 2^n)
    (t : ℕ) (h : SplitMachine.Trace n t) :
    ∃ xs ys b, (machine n (2*n)).config
        (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h=NodeStateCircuit.pack xs ys b ∧
      Good n N (2*n) xs ys := by
  induction t with
  | zero=>
    have hbw : N < 2^(n+1) := hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have ha : (bitsValue (natBasis (n+1) N)).toNat=N := by
      rw [natBasis_value,Nat.mod_eq_of_lt hbw]
    refine ⟨[natBasis (n+1) N],[],false,rfl,⟨?_,?_,?_,?_⟩⟩
    · intro a ha'
      have he : a=natBasis (n+1) N := List.mem_singleton.mp ha'
      subst a
      rw [ha]
      exact ⟨hN,hb⟩
    · simp
    · simp only [values_cons,values_nil,List.prod_cons,List.prod_nil,ha,mul_one]
    · have hs:=splitWeight_bound (by omega : 0 < N) hb
      simp only [values_cons,values_nil,ha,weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega
  | succ t ih=>
    obtain ⟨xs,ys,b,he,hg⟩:=ih h.1
    obtain ⟨xs',ys',b',he',hg'⟩:=next_safe hn xs ys b hg h.2
    refine ⟨xs',ys',b',?_,hg'⟩
    change (machine n (2*n)).next ((machine n (2*n)).config _ t h.1) h.2=_
    rw [he,he']

lemma Good.pending_dvd {n N s : ℕ} {xs ys : List (Basis (n+1))}
    (h : Good n N s xs ys) (a : Basis (n+1)) (ha : a∈xs) : (bitsValue a).toNat ∣ N := by
  rw [←h.product]
  exact (List.dvd_prod (List.mem_map.mpr ⟨a,ha,rfl⟩)).trans (dvd_mul_right _ _)

theorem query_safe {n N : ℕ} (hn : 128  ≤  n) (hN : 2  ≤  N) (hb : N < 2^n)
    (t : ℕ) (h : SplitMachine.Trace n t) :
    let m:=(bitsValue ((query n (2*n)).eval ((machine n (2*n)).config
      (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h))).toNat
    m=0 ∨ (2 ≤ m ∧ m < 2^n ∧ m ∣ N) := by
  obtain ⟨xs,ys,b,he,hg⟩:=config_safe hn hN hb t h
  dsimp only
  rw [he]
  cases xs with
  | nil=>
    left
    rw [query,eval_comp,NodeStateCircuit.top_pack]
    change (bitsValue ((resizeWord (n+1) n).eval (fun _=>false))).toNat=0
    rw [resizeWord_value,zeroBasis_value]
    simp
  | cons a xs=>
    have ha:=hg.bounded a (by simp)
    rw [query_value a xs ys b ha.2]
    exact Or.inr ⟨ha.1,ha.2,hg.pending_dvd a (by simp)⟩
end PhysicalNode
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedCanonical
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

lemma retainedCanonical_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedCanonical t a m).eval (M.encoded x t r) 0=true ↔
      dataCanonicalResidue (trueData P)
        (bitsValue (a.eval (M.encoded x t r))).toNat d := by
  have he:=tableNets_values hn (M.fieldRows t) (M.encoded x t r)
  rw [M.fieldRows_values] at he
  have hp : ∀ p∈tableNets (M.fieldRows t),
      ((bitsValue (p.eval (M.encoded x t r))).toNat).Prime := by
    intro p hp
    apply PhysicalTree.tableFactors_prime hc
    rw [←he]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  rw [retainedCanonical,tableCanonicalNet_value _ a m _ (by omega) hp,he,hm]
  exact tableCanonical_correct (by omega) hd (hm ▸ (bitsValue (m.eval (M.encoded x t r))).isLt.le)
    hdiv (PhysicalTree.tableFactors_prime hc)
    (PhysicalTree.tableFactors_cover hc hP hP0 (by omega) hdiv) _

end NodeMachine

namespace TransitionWords

lemma readNet_eval {k n K : ℕ} (y : BooleanNetwork k (n*(K+1))) (i : Fin K) (x : Basis k) :
    (readNet y i).eval x=read (y.eval x) i := rfl

lemma firstOnly_eval {k n K : ℕ} (a : BooleanNetwork k n) (x : Basis k) :
    (firstOnly (K:=K) a).eval x=encode (fun i : Fin K=>if i.val=0 then a.eval x else OrderTrial.natBasis n 0) := by
  rw [firstOnly,encodeNet_eval]
  congr 1
  funext i
  split_ifs
  · rfl
  · funext j
    simp only [wordConstant,eval_vector,eval_constant,OrderTrial.natBasis]
end TransitionWords

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma retainedCanonicalList_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (y : BooleanNetwork (M.width t) (n*(n^5+1)))
    (x : Basis c) (r : Trace n t) (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedCanonicalList (by omega) t m y).eval (M.encoded x t r) 0=true ↔
      dataCanonicalList (trueData P) d n (by omega) (y.eval (M.encoded x t r)) := by
  change (M.retainedCanonicalList _ t m y).eval (M.encoded x t r) 0=true ↔
    dataCanonicalResidue (trueData P) (bitsValue (TransitionWords.read (y.eval (M.encoded x t r))
      ⟨0,pow_pos (by omega : 0<n) 5⟩)).toNat d ∧
    y.eval (M.encoded x t r)=TransitionWords.encode (fun i : Fin (n^5)=>if i.val=0 then
      TransitionWords.read (y.eval (M.encoded x t r)) ⟨0,pow_pos (by omega : 0<n) 5⟩ else OrderTrial.natBasis n 0)
  let aa : BooleanNetwork (M.width t) n := TransitionWords.readNet y ⟨0,pow_pos (by omega : 0<n) 5⟩
  have hcan := M.retainedCanonical_exact hn t aa m x r hc hP hP0 hd hdiv hm
  have hshape : (equalOn y (TransitionWords.firstOnly (K:=n^5) aa)).eval (M.encoded x t r) 0=true ↔
      y.eval (M.encoded x t r)=TransitionWords.encode (fun i : Fin (n^5)=>
        if i.val=0 then aa.eval (M.encoded x t r) else OrderTrial.natBasis n 0) := by
    rw [equalOn_value y (TransitionWords.firstOnly (K:=n^5) aa),TransitionWords.firstOnly_eval]
    exact ⟨fun h=>(bitsEquiv _).injective (BitVec.eq_of_toNat_eq h),congrArg (fun z=>(bitsValue z).toNat)⟩
  simpa only [retainedCanonicalList,eval_band,Bool.and_eq_true,aa,
    TransitionWords.readNet_eval] using and_congr hcan hshape
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedComponentOrder
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

lemma retainedComponentOrder_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (a m p : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d)
    (hp : ((bitsValue (p.eval (M.encoded x t r))).toNat).Prime)
    (hpd : (bitsValue (p.eval (M.encoded x t r))).toNat∣d)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat).Coprime d) :
    (bitsValue ((M.retainedComponentOrder t a m p).eval (M.encoded x t r))).toNat=
      dataOrder (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat
        (Nat.gcd d ((bitsValue (p.eval (M.encoded x t r))).toNat^n)) := by
  let z:=M.encoded x t r
  let pN:=(bitsValue (p.eval z)).toNat
  let q:=pN^(d.factorization pN)
  have hq : 2≤q := hp.two_le.trans (Nat.le_pow (hp.factorization_pos_of_dvd (by omega) hpd))
  have hqd : q∣d := Nat.ordProj_dvd d pN
  have hqa : ((bitsValue (a.eval z)).toNat).Coprime q := ha.of_dvd_right hqd
  have hu : IsUnit ((bitsValue (a.eval z)).toNat : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hqa
  have he : (bitsValue ((primeComponent m p).eval z)).toNat=q := by
    rw [primeComponent_value m p z (by change (bitsValue (m.eval (M.encoded x t r))).toNat≠0;omega) hp,hm]
  have ho:=M.retainedOrder_exact hn t a (primeComponent m p) x r hc hP hP0 hq
    (hqd.trans hdiv) hu.unit hu.unit_spec.symm he
  have ht:=dataOrder_correct (by omega : 0<P) hq (hqd.trans hdiv) hu.unit hu.unit_spec.symm
  dsimp only [retainedComponentOrder]
  rw [ho,prime_component_gcd (by omega) hp (hm ▸ (bitsValue (m.eval z)).isLt.le)]
  exact ht.symm

lemma data_component_order_ne_zero {P d a p n : ℕ} (hP : 0<P) (hd : 2≤d)
    (hdiv : d∣P) (hb : d≤2^n) (hp : p.Prime) (hpd : p∣d) (ha : a.Coprime d) :
    dataOrder (trueData P) a (Nat.gcd d (p^n))≠0 := by
  rw [prime_component_gcd (by omega) hp hb]
  let q:=p^(d.factorization p)
  have hq : 2≤q:=hp.two_le.trans (Nat.le_pow (hp.factorization_pos_of_dvd (by omega) hpd))
  have hqd : q∣d:=Nat.ordProj_dvd d p
  have hqa : a.Coprime q:=ha.of_dvd_right hqd
  let : NeZero q:=⟨by omega⟩
  have hu : IsUnit (a : ZMod q):=(ZMod.isUnit_iff_coprime _ _).mpr hqa
  rw [dataOrder_correct hP hq (hqd.trans hdiv) hu.unit hu.unit_spec.symm]
  exact Nat.ne_of_gt (orderOf_pos _)
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableFavorable
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

lemma table_pairwise_iff {ps : List ℕ} {m : ℕ} (hm : 2 ≤ m)
    (hps : ∀ p∈ps,p.Prime) (hcover : ∀ p : ℕ,p.Prime→p ∣ m→p∈ps) (v : ℕ→ℕ) :
    (∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→v p=v q) ↔
      ∀ p∈m.primeFactors,v p=v m.minFac := by
  have hmin:=hcover m.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m)
  constructor
  · intro h p hp
    have H:=Nat.mem_primeFactors.mp hp
    exact h p (hcover p H.1 H.2.1) H.2.1 _ hmin (Nat.minFac_dvd m)
  · intro h p hp hpd q hq hqd
    have hp':=Nat.mem_primeFactors.mpr ⟨hps p hp,hpd,by omega⟩
    have hq':=Nat.mem_primeFactors.mpr ⟨hps q hq,hqd,by omega⟩
    exact (h p hp').trans (h q hq').symm

lemma tableFavorable_correct {ps : List ℕ} {P m n : ℕ} (hP : 0 < P) (hm : 2 ≤ m)
    (hb : m ≤ 2^n) (hd : m ∣ P) (hps : ∀ p∈ps,p.Prime)
    (hcover : ∀ p : ℕ,p.Prime→p ∣ m→p∈ps) (a : ℕ) :
    tableFavorable ps (trueData P) a m n ↔ dataResidueGood (trueData P) a m := by
  rw [tableFavorable,dataResidueGood,dataRecord_correct hP hd,recordFirst_factorization hm]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply not_congr
  have he : (∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→
      padicValNat 2 (dataOrder (trueData P) a (Nat.gcd m (p^n)))=
        padicValNat 2 (dataOrder (trueData P) a (Nat.gcd m (q^n)))) ↔
      ∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→
        padicValNat 2 (dataOrder (trueData P) a (p^m.factorization p))=
          padicValNat 2 (dataOrder (trueData P) a (q^m.factorization q)) := by
    apply forall_congr';intro p
    apply forall_congr';intro hp
    apply forall_congr';intro _
    apply forall_congr';intro q
    apply forall_congr';intro hq
    rw [prime_component_gcd (by omega) (hps p hp) hb,prime_component_gcd (by omega) (hps q hq) hb]
  exact he.trans (table_pairwise_iff hm hps hcover _)
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedFavorable
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

lemma retainedFavorable_table {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedFavorable t a m).eval (M.encoded x t r) 0=true ↔
      tableFavorable (PhysicalTree.tableFactors (M.dataLog x t r)) (trueData P)
        (bitsValue (a.eval (M.encoded x t r))).toNat d n := by
  have hval:=tableNets_values hn (M.fieldRows t) (M.encoded x t r)
  rw [M.fieldRows_values] at hval
  have hp : ∀ p∈tableNets (M.fieldRows t),
      ((bitsValue (p.eval (M.encoded x t r))).toNat).Prime := by
    intro p hp
    apply PhysicalTree.tableFactors_prime hc
    rw [←hval]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  rw [retainedFavorable,eval_band,Bool.and_eq_true,OrderSlots.usableOn_value a m _ (by omega),
    OrderSlots.Usable,ZMod.isUnit_iff_coprime,hm,tableFavorable,←hval,and_assoc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro ha
  rw [bnot_value]
  apply not_congr
  simp only [all_eval,List.forall_mem_map,eval_bor,Bool.or_eq_true,bnot_value,
    dividesOn_value,hm,or_iff_not_imp_left,not_not]
  have hcmp (p q : BooleanNetwork (M.width t) n)
      (hp' : p∈tableNets (M.fieldRows t)) (hq' : q∈tableNets (M.fieldRows t))
      (hpd : (bitsValue (p.eval (M.encoded x t r))).toNat∣d)
      (hqd : (bitsValue (q.eval (M.encoded x t r))).toNat∣d) :
      (sameTwoVal (M.retainedComponentOrder t a m p) (M.retainedComponentOrder t a m q)).eval
        (M.encoded x t r) 0=true ↔
      padicValNat 2 (dataOrder (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat
        (d.gcd ((bitsValue (p.eval (M.encoded x t r))).toNat^n)))=
      padicValNat 2 (dataOrder (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat
        (d.gcd ((bitsValue (q.eval (M.encoded x t r))).toNat^n))) := by
    have hep:=M.retainedComponentOrder_exact hn t a m p x r hc hP hP0 hd hdiv hm (hp p hp') hpd ha
    have heq:=M.retainedComponentOrder_exact hn t a m q x r hc hP hP0 hd hdiv hm (hp q hq') hqd ha
    have hb : d ≤ 2^n:=hm ▸ (bitsValue (m.eval (M.encoded x t r))).isLt.le
    have hnp : (bitsValue ((M.retainedComponentOrder t a m p).eval (M.encoded x t r))).toNat≠0 := by
      rw [hep]
      exact data_component_order_ne_zero (by omega) hd hdiv hb (hp p hp') hpd ha
    have hnq : (bitsValue ((M.retainedComponentOrder t a m q).eval (M.encoded x t r))).toNat≠0 := by
      rw [heq]
      exact data_component_order_ne_zero (by omega) hd hdiv hb (hp q hq') hqd ha
    rw [sameTwoVal_value _ _ _ hnp hnq,hep,heq]
  constructor
  · intro h p hp' hpd q hq' hqd
    exact (hcmp p q hp' hq' hpd hqd).mp (h p hp' q hq' hpd hqd)
  · intro h p hp' q hq' hpd hqd
    exact (hcmp p q hp' hq' hpd hqd).mpr (h p hp' hpd q hq' hqd)

lemma retainedFavorable_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedFavorable t a m).eval (M.encoded x t r) 0=true ↔
      dataResidueGood (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat d := by
  rw [M.retainedFavorable_table hn t a m x r hc hP hP0 hd hdiv hm]
  exact tableFavorable_correct (by omega) hd (hm ▸ (bitsValue (m.eval (M.encoded x t r))).isLt.le)
    hdiv (PhysicalTree.tableFactors_prime hc)
    (PhysicalTree.tableFactors_cover hc hP hP0 (by omega) hdiv) _

lemma retainedGoodList_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (y : BooleanNetwork (M.width t) (n*(n^5+1)))
    (x : Basis c) (r : Trace n t) (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedGoodList t m y).eval (M.encoded x t r) 0=true ↔
      dataGoodList (trueData P) d n (y.eval (M.encoded x t r)) := by
  change (M.retainedGoodList t m y).eval (M.encoded x t r) 0=true ↔
    ∃ i : Fin (n^5),dataResidueGood (trueData P)
      (bitsValue (TransitionWords.read (y.eval (M.encoded x t r)) i)).toNat d
  rw [retainedGoodList,any_eval]
  constructor
  · rintro ⟨v,hv,he⟩
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hv
    refine ⟨i,?_⟩
    rw [M.retainedFavorable_exact hn t _ m x r hc hP hP0 hd hdiv hm,
      TransitionWords.readNet_eval] at he
    exact he
  · rintro ⟨i,hi⟩
    refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    rw [M.retainedFavorable_exact hn t _ m x r hc hP hP0 hd hdiv hm,
      TransitionWords.readNet_eval]
    exact hi
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

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableDirectPhi
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

lemma primesPhiNet_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : (bitsValue (m.eval x)).toNat≠0)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) :
    (bitsValue ((primesPhiNet m ps).eval x)).toNat=(bitsValue (m.eval x)).toNat.totient := by
  let vals:=ps.map (fun q=>(bitsValue (q.eval x)).toNat)
  have hps : ∀ p∈vals,p.Prime := by
    intro p hp'
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp'
    exact hp q hq
  have hd:=PhysicalTree.dvd_cover_power vals hm (bitsValue (m.eval x)).isLt.le hps hcover
  rw [primesPhiNet,totientFromList_value hn,List.map_flatten,List.map_replicate,
    totientScan_exact _ _ (Nat.pos_of_ne_zero hm) (by
      intro p hp'
      obtain ⟨qs,hqs,hp'⟩:=List.mem_flatten.mp hp'
      have he:=(List.mem_replicate.mp hqs).2
      subst qs
      exact hps p hp') (by
      rw [List.prod_flatten,List.map_replicate,List.prod_replicate]
      exact hd)]
  exact Nat.mod_eq_of_lt ((Nat.totient_le _).trans_lt (bitsValue (m.eval x)).isLt)

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableLevelCircuit
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
open scoped BigOperators

lemma equalLevelSum_le_totient {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (ho : Odd m) :
    (∑ t : Fin (n+1),∏ p : Component m,
      closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val)≤ m.totient := by
  classical
  let p₀ : Component m := ⟨m.minFac,Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd m,by omega⟩⟩
  have h0 : m≠0:=by omega
  let : NeZero m:=⟨h0⟩
  rw [←equal_component_card h0 hb ho p₀]
  calc
    _≤Fintype.card (∀ p : Component m,ComponentUnits m p):=Fintype.card_subtype_le _
    _=Fintype.card (ZMod m)ˣ:=(Fintype.card_congr (unitCRT m h0).toEquiv).symm
    _=m.totient:=ZMod.card_units_eq_totient m

lemma componentLevelProduct_lt {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (ho : Odd m)
    (t : Fin (n+1)) :
    (∏ p : Component m,closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val)<2^n := by
  have hs:=Finset.single_le_sum (f:=fun t : Fin (n+1)=>∏ p : Component m,
    closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ t)
  exact (hs.trans (equalLevelSum_le_totient hm hb ho)).trans_lt ((Nat.totient_le m).trans_lt hb)

lemma table_level_product {ps : List ℕ} {m : ℕ} (hm : m≠0)
    (hp : ∀ p∈ps,p.Prime) (hcover : ∀ p : ℕ,p.Prime→p∣m→p∈ps) (t : ℕ) :
    (∏ p∈ps.toFinset,if p∣m then closedLevelCount (primePowerUnitCount p (m.factorization p)) t else 1)=
      ∏ p : Component m,closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t := by
  classical
  have he : ps.toFinset.filter (fun p=>p∣m)=m.primeFactors := by
    ext p
    simp only [Finset.mem_filter,List.mem_toFinset]
    constructor
    · rintro ⟨hps,hpd⟩
      exact Nat.mem_primeFactors.mpr ⟨hp p hps,hpd,hm⟩
    · intro h
      obtain ⟨hpp,hpd,_⟩:=Nat.mem_primeFactors.mp h
      exact ⟨hcover p hpp hpd,hpd⟩
  rw [←Finset.prod_filter,he]
  exact (Finset.prod_coe_sort _ _).symm

namespace BitArithmetic

lemma tableLevelNet_value {k n : ℕ} (hn : 2 ≤ n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (ho : Odd (bitsValue (m.eval x)).toNat)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) (t : Fin (n+1)) :
    (bitsValue ((tableLevelNet m ps t.val).eval x)).toNat=
      ∏ p : Component (bitsValue (m.eval x)).toNat,
        closedLevelCount (primePowerUnitCount p.val ((bitsValue (m.eval x)).toNat.factorization p.val)) t.val := by
  let f : ℕ→ℕ:=fun p=>if p∣(bitsValue (m.eval x)).toNat then
    closedLevelCount (primePowerUnitCount p ((bitsValue (m.eval x)).toNat.factorization p)) t.val else 1
  have hh:=distinctProductNet_value (fun p=>componentLevelNet m p t.val) ps x f (by
    intro p hp'
    have he:=componentLevelNet_value hn m p x (by omega) (hp p hp') t.val
    change (bitsValue ((componentLevelNet m p t.val).eval x)).toNat=f (bitsValue (p.eval x)).toNat at he
    rw [←he,Nat.mod_eq_of_lt (bitsValue ((componentLevelNet m p t.val).eval x)).isLt])
  rw [tableLevelNet,hh]
  dsimp only [f]
  rw [table_level_product (by omega) (by
    intro p hp'
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp'
    exact hp q hq) hcover t.val]
  exact Nat.mod_eq_of_lt (componentLevelProduct_lt hm (bitsValue (m.eval x)).isLt ho t)

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordSumCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

lemma sumNet_nat {k w : ℕ} (as : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((sumNet as).eval x)).toNat=
      (as.map (fun a=>(bitsValue (a.eval x)).toNat)).sum%2^w := by
  induction as with
  | nil=>simp [sumNet,wordConstant_eval]
  | cons a as ih=>
    simp only [sumNet,eval_comp,eval_pair,add_word,BitVec.toNat_add,ih,
      List.map_cons,List.sum_cons,Nat.add_mod_mod]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableFavorableCount
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
open scoped BigOperators
namespace BitArithmetic

lemma tableBadCountNet_value {k n : ℕ} (hn : 2 ≤ n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (ho : Odd (bitsValue (m.eval x)).toNat)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) :
    (bitsValue ((tableBadCountNet m ps).eval x)).toNat=
      ∑ t : Fin (n+1),∏ p : Component (bitsValue (m.eval x)).toNat,
        closedLevelCount (primePowerUnitCount p.val ((bitsValue (m.eval x)).toNat.factorization p.val)) t.val := by
  have hs:=equalLevelSum_le_totient hm (bitsValue (m.eval x)).isLt ho
  rw [tableBadCountNet,sumNet_nat,List.map_ofFn,List.sum_ofFn]
  have he : (fun t : Fin (n+1)=>(bitsValue ((tableLevelNet m ps t.val).eval x)).toNat)=
      (fun t : Fin (n+1)=>∏ p : Component (bitsValue (m.eval x)).toNat,
        closedLevelCount (primePowerUnitCount p.val ((bitsValue (m.eval x)).toNat.factorization p.val)) t.val) := by
    funext t
    exact tableLevelNet_value hn m ps x hm ho hp hcover t
  change (∑ t : Fin (n+1),(bitsValue ((tableLevelNet m ps t.val).eval x)).toNat)%2^n=_
  rw [he,Nat.mod_eq_of_lt (hs.trans_lt ((Nat.totient_le _).trans_lt (bitsValue (m.eval x)).isLt))]

lemma tableFavorableCountNet_value {k n : ℕ} (hn : 2 ≤ n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (ho : Odd (bitsValue (m.eval x)).toNat)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) :
    (bitsValue ((tableFavorableCountNet m ps).eval x)).toNat=
      favorableCount (bitsValue (m.eval x)).toNat n := by
  rw [tableFavorableCountNet,natSubOn_value,primesPhiNet_value (by omega) m ps x (by omega) hp hcover,
    tableBadCountNet_value hn m ps x hm ho hp hcover]
  rfl

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedFavorableCount
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

lemma retainedFavorableCount_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (ho : Odd d)
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedFavorableCount t m).eval (M.encoded x t r))).toNat=
      dataFavorable (trueData P) d n := by
  rw [dataFavorable_correct (by omega) (by omega) hdiv]
  have hval:=tableNets_values hn (M.fieldRows t) (M.encoded x t r)
  rw [M.fieldRows_values] at hval
  have hh:=tableFavorableCountNet_value hn m (tableNets (M.fieldRows t)) (M.encoded x t r)
    (hm ▸ hd) (hm ▸ ho) (by
      intro p hp
      apply PhysicalTree.tableFactors_prime hc
      rw [←hval]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩) (by
      rw [hm,hval]
      exact PhysicalTree.tableFactors_cover hc hP hP0 (by omega) hdiv)
  simpa only [retainedFavorableCount,hm] using hh

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedListFilter
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
namespace Completion.Expressions

lemma listRateCoin_value (n K : ℕ) (v : Fin 3→ℕ) (hm : v 0≤2^n) :
    (listRateCoin n K).eval v=1-(1-(v 1:ℚ)/(2:ℚ)^(Nat.clog 2 (v 0)))^K := by
  rw [listRateCoin,RatExpr.repeatedSuccess_value,RatExpr.eval_div,RatExpr.eval_ofNat,
    RatExpr.eval_ofNat,OrderTrial.Expressions.coveringPow_correct]
  · simp only [NatExpr.eval,Nat.cast_pow,Nat.cast_ofNat]
  · exact hm
end Completion.Expressions

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma listFilterVars_eval (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n))
    (x : Basis (M.width t)) (r : PhysicalListSlots.Result n)
    (hraw : raw.eval x=PhysicalListSlots.layout n r) :
    (bitsValue ((M.listFilterVars t m raw 0).eval x)).toNat=(bitsValue (m.eval x)).toNat ∧
    (bitsValue ((M.listFilterVars t m raw 1).eval x)).toNat=
      (bitsValue ((M.retainedFavorableCount t m).eval x)).toNat ∧
    (bitsValue ((M.listFilterVars t m raw 2).eval x)).toNat=(bitsValue r.2.2.2).toNat := by
  simp only [listFilterVars,Fin.reduceEq,ite_true, if_true,ite_false, if_false,eval_comp]
  simp only [resizeWord_toNat (show n ≤ listVarWidth n from Nat.le_add_right _ _),
    resizeWord_toNat (show listCoinWidth n ≤ listVarWidth n from Nat.le_add_left _ _),hraw]
  change _ ∧ _ ∧ (bitsValue ((Completion.retentionWires _ _ _ _).eval (Completion.layout _ _ _ _ r))).toNat=_
  rw [Completion.retentionWires_eval]
  exact ⟨True.intro,True.intro,rfl⟩

/-- Concrete local same-history test: the only inputs are the physical retained
words and the complete verified table, not an assumed success oracle. -/
theorem retainedListFilter_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n))
    (x : Basis c) (h : Trace n t) (r : PhysicalListSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (ho : Odd d)
    (hm : (bitsValue (m.eval (M.encoded x t h))).toNat=d)
    (hr : raw.eval (M.encoded x t h)=PhysicalListSlots.layout n r) :
    (M.retainedListFilter (by omega) t m raw).eval (M.encoded x t h) 0=true ↔
      dataListPassed (trueData P) (m.eval (M.encoded x t h)) (by omega) r := by
  have hv:=M.listFilterVars_eval t m raw (M.encoded x t h) r hr
  have hf:=M.retainedFavorableCount_exact hn t m x h hc hP hP0 hd hdiv ho hm
  unfold retainedListFilter dataListPassed
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval r
  · exact hv.2.2
  · rw [M.retainedGoodList_exact hn t m _ x h hc hP hP0 hd hdiv hm]
    erw [eval_comp,eval_comp,hr]
    change dataGoodList (trueData P) d n
      ((PhysicalListSlots.ordinaryNet n).eval ((Completion.ordinaryWires _ _ _ _).eval
        (Completion.layout _ _ _ _ r))) ↔ _
    rw [Completion.ordinaryWires_eval,PhysicalListSlots.ordinaryNet_eval,hm]
  · rw [M.retainedCanonicalList_exact hn t m _ x h hc hP hP0 hd hdiv hm]
    erw [eval_comp,hr]
    change dataCanonicalList (trueData P) d n _
      ((Completion.guessWires _ _ _ _).eval (Completion.layout _ _ _ _ r)) ↔ _
    rw [Completion.guessWires_eval,hm]
  · rw [Completion.Expressions.listRateCoin_value]
    · rw [hv.1,hv.2.1,hf,hm]
      rfl
    · rw [hv.1]
      exact (bitsValue (m.eval (M.encoded x t h))).isLt.le
  · exact RatExpr.eval_const _ _
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedListDummy
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

lemma listDummyFilter_exact (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) (x : Basis (M.width t))
    (r : PhysicalListSlots.Result n) (hr : raw.eval x=PhysicalListSlots.layout n r) :
    (M.listDummyFilter t m raw).eval x 0=true ↔ UniversalSplit.dummyList r := by
  have hv:=M.listFilterVars_eval t m raw x r hr
  have hh : Completion.test (fun _=>True) (fun y=>y=natBasis _ 0) 1 (Completion.target n) r ↔
    UniversalSplit.dummyList r := Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) r
  refine Iff.trans ?_ hh
  unfold listDummyFilter
  apply Completion.predicateFilter_test
  · rw [eval_comp,hr]
    exact Completion.rareWires_eval r
  · exact hv.2.2
  · simp only [eval_constant]
  · rw [zeroWord_value,eval_comp,hr]
    change (bitsValue ((Completion.guessWires _ _ _ _).eval
      (Completion.layout _ _ _ _ r))).toNat=0 ↔ _
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

lemma dataOrderPassed_correct {M n : ℕ} (hM : 0<M) (a m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat∣M)
    (r : OrderSlots.Result n) :
    dataOrderPassed (trueData M) a m r ↔ OrderSlots.passed a m r := by
  classical
  rw [dataOrderPassed,residueUsable_iff]
  by_cases h : OrderSlots.Usable a m
  · rw [ite_eq_left h,OrderSlots.passed,dite_eq_left h,
      dataOrder_correct hM hm hd h.2.unit h.2.unit_spec.symm,
      dataOrderSuccess_correct hM hm hd h.2.unit h.2.unit_spec.symm]
    change Completion.test _ _ _ _ r ↔ Completion.passed _ (natBasis _ (OrderSlots.unitOrder a m)) _ _ r
    rw [OrderSlots.unitOrder,dite_eq_left h]
    exact Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) r
  · rw [ite_eq_right h,OrderSlots.passed,dite_eq_right h]
    change Completion.test _ _ _ _ r ↔ Completion.passed _ (natBasis _ (OrderSlots.unitOrder a m)) _ _ r
    rw [OrderSlots.unitOrder,dite_eq_right h]
    exact Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) r

/-- All list/order/retention decisions are on the actual retained raw block.
The record may be that of any actual node whose label is divisible by m. -/
lemma dataSplitPassed_correct {M n : ℕ} (hM : 0<M) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat∣M) (hn : 0<n)
    (r : UniversalSplit.Raw n) :
    dataSplitPassed (trueData M) m hn r ↔ UniversalSplit.passed m r := by
  classical
  rw [dataSplitPassed,UniversalSplit.passed]
  split_ifs with hh
  · change (_ ∧ ∀ i,_) ↔ (_ ∧ ∀ i,_)
    exact and_congr (dataListPassed_correct hM m hm hd hn r.1)
      (forall_congr' (fun i=>dataOrderPassed_correct hM _ m hm hd (r.2 i)))
  · rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedSplitFilter
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

lemma splitModulus_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.splitModulus t raw).eval x=q := by
  rw [splitModulus,eval_comp,hr,FixedSplit.modulusNet_eval]
lemma splitList_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.splitList t raw).eval x=PhysicalListSlots.layout n r.1 := by
  rw [splitList,eval_comp,eval_comp,hr,FixedSplit.launchWires_eval,FixedSplit.listWires_eval]
lemma splitBase_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) (i : Fin (n^5)) :
    (M.splitBase t raw i).eval x=FixedSplit.bases r.1 i := by
  rw [splitBase,eval_comp,hr,FixedSplit.actualBaseNet_eval]
lemma splitOrder_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) (i : Fin (n^5)) :
    (M.splitOrder t raw i).eval x=OrderSlots.layout n (r.2 i) := by
  rw [splitOrder,eval_comp,hr,FixedSplit.actualOrderRawNet_eval]

lemma splitDummyFilter_exact (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.splitDummyFilter t raw).eval x 0=true ↔ UniversalSplit.dummy r := by
  rw [splitDummyFilter,eval_band,Bool.and_eq_true,
    M.listDummyFilter_exact t _ _ x r.1 (M.splitList_eval t raw x q r hr),all_eval]
  simp only [List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  rw [M.orderDummyFilter_exact t _ _ _ x (r.2 i) (M.splitOrder_eval t raw x q r hr i)]
  exact Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) (r.2 i)

/-- The hard/ordinary/rare/dummy selection is on the actual retained split's
modulus and coin strings. The table is the same final retained complete log. -/
theorem retainedSplitFilter_exact {N P : ℕ} (hn : 128≤n) (t : ℕ)
    (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis c) (h : Trace n t) (q : Basis n) (r : UniversalSplit.Raw n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hdiv : UniversalSplit.Hard (bitsValue q).toNat → (bitsValue q).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=FixedSplit.encoding q r) :
    (M.retainedSplitFilter (by omega) t raw).eval (M.encoded x t h) 0=true ↔
      dataSplitPassed (trueData P) q (by omega) r := by
  classical
  rw [retainedSplitFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,UniversalSplit.hardOn_value hn,
    M.splitModulus_eval t raw _ q r hr,dataSplitPassed]
  by_cases hh : UniversalSplit.Hard (bitsValue q).toNat
  · simp only [hh,ite_eq_left,true_and,not_true_eq_false,false_and,or_false]
    rw [splitActualFilter,eval_band,Bool.and_eq_true,
      M.retainedListFilter_exact (by omega) t _ _ x h r.1 hc hP hP0 hh.1 (hdiv hh) hh.2.2.1
        (by rw [M.splitModulus_eval t raw _ q r hr]) (M.splitList_eval t raw _ q r hr),
      M.splitModulus_eval t raw _ q r hr,all_eval]
    simp only [List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    rw [M.retainedOrderFilter_exact (by omega) t _ _ _ x h (r.2 i) hc hP hP0
      (by rw [M.splitModulus_eval t raw _ q r hr];exact hh.1)
      (by rw [M.splitModulus_eval t raw _ q r hr];exact hdiv hh)
      (M.splitOrder_eval t raw _ q r hr i),M.splitBase_eval t raw _ q r hr,
      M.splitModulus_eval t raw _ q r hr]
  · simp only [hh,ite_eq_right,false_and,not_false_eq_true,true_and,false_or]
    exact M.splitDummyFilter_exact t raw _ q r hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedSplitPass
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

lemma retainedSplitFilter_nonhard (hn : 128≤n) (t : ℕ)
    (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hh : ¬UniversalSplit.Hard (bitsValue q).toNat)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.retainedSplitFilter (by omega) t raw).eval x 0=true ↔ UniversalSplit.passed q r := by
  classical
  rw [retainedSplitFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,UniversalSplit.hardOn_value hn,
    M.splitModulus_eval t raw x q r hr]
  simp only [hh,false_and,not_false_eq_true,true_and,false_or]
  rw [UniversalSplit.passed,dite_eq_right hh]
  exact M.splitDummyFilter_exact t raw x q r hr

lemma retainedSplitFilter_passed {N P : ℕ} (hn : 128≤n) (t : ℕ)
    (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis c) (h : Trace n t) (q : Basis n) (r : UniversalSplit.Raw n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hdiv : UniversalSplit.Hard (bitsValue q).toNat → (bitsValue q).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=FixedSplit.encoding q r) :
    (M.retainedSplitFilter (by omega) t raw).eval (M.encoded x t h) 0=true ↔
      UniversalSplit.passed q r := by
  classical
  by_cases hh : UniversalSplit.Hard (bitsValue q).toNat
  · rw [M.retainedSplitFilter_exact hn t raw x h q r hc hP hP0 hdiv hr]
    exact dataSplitPassed_correct (by omega) q hh.1 (hdiv hh) (by omega) r
  · exact M.retainedSplitFilter_nonhard hn t raw _ q r hh hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveNode
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
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree
namespace PhysicalNode

lemma natBasis_zero (w : ℕ) : natBasis w 0=(fun _=>false) := by
  apply (bitsEquiv w).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue (natBasis w 0)).toNat=(bitsValue (fun _=>false)).toNat
  rw [natBasis_value,zeroBasis_value]
  simp

lemma start_zero {n : ℕ} (q : Basis n) (hq : (bitsValue q).toNat=0) :
    NodeKernel.start q=NodeStateCircuit.pack (s:=2*n) [] [] false := by
  rw [NodeKernel.start,startNet_eval,hq,natBasis_zero,NodeStateCircuit.pack,NodeStateCircuit.pack]
  apply congrArg (fun x=>Fin.append (Fin.append x (stackEncoding (2*n+1) (n+1) [])) (fun _=>false))
  apply block_ext
  intro i
  rw [block_stackEncoding,block_stackEncoding]
  cases he : i.val with
  | zero=>rfl
  | succ j=>rfl

lemma config_zero {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (hq : (bitsValue q).toNat=0)
    (t : ℕ) (r : SplitMachine.Trace n t) :
    (machine n (2*n)).config (NodeKernel.start q) t r=NodeStateCircuit.pack [] [] false := by
  induction t with
  | zero=>exact start_zero q hq
  | succ t ih=>
    change (machine n (2*n)).next ((machine n (2*n)).config (NodeKernel.start q) t r.1) r.2=_
    rw [ih,next_nil hn]

lemma query_zero {n : ℕ} (hn : 128 ≤ n) (q : Basis n) (hq : (bitsValue q).toNat=0)
    (t : ℕ) (r : SplitMachine.Trace n t) :
    (bitsValue ((query n (2*n)).eval
      ((machine n (2*n)).config (NodeKernel.start q) t r))).toNat=0 := by
  rw [config_zero hn q hq,query,eval_comp,NodeStateCircuit.top_pack]
  change (bitsValue ((resizeWord (n+1) n).eval (fun _=>false))).toNat=0
  rw [resizeWord_value,zeroBasis_value]
  simp
end PhysicalNode

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SplitHistoryAccess
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
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

lemma previousNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : FixedSplit.Raw n) :
    (M.previousNet t).eval (M.encoded x (t+1) (h,r))=M.encoded x t h := by
  rw [previousNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (FixedSplit.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork) ∘
      firstRegister (M.width t) (FixedSplit.width n) M.initWork=_
  rw [packed_first,packed_first]
lemma lastSplitNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : FixedSplit.Raw n) :
    (M.lastSplitNet t).eval (M.encoded x (t+1) (h,r))=
      FixedSplit.encoding (M.query.eval (M.config x t h)) r := by
  rw [lastSplitNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (FixedSplit.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork) ∘
      targetRegister (M.width t) (FixedSplit.width n) M.initWork=_
  rw [packed_first,packed_targetRegister]
end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedNodeFilter
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

lemma nodePrefixFilter_passed {N : ℕ} (hn : 128≤n) (T s : ℕ)
    (raw : BooleanNetwork (M.width T) ((PhysicalNode.machine n (2*n)).width s))
    (x : Basis c) (h : Trace n T) (q : Basis n) (r : SplitMachine.Trace n s)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x T h))
    (hq : (bitsValue q).toNat=0 ∨ 2≤(bitsValue q).toNat)
    (hP : (bitsValue q).toNat≠0 → (bitsValue q).toNat∈(M.dataLog x T h).map Prod.fst)
    (hr : raw.eval (M.encoded x T h)=
      (PhysicalNode.machine n (2*n)).encoded (NodeKernel.start q) s r) :
    (M.nodePrefixFilter (by omega) T s raw).eval (M.encoded x T h) 0=true ↔
      (PhysicalNode.machine n (2*n)).passed (NodeKernel.start q) s r := by
  induction s with
  | zero=>simp [nodePrefixFilter,SplitMachine.passed]
  | succ s ih=>
    rw [nodePrefixFilter,eval_band,Bool.and_eq_true]
    apply and_congr
    · apply ih _ r.1
      rw [eval_comp,hr,SplitMachine.previousNet_encoded]
    · have hraw : (raw.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s)).eval
          (M.encoded x T h)= FixedSplit.encoding
          ((PhysicalNode.query n (2*n)).eval ((PhysicalNode.machine n (2*n)).config
            (NodeKernel.start q) s r.1)) r.2 := by
        rw [eval_comp,hr,SplitMachine.lastSplitNet_encoded]
        rfl
      rcases hq with hz | hpos
      · apply M.retainedSplitFilter_nonhard hn T _ _ _ r.2 _ hraw
        have hzero:=PhysicalNode.query_zero hn q hz s r.1
        intro hh
        have hh':=hh.1
        omega
      · apply M.retainedSplitFilter_passed hn T _ x h _ r.2 hc (hP (by omega)) (by omega) _ hraw
        intro hh
        have hs:=PhysicalNode.query_safe hn hpos (bitsValue q).isLt s r.1
        rw [←PhysicalNode.startNet_eval n q] at hs
        change (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat=0 ∨
          (2 ≤ (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat ∧
          (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat<2^n ∧
          (bitsValue ((PhysicalNode.query n (2*n)).eval
          ((PhysicalNode.machine n (2*n)).config (NodeKernel.start q) s r.1))).toNat∣(bitsValue q).toNat) at hs
        rcases hs with hz | hs
        · have hh':=hh.1
          omega
        · exact hs.2.2

/-- Every split in the actual retained node history is tested against the final
read-only verified table. No fresh random experiment or ideal flag is inserted. -/
theorem retainedNodeFilter_passed {N : ℕ} (hn : 128≤n) (T : ℕ)
    (raw : BooleanNetwork (M.width T) (NodeKernel.width n))
    (x : Basis c) (h : Trace n T) (q : Basis n) (r : NodeKernel.Raw n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x T h))
    (hq : (bitsValue q).toNat=0 ∨ 2≤(bitsValue q).toNat)
    (hP : (bitsValue q).toNat≠0 → (bitsValue q).toNat∈(M.dataLog x T h).map Prod.fst)
    (hr : raw.eval (M.encoded x T h)=NodeKernel.encoding q r) :
    (M.retainedNodeFilter (by omega) T raw).eval (M.encoded x T h) 0=true ↔ NodeKernel.passed q r :=
  M.nodePrefixFilter_passed hn T (2*n) raw x h q r hc hq hP hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveTree
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
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree
namespace PhysicalTree

lemma verified_query_safe {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (r : NodeMachine.Trace n t)
    (hv : (machine n).verified (initialQueue n N) t r) :
    let m:=(bitsValue ((query n).eval ((machine n).config (initialQueue n N) t r))).toNat
    m=0 ∨ 2 ≤ m := by
  dsimp only
  rw [verified_query_value hn hN hb t r hv]
  have hh:=run_bounds (xs:=[N]) (B:=2^n) (by
    intro a ha
    have he : a=N := List.mem_singleton.mp ha
    subst a
    exact ⟨hN,hb⟩) t
  cases he : run t [N] with
  | nil=>exact Or.inl rfl
  | cons a as=>exact Or.inr (hh a (by rw [he];simp)).1
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedTreeFilter
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

lemma treePrefixFilter_passed_oai {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (T s : ℕ) (h : NodeMachine.Trace n T) (r : NodeMachine.Trace n s)
    (raw : BooleanNetwork ((machine n).width T) ((machine n).width s))
    (hc : CompleteLog n N ((machine n).dataLog (initialQueue n N) T h))
    (hv : (machine n).verified (initialQueue n N) s r)
    (hsub : ∀ a∈(machine n).dataLog (initialQueue n N) s r,
      a∈(machine n).dataLog (initialQueue n N) T h)
    (hr : raw.eval ((machine n).encoded (initialQueue n N) T h)=
      (machine n).encoded (initialQueue n N) s r) :
    ((machine n).treePrefixFilter (by omega) T s raw).eval
      ((machine n).encoded (initialQueue n N) T h) 0=true ↔
      (machine n).passed (initialQueue n N) s r := by
  induction s with
  | zero=>simp [NodeMachine.treePrefixFilter,NodeMachine.passed]
  | succ s ih=>
    rw [NodeMachine.treePrefixFilter,eval_band,Bool.and_eq_true]
    apply and_congr
    · apply ih r.1 _ hv.1 (fun a ha=>hsub a (List.mem_cons_of_mem _ ha))
      rw [eval_comp,hr,NodeMachine.previousNet_encoded]
    · apply (machine n).retainedNodeFilter_passed hn T _ (initialQueue n N) h _ r.2 hc
        (verified_query_safe hn hN hb s r.1 hv.1)
      · intro _
        apply List.mem_map.mpr
        refine ⟨_,hsub _ (List.mem_cons_self),rfl⟩
      · rw [eval_comp,hr,NodeMachine.lastNodeNet_encoded]
        rfl

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed_oai := @OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed_oai
