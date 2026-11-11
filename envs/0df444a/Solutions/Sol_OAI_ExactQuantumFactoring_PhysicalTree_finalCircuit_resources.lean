-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:12:14.381362+00:00
-- url     : https://prove2.me/submissions/8c092845-17d5-48e6-8dd1-1f74ce36627e

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGDivisionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGBounds
open Std.Sat Std.Tactic.BVDecide
open BVExpr.bitblast
variable {α : Type} [Hashable α] [DecidableEq α]

lemma div_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastUdiv aig input).aig.decls.size ≤ aig.decls.size+36*w*w+7*w := by
  unfold blastUdiv
  dsimp only
  apply (ite_size _ _).trans
  apply (Nat.add_le_add_right (div_go_size _ _ _ _ _ _ _ _) (3*w)).trans
  have hh := eq_size aig ⟨input.rhs, blastConst aig 0#w⟩
  omega

end ExactQuantumFactoring.AIGBounds


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanProgram
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.cnotAt_target _root_.OAI.ExactQuantumFactoring.notAt_target _root_.OAI.ExactQuantumFactoring.toffoliAt_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

namespace BooleanOp

lemma compile_length {q : ℕ} {t : Fin q} (o : BooleanOp q t) :
    o.compile.length ≤ 2 := by
  cases o with
  | constant b => cases b <;> simp [compile]
  | copy => simp [compile]
  | neg => simp [compile]
  | conj a b ha hb => simp only [compile]; split <;> simp

end BooleanOp

lemma BooleanProgram.compile_length {q : ℕ} (p : BooleanProgram q) :
    p.compile.length ≤ 2 * p.length := by
  induction p with
  | nil => simp [compile]
  | cons o p ih =>
    change (o.2.compile ++ BooleanProgram.compile p).length ≤ 2 * (o :: p).length
    rw [List.length_append, List.length_cons]
    have h := o.2.compile_length
    omega

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanNetwork
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_assign _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_band _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bit _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bnot _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bxor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_constant _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_mux _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_node _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_rewire _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_select _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_node _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring

namespace BoolNet

lemma program_length {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) :
    (p.program h).length = p.count := by
  induction p with
  | input => rfl
  | add p o ih => simp [program, count, ih]

lemma compile_length {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) :
    (BooleanProgram.compile (p.program h)).length ≤ 2 * p.count := by
  simpa only [program_length] using BooleanProgram.compile_length (p.program h)

end BoolNet


end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanAlgebra
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.BooleanNetwork

lemma count_sequence {n : ℕ} (cs : List (BooleanNetwork n n)) :
    (sequence cs).net.count = (cs.map (fun c => c.net.count)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [sequence, count_comp, ih]

lemma count_iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) :
    (iterate c k).net.count = k * c.net.count := by
  simp [iterate, count_sequence, List.sum_replicate]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanFold
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

lemma any_count {n c : ℕ} (cs : List (BooleanNetwork n 1))
    (h : ∀ a ∈ cs, a.net.count ≤ c) : (any cs).net.count ≤ cs.length*(c+4)+1 := by
  induction cs with
  | nil => simp [any]
  | cons a cs ih =>
    have ha := h a (by simp)
    have hc := ih (fun b hb => h b (by simp [hb]))
    simp only [any,count_bor,List.length_cons]
    nlinarith

lemma all_count {n c : ℕ} (cs : List (BooleanNetwork n 1))
    (h : ∀ a ∈ cs, a.net.count ≤ c) : (all cs).net.count ≤ cs.length*(c+1)+1 := by
  induction cs with
  | nil => simp [all]
  | cons a cs ih =>
    have ha := h a (by simp)
    have hc := ih (fun b hb => h b (by simp [hb]))
    simp only [all,count_band,List.length_cons]
    nlinarith

end ExactQuantumFactoring.BooleanNetwork


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

lemma div_count (w : ℕ) : (div w).net.count ≤ 216*w*w+56*w+6 := by
  have h := compileVec_count (blastUdiv (inputs (w+w)).1 (binaryInputs w)).aig
    (blastUdiv (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.div_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [div]
  nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ArithmeticPredicates
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

lemma wordLe_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (wordLe a b).net.count ≤ a.net.count+b.net.count+48*w+9 := by
  simp only [wordLe,count_bnot]
  have := wordLt_count b a
  omega

lemma wordEq_count (w : ℕ) : (wordEq w).net.count ≤ 96*w+21 := by
  simp only [wordEq,count_bnot,count_bor,count_comp,count_select,zero_add]
  have := ult_count w
  omega

lemma staticPower_count (w e : ℕ) : (staticPower w e).net.count ≤
    w+e*(90*w*w+14*w+6) := by
  simp only [staticPower,count_comp,count_pair,count_select,wordConstant_count,zero_add,
    count_rewire,count_iterate,staticPowerStep]
  have h := mul_count w
  exact Nat.add_le_add_left (Nat.mul_le_mul_left e h) w

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_StaticPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma equalOn_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (equalOn a b).net.count ≤ a.net.count+b.net.count+96*w+21 := by
  simp only [equalOn,count_comp,count_pair]
  have := wordEq_count w
  omega

lemma constMod_count (w d : ℕ) : (constMod w d).net.count ≤ 216*w*w+57*w+6 := by
  simp only [constMod,count_comp,count_pair,count_select,wordConstant_count,zero_add]
  have := mod_count w
  omega

lemma dividesNet_count (w d : ℕ) : (dividesNet w d).net.count ≤ 216*w*w+154*w+27 := by
  have h := equalOn_count (constMod w d) (wordConstant (BitVec.ofNat w 0))
  rw [wordConstant_count] at h
  have := constMod_count w d
  change (equalOn (constMod w d) (wordConstant (BitVec.ofNat w 0))).net.count ≤ _
  omega

lemma constPowMod_count (w s j : ℕ) :
    (constPowMod w s j).net.count ≤ 3*w+w*(3672*w*w+436*w+36) := by
  simp only [constPowMod,count_comp,count_pair,count_select,wordConstant_count,count_rewire,zero_add]
  have := modularPower_count w w
  omega

lemma powerOneNet_count (w s j : ℕ) :
    (powerOneNet w s j).net.count ≤ 100*w+21+w*(3672*w*w+436*w+36) := by
  have h := equalOn_count (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))
  rw [wordConstant_count] at h
  have := constPowMod_count w s j
  change (equalOn (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))).net.count ≤ _
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AKSNetworks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma orderTests_count (w s k : ℕ) : (orderTests w s k).net.count ≤
    k*(100*w+23+w*(3672*w*w+436*w+36))+1 := by
  have h := all_count (c := 100*w+22+w*(3672*w*w+436*w+36))
    (List.ofFn (fun i : Fin k => (powerOneNet w s (i.val+1)).bnot)) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      rw [count_bnot]
      have := powerOneNet_count w s (i.val+1)
      omega)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [orderTests,List.length_ofFn])
  ring

lemma properDivisor_count (w d : ℕ) :
    (properDivisor w d).net.count ≤ 216*w*w+203*w+36 := by
  have h := wordLt_count (wordConstant (n := w) (BitVec.ofNat w d)) (select id)
  rw [wordConstant_count,count_select] at h
  have hd := dividesNet_count w d
  rw [properDivisor,count_band]
  omega

lemma noSmallDivisor_count (w B : ℕ) : (noSmallDivisor w B).net.count ≤
    (B-1)*(216*w*w+203*w+38)+1 := by
  have h := all_count (c := 216*w*w+203*w+37)
    (List.ofFn (fun i : Fin (B-1) => (properDivisor w (i.val+2)).bnot)) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      rw [count_bnot]
      have := properDivisor_count w (i.val+2)
      omega)
  simpa only [noSmallDivisor,List.length_ofFn] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordBlocks
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma wordBlocks_count {n s w c : ℕ} (f : Fin s → BooleanNetwork n w)
    (h : ∀ i, (f i).net.count ≤ c) : (wordBlocks f).net.count ≤ s*w*c := by
  apply count_vector_le
  intro i
  simpa only [count_rewire] using h (finProdFinEquiv.symm i).1

lemma addMod_count {n w : ℕ} (a b m : BooleanNetwork n w) :
    (addMod a b m).net.count ≤ a.net.count+b.net.count+m.net.count+
      216*(w+1)^2+142*(w+1)+15 := by
  have h₁ := add_count (w+1)
  have h₂ := mod_count (w+1)
  simp only [addMod,count_rewire,count_comp,count_pair,count_padRight]
  nlinarith

lemma sumMod_count {n w c : ℕ} (m : BooleanNetwork n w) (as : List (BooleanNetwork n w))
    (h : ∀ a ∈ as, a.net.count ≤ c) :
    (sumMod m as).net.count ≤ w+as.length*(c+m.net.count+216*(w+1)^2+142*(w+1)+15) := by
  induction as with
  | nil => simp [sumMod,wordConstant_count]
  | cons a as ih =>
    have ha := h a (by simp)
    have hi := ih (fun b hb => h b (by simp [hb]))
    have hh := addMod_count a (sumMod m as) m
    simp only [sumMod,List.length_cons]
    nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicCircuit
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

lemma cyclicTerm_count {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (k i : Fin s) :
    (cyclicTerm a b m k i).net.count ≤ a.net.count+b.net.count+m.net.count+
      (1224*w*w+143*w+12) := by
  have h := mulMod_count (a.comp (blockNet s w i)) (b.comp (blockNet s w (k-i))) m
  simpa only [cyclicTerm,count_comp,blockNet_count,add_zero] using h

lemma cyclicMulNet_count {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : (cyclicMulNet a b m).net.count ≤
      cyclicMulBound s w a.net.count b.net.count m.net.count := by
  apply wordBlocks_count
  intro k
  have h := sumMod_count m (List.ofFn (cyclicTerm a b m k)) (by
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact cyclicTerm_count a b m k i)
  simp only [List.length_ofFn] at h
  
  nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicConstants
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

lemma arrayConstant_count {n s w : ℕ} (f : Fin s → ℕ) :
    (arrayConstant (n := n) s w f).net.count ≤ s*w*w := by
  apply wordBlocks_count
  intro i
  exact (wordConstant_count _).le

lemma cyclicAddNet_count {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : (cyclicAddNet a b m).net.count ≤
      s*w*(a.net.count+b.net.count+m.net.count+216*(w+1)^2+142*(w+1)+15) := by
  apply wordBlocks_count
  intro i
  have h := addMod_count (a.comp (blockNet s w i)) (b.comp (blockNet s w i)) m
  simpa only [count_comp,blockNet_count,add_zero] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicPowerCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

lemma cyclicMulBound_mono {s w a b c a' b' c' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    cyclicMulBound s w a b c ≤ cyclicMulBound s w a' b' c' := by
  dsimp [cyclicMulBound]
  gcongr

lemma cyclicNew_count (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    (cyclicNew s w i).net.count ≤ cyclicStepBound s w := by
  let sq := cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b)
  have hs : sq.net.count ≤ cyclicMulBound s w 0 0 0 := cyclicMulNet_count _ _ _
  have hh : (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)).net.count ≤
      cyclicMulBound s w (cyclicMulBound s w 0 0 0) 0 0 :=
    (cyclicMulNet_count sq (cyclicBase s w b) (cyclicMod s w b)).trans
      (cyclicMulBound_mono hs (by rfl) (by rfl))
  simp only [cyclicNew,wordMux_count,cyclicBit,count_bit,zero_add]
  change (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)).net.count +
    sq.net.count + 7*(s*w) ≤ cyclicStepBound s w
  dsimp [cyclicStepBound]
  omega

lemma cyclicStep_count (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    (cyclicStep s w i).net.count ≤ cyclicStepBound s w := by
  simpa only [cyclicStep,count_pair,count_select,zero_add] using cyclicNew_count s w i

lemma cyclicPrefix_count (s w b k : ℕ) [NeZero s] (hk : k ≤ b) :
    (cyclicPrefix s w b k hk).net.count ≤ k*cyclicStepBound s w := by
  induction k with
  | zero => simp [cyclicPrefix]
  | succ k ih =>
    have h := cyclicStep_count s w (⟨k,by omega⟩ : Fin b)
    have hi := ih (by omega)
    simp only [cyclicPrefix,count_comp]
    nlinarith

lemma cyclicPower_count (s w b : ℕ) [NeZero s] :
    (cyclicPower s w b).net.count ≤ s*w*w+b*cyclicStepBound s w := by
  have h₁ := arrayConstant_count (n := (s*w+w)+b) (s := s) (w := w) (fun i => if i=0 then 1 else 0)
  have h₂ := cyclicPrefix_count s w b b le_rfl
  simp only [cyclicPower,count_comp,count_pair,count_select,count_rewire,zero_add]
  change (arrayConstant s w _).net.count + _ ≤ _
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicTestCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

lemma cyclicPowerOn_count {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) :
    (cyclicPowerOn a m e).net.count ≤ a.net.count+m.net.count+e.net.count+
      s*w*w+b*cyclicStepBound s w := by
  have h := cyclicPower_count s w b
  simp only [cyclicPowerOn,count_comp,count_pair]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicTestBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma cyclicAddBound_mono {s w a b c a' b' c' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    cyclicAddBound s w a b c ≤ cyclicAddBound s w a' b' c' := by
  dsimp [cyclicAddBound]
  gcongr

lemma cyclicTest_count (s w a : ℕ) [NeZero s] :
    (cyclicTest s w a).net.count ≤ cyclicTestBound s w := by
  let m : BooleanNetwork w w := select id
  let e : BooleanNetwork w w := select Fin.rev
  let X : BooleanNetwork w (s*w) := cyclicXNet s w
  let C : BooleanNetwork w (s*w) := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  have hx : X.net.count ≤ s*w*w := arrayConstant_count _
  have hc : C.net.count ≤ s*w*w := arrayConstant_count _
  have hm : m.net.count=0 := rfl
  have he : e.net.count=0 := rfl
  have ha : (cyclicAddNet X C m).net.count ≤ cyclicAddBound s w (s*w*w) (s*w*w) 0 :=
    (cyclicAddNet_count X C m).trans (cyclicAddBound_mono hx hc (by rfl))
  have hl := cyclicPowerOn_count (cyclicAddNet X C m) m e
  rw [hm,he] at hl
  have hp : (cyclicPowerOn X m e).net.count ≤ 2*(s*w*w)+w*cyclicStepBound s w := by
    have h := cyclicPowerOn_count X m e
    rw [hm,he] at h
    omega
  have hr : rhs.net.count ≤ cyclicAddBound s w (2*(s*w*w)+w*cyclicStepBound s w) (s*w*w) 0 :=
    (cyclicAddNet_count (cyclicPowerOn X m e) C m).trans
      (cyclicAddBound_mono hp hc (by rfl))
  have hq := wordEq_count (s*w)
  change ((lhs.pair rhs).comp (wordEq (s*w))).net.count ≤ _
  rw [count_comp,count_pair]
  change (cyclicPowerOn (cyclicAddNet X C m) m e).net.count+rhs.net.count+_ ≤ _
  dsimp [cyclicTestBound]
  omega

lemma cyclicStepBound_mono {s w s' w' : ℕ} (hs : s ≤ s') (hw : w ≤ w') :
    cyclicStepBound s w ≤ cyclicStepBound s' w' := by
  unfold cyclicStepBound cyclicMulBound
  gcongr

lemma cyclicTestBound_mono {s w s' w' : ℕ} (hs : s ≤ s') (hw : w ≤ w') :
    cyclicTestBound s w ≤ cyclicTestBound s' w' := by
  unfold cyclicTestBound cyclicAddBound
  gcongr <;> exact cyclicStepBound_mono hs hw

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RootCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma rootNext_count (w k : ℕ) : (rootNext w k).net.count ≤ 87*w+6 := by
  simp only [rootNext,count_comp,count_pair,rootGuess,count_select,wordConstant_count,zero_add]
  have := add_count w
  omega

lemma rootStep_count (w e k : ℕ) : (rootStep w e k).net.count ≤
    230*w+21+e*(90*w*w+14*w+6) := by
  have h₁ := rootNext_count w k
  have h₂ := staticPower_count w e
  have h₃ := wordLe_count ((rootNext w k).comp (staticPower w e)) (rootModulus w)
  simp only [count_comp,rootModulus,count_select] at h₃
  simp only [rootStep,count_pair,rootModulus,count_select,zero_add,rootNew,wordMux_count,
    rootGuess,count_select,add_zero]
  omega

lemma rootPrefix_count (w e k : ℕ) : (rootPrefix w e k).net.count ≤
    k*(230*w+21+e*(90*w*w+14*w+6)) := by
  induction k with
  | zero => simp [rootPrefix]
  | succ k ih =>
    have h := rootStep_count w e k
    rw [rootPrefix,count_comp]
    nlinarith

lemma boundedRootNet_count (n e : ℕ) : (boundedRootNet n e).net.count ≤
    rootWidth n+n*(230*rootWidth n+21+e*(90*rootWidth n*rootWidth n+14*rootWidth n+6)) := by
  have h := rootPrefix_count (rootWidth n) e n
  simp only [boundedRootNet,count_comp,count_pair,count_select,wordConstant_count,
    zero_add,count_rewire]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PerfectPowerCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma rootCheck_count (w e : ℕ) : (rootCheck w e).net.count ≤
    146*w+31+e*(90*w*w+14*w+6) := by
  have h₁ := wordLe_count (wordConstant (n := w+w) (BitVec.ofNat w 2)) (rootGuess w)
  have h₂ := wordEq_count w
  have h₃ := staticPower_count w e
  simp only [rootGuess,count_select,wordConstant_count] at h₁
  simp only [rootCheck,count_band,count_comp,count_pair,rootGuess,rootModulus,count_select,
    zero_add,add_zero]
  omega

lemma exponentCheck_count (n e : ℕ) (he : e ≤ n) : (exponentCheck n e).net.count ≤
    perfectCheckBound n := by
  have h₁ := boundedRootNet_count n e
  have h₂ := rootCheck_count (rootWidth n) e
  have h₃ := Nat.mul_le_mul_right (90*rootWidth n*rootWidth n+14*rootWidth n+6) he
  have h₄ := Nat.mul_le_mul_left n h₃
  simp only [exponentCheck,count_comp,count_pair,count_select,zero_add]
  dsimp [perfectCheckBound]
  nlinarith

lemma perfectExponent_count (n : ℕ) (e : Fin (n+1)) :
    (if 2 ≤ e.val then exponentCheck n e.val else
      (constant false : BooleanNetwork (rootWidth n) 1)).net.count ≤ perfectCheckBound n := by
  by_cases he : 2 ≤ e.val
  · have hh := congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count)
      (ite_eq_left he : (if 2 ≤ e.val then exponentCheck n e.val else constant false)=exponentCheck n e.val)
    exact hh.trans_le (exponentCheck_count n e.val (by omega))
  · have hh := congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count)
      (ite_eq_right he : (if 2 ≤ e.val then exponentCheck n e.val else constant false)=constant false)
    apply hh.trans_le
    change 1 ≤ perfectCheckBound n
    dsimp [perfectCheckBound,rootWidth]
    omega

lemma perfectPowerNet_count (n : ℕ) : (perfectPowerNet n).net.count ≤
    (n+1)*(perfectCheckBound n+4)+1 := by
  have h := any_count (c := perfectCheckBound n)
    (List.ofFn (fun e : Fin (n+1) => if 2 ≤ e.val then exponentCheck n e.val else constant false)) (by
      intro c hc
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hc
      exact perfectExponent_count n e)
  simpa only [perfectPowerNet,List.length_ofFn] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedAKS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

lemma allCongruences_count (s w : ℕ) [NeZero s] :
    (allCongruences s w).net.count ≤ 8*s*(cyclicTestBound s w+1)+1 := by
  simpa only [allCongruences,List.length_ofFn] using
    all_count (List.ofFn (fun i : Fin (8*s) => cyclicTest s w (i.val+1))) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      exact cyclicTest_count s w (i.val+1))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AKSBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma aksBranch_count (n s : ℕ) [NeZero s] :
    (aksBranch n s).net.count ≤ aksBranchBound n s (rootWidth n) := by
  have hd := dividesNet_count (rootWidth n) s
  have ho := orderTests_count (rootWidth n) s (n^2)
  have hs := noSmallDivisor_count (rootWidth n) (8*s)
  have hc := allCongruences_count s (rootWidth n)
  have hmul : (8*s-1)*(216*rootWidth n*rootWidth n+203*rootWidth n+38) ≤
      (8*s)*(216*rootWidth n*rootWidth n+203*rootWidth n+38) := by gcongr; omega
  simp only [aksBranch,count_band,count_bnot]
  dsimp [aksBranchBound]
  omega

lemma aksBranchBound_mono {n s s' w : ℕ} (hs : s ≤ s') :
    aksBranchBound n s w ≤ aksBranchBound n s' w := by
  unfold aksBranchBound
  gcongr
  exact cyclicTestBound_mono hs le_rfl

lemma aksStaticBranch_count (n s : ℕ) (hs : s ≤ n^8) :
    (aksStaticBranch n s).net.count ≤ aksBranchBound n (n^8) (rootWidth n) := by
  by_cases hp : s.Prime
  · let : NeZero s := ⟨hp.ne_zero⟩
    have he : aksStaticBranch n s = aksBranch n s := dite_eq_left hp
    exact (congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count) he).trans_le
      ((aksBranch_count n s).trans (aksBranchBound_mono hs))
  · have he : aksStaticBranch n s = constant false := dite_eq_right hp
    rw [he]
    change 1 ≤ aksBranchBound n (n^8) (rootWidth n)
    unfold aksBranchBound
    omega

/-- Explicit polynomial size for the full exact primality network. -/
theorem primalityNet_count (n : ℕ) : (primalityNet n).net.count ≤ primalityBound n := by
  have hp := perfectPowerNet_count n
  have ha := any_count (c := aksBranchBound n (n^8) (rootWidth n))
    (List.ofFn (fun s : Fin (n^8+1) => aksStaticBranch n s.val)) (by
      intro c hc
      obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hc
      exact aksStaticBranch_count n s.val (by omega))
  simp only [List.length_ofFn] at ha
  simp only [primalityNet,count_band,count_bnot]
  dsimp [primalityBound]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordResize
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma resizeWord_count (u w : ℕ) : (resizeWord u w).net.count≤w := by
  have hh := count_vector_le (c:=1)
    (fun i : Fin w => if h : i.val<u then bit ⟨i.val,h⟩ else constant false) (by
      intro i
      by_cases h : i.val<u
      · have he : (if h : i.val<u then bit (n:=u) ⟨i.val,h⟩ else constant false)=bit ⟨i.val,h⟩ := dite_eq_left h
        exact (congrArg (fun c : BooleanNetwork u 1 => c.net.count) he).trans_le (by simp)
      · have he : (if h : i.val<u then bit (n:=u) ⟨i.val,h⟩ else constant false)=constant false := dite_eq_right h
        exact (congrArg (fun c : BooleanNetwork u 1 => c.net.count) he).trans_le (by simp))
  simpa only [resizeWord,mul_one] using hh

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorVerifier
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

lemma primeWord_count (n : ℕ) : (primeWord n).net.count≤
    49*n+10+rootWidth n+primalityBound n := by
  have h₁ := wordLe_count (wordConstant (n:=n) (BitVec.ofNat n 2)) (select id)
  have h₂ := resizeWord_count n (rootWidth n)
  have h₃ := primalityNet_count n
  rw [wordConstant_count,count_select] at h₁
  simp only [primeWord,count_band,count_comp]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorVerifierBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma zeroWord_count {k n : ℕ} (a : BooleanNetwork k n) :
    (zeroWord a).net.count ≤ a.net.count+97*n+21 := by
  have h := equalOn_count a (wordConstant (n:=k) (BitVec.ofNat n 0))
  rw [wordConstant_count] at h
  dsimp [zeroWord]
  omega

lemma primeOrZero_count {k n : ℕ} (a : BooleanNetwork k n) :
    (primeOrZero a).net.count ≤ 2*a.net.count+146*n+35+rootWidth n+primalityBound n := by
  have h₁ := zeroWord_count a
  have h₂ := primeWord_count n
  simp only [primeOrZero,count_bor,count_comp]
  omega

lemma paddedPair_count {k n : ℕ} (a b : BooleanNetwork k n) :
    (paddedPair a b).net.count ≤ 2*a.net.count+2*b.net.count+242*n+57 := by
  have h₁ := zeroWord_count a
  have h₂ := zeroWord_count b
  have h₃ := wordLe_count a b
  simp only [paddedPair,count_bor,count_band,count_bnot]
  omega

lemma unpadWord_count {k n : ℕ} (a : BooleanNetwork k n) :
    (unpadWord a).net.count ≤ 2*a.net.count+105*n+21 := by
  have h := zeroWord_count a
  simp only [unpadWord,wordMux_count,wordConstant_count]
  omega

lemma productNet_count {k w c : ℕ} (as : List (BooleanNetwork k w))
    (h : ∀ a∈as, a.net.count ≤ c) :
    (productNet as).net.count≤as.length*(c+90*w*w+14*w+6)+w := by
  induction as with
  | nil => simp [productNet,wordConstant_count]
  | cons a as ih =>
    have ha := h a (by simp)
    have hb := ih (fun b hb => h b (by simp [hb]))
    have hm := mul_count w
    simp only [productNet,count_comp,count_pair,List.length_cons]
    nlinarith

lemma candidateProduct_count {k n c : ℕ} (as : Fin n→BooleanNetwork k n)
    (h : ∀ i, (as i).net.count ≤ c) :
    (candidateProduct as).net.count ≤ candidateProductBound n c := by
  have hh := productNet_count (c:=2*c+105*n+21+rootWidth n)
    (List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n)))) (by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      have h₁ := unpadWord_count (as i)
      have h₂ := resizeWord_count n (rootWidth n)
      have h₃ := h i
      simp only [count_comp]
      omega)
  simpa only [candidateProduct,candidateProductBound,List.length_ofFn] using hh

lemma factorVerifierOn_count {k n c : ℕ} (N : BooleanNetwork k n)
    (as : Fin n→BooleanNetwork k n) (hN : N.net.count ≤ c) (ha : ∀ i, (as i).net.count ≤ c) :
    (factorVerifierOn N as).net.count≤factorVerifierBound n c := by
  have h₁ := all_count (c:=2*c+146*n+35+rootWidth n+primalityBound n)
    (List.ofFn (fun i => primeOrZero (as i))) (by
      intro a hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      have := primeOrZero_count (as i)
      have := ha i
      omega)
  have h₂ := all_count (c:=4*c+242*n+57)
    (List.ofFn (fun i : Fin (n*n) =>
      if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
        paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
      else constant true)) (by
      intro a hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      by_cases hij : (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2
      · have he : (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
            else constant true) =
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2) := ite_eq_left hij
        have hc := congrArg (fun d : BooleanNetwork k 1 => d.net.count) he
        have := paddedPair_count (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
        have := ha (finProdFinEquiv.symm i).1
        have := ha (finProdFinEquiv.symm i).2
        omega
      · have he : (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
            else constant true) = (constant (n:=k) true) := ite_eq_right hij
        have hc := congrArg (fun d : BooleanNetwork k 1 => d.net.count) he
        have ht : (constant (n:=k) true).net.count=1 := rfl
        omega)
  have h₃ := equalOn_count (candidateProduct as) (N.comp (resizeWord n (rootWidth n)))
  have h₄ := candidateProduct_count as ha
  have h₅ := resizeWord_count n (rootWidth n)
  simp only [List.length_ofFn] at h₁ h₂
  rw [show 4*c+242*n+57+1 = 4*c+242*n+58 by omega] at h₂
  simp only [count_comp] at h₃
  simp only [factorVerifierOn,count_band]
  dsimp [factorVerifierBound]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanOracle
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace BooleanNetwork

lemma copyPrefix_length {k m : ℕ} (source : Fin m → Fin k) (t : ℕ) (h : t ≤ m) :
    (copyPrefix source t h).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [copyPrefix, ih]

lemma oracle_length {n m : ℕ} (c : BooleanNetwork n m) :
    c.oracle.length ≤ 4*c.net.count + 2*m := by
  unfold oracle
  simp only [List.length_append, List.length_map, List.length_reverse]
  have hp := c.net.compile_length (Nat.le_add_right c.width m)
  have hc := BooleanProgram.compile_length (copyPrefix c.output m le_rfl)
  rw [copyPrefix_length] at hc
  omega

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OracleLayout
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_assign _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_band _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bit _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bnot _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bxor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_constant _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_mux _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_rewire _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_rewire _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma oracleOn_length {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    (oracleOn c hr).length ≤ 4*c.net.count+2*m := by
  simpa [oracleOn] using oracle_length c

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PackedPrograms
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma firstProgram_length {n : ℕ} (m r : ℕ) (ops : List (Instruction n)) :
    (firstProgram m r ops).length = ops.length := by simp [firstProgram]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CoherentSampling
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

lemma sampleProgram_length {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction n)) :
    (sampleProgram c hr ops).length ≤ 4*c.net.count+2*m+ops.length := by
  have h := oracleOn_length c hr
  simp only [sampleProgram,List.length_append,firstProgram_length]
  omega

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhasePreparation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma hadamardPrefix_length (q k : ℕ) (h : k ≤ q) : (hadamardPrefix q k h).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [hadamardPrefix, ih]

lemma preparePhase_length (b : ℕ) (hb : 2 ≤ b) : (preparePhase b hb).length = b+3 := by
  simp [preparePhase, hadamardPrefix_length]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CleanPermutation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.cnotAt_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma swapPrefix_length (n r k : ℕ) (hk : k ≤ n) :
    (swapPrefix n r k hk).length = 3*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [swapPrefix, swapAt, ih (by omega)]; omega

lemma cleanPermutation_length {n r : ℕ} (f g : BooleanNetwork n n)
    (hf : f.net.count ≤ r) (hg : g.net.count ≤ r) :
    (cleanPermutation f g hf hg).length ≤ 4*f.net.count+4*g.net.count+7*n := by
  have h₁ := oracleOn_length f hf
  have h₂ := oracleOn_length g hg
  simp only [cleanPermutation, List.length_append, swapPrefix_length]
  omega

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

lemma rowCircuit_length {b : ℕ} (j : Fin b) :
    (rowCircuit j).length ≤ 998*b+49 := by
  have h := cleanPermutation_length (ControlledTranslation.forward (rowNetwork j))
    (ControlledTranslation.backward (rowNetwork j))
    (translation_count_forward j) (translation_count_backward j)
  have hf := ControlledTranslation.forward_count (rowNetwork j)
  have hg := ControlledTranslation.backward_count (rowNetwork j)
  rw [rowNetwork_count] at hf hg
  change (translation j).length ≤ _ at h
  simp only [rowCircuit, List.length_append, List.length_singleton]
  omega

lemma triPrefix_length (b k : ℕ) (hk : k ≤ b) :
    (triPrefix b k hk).length ≤ k*(998*b+49) := by
  induction k with
  | zero => simp [triPrefix]
  | succ k ih =>
    have hp := ih (by omega)
    have hr := rowCircuit_length (⟨k,by omega⟩ : Fin b)
    simp only [triPrefix, List.length_append]
    nlinarith

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularPreparation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

lemma preparation_length (a : ℕ) : (preparation a).length = a+5 := by
  simp [preparation, preparePhase_length]

lemma transform_length (a : ℕ) :
    (transform a).length ≤ (a+2)*(998*(a+2)+49)+2*(a+5) := by
  have h := triPrefix_length (a+2) (a+2) le_rfl
  simp only [transform, List.length_append, List.length_map, List.length_reverse,
    preparation_length]
  omega

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSampleCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Actual modular-power/triangular-transform order sampler. All arithmetic
inputs are read-only wires; the modular output remains coherent. -/
namespace ExactQuantumFactoring.OrderSample
open scoped BigOperators
open BooleanNetwork Triangular

lemma program_length (w s : ℕ) : (program w s).length ≤
    4*scratch w (s+2)+2*w+(s+2)*(998*(s+2)+49)+2*(s+5) := by
  have hh := sampleProgram_length (powerNetwork w (s+2)) (powerNetwork_count w (s+2))
    (rightProgram (w+w) (Triangular.transform s))
  have ht := Triangular.transform_length s
  have hp := powerNetwork_count w (s+2)
  simp only [rightProgram,List.length_map] at hh
  change (program w s).length ≤ _ at hh
  dsimp [scratch] at ⊢
  omega

end ExactQuantumFactoring.OrderSample


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_InitialOrderState
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

namespace Triangular

lemma uniformPreparation_length (b : ℕ) : (uniformPreparation b).length=b := by
  simp [uniformPreparation,hadamardPrefix_length]

end Triangular
namespace OrderSample

lemma initial_length (w b : ℕ) : (initial w b).length=b := by
  simp [initial,firstProgram_length,rightProgram,Triangular.uniformPreparation_length]

lemma completeSampler_length (w s : ℕ) : (completeSampler w s).length ≤
    (s+2)+4*scratch w (s+2)+2*w+(s+2)*(998*(s+2)+49)+2*(s+5) := by
  have h := program_length w s
  simp only [completeSampler,List.length_append,initial_length]
  omega

end OrderSample
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ParallelPreparation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

lemma parallelProgram_length {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q)) :
    (parallelProgram A B).length=A.length+B.length := by
  simp [parallelProgram,leftProgram,rightProgram]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialRawPreparation
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

namespace OrderTrial

lemma guessProgram_length (n : ℕ) : (guessProgram n).length=3*n+retentionBits n := by
  simp only [guessProgram,parallelProgram_length,hadamardPrefix_length]
  omega

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DyadicCompletion
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

lemma program_length {q : ℕ} (P : List (Instruction q)) (W t d : ℕ) :
    (program P W t d).length=P.length+t+W+coinBits W t d := by
  simp only [program,parallelProgram_length,hadamardPrefix_length]
  omega

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalCompletionOutput
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma rareNet_count (q W t d : ℕ) : (rareNet q W t d).net.count ≤ 97*t+21 := by
  have h := equalOn_count (rareWires q W t d) (wordConstant (BitVec.ofNat t 0))
  apply h.trans
  simp only [rareWires,count_select,wordConstant_count]
  omega

lemma outputNet_count {q W : ℕ} (ordinary : BooleanNetwork q W) (t d : ℕ) :
    (outputNet ordinary t d).net.count ≤ ordinary.net.count+97*t+7*W+21 := by
  rw [outputNet,wordMux_count,count_comp]
  have h := rareNet_count q W t d
  simp only [guessWires,ordinaryWires,count_select] at *
  omega

lemma zeros_count (k m : ℕ) : (zeros k m).net.count=m := by
  simp [zeros]

lemma initialNet_count {k q : ℕ} (ordinary : BooleanNetwork k q) (W t d : ℕ) :
    (initialNet ordinary W t d).net.count=ordinary.net.count+t+W+coinBits W t d := by
  simp only [initialNet,count_pair,zeros_count]
  omega

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_GcdCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma euclidStep_count (w : ℕ) : (euclidStep w).net.count ≤ 216*w*w+300*w+100 := by
  have hc := equalOn_count (rootGuess w) (wordConstant (n:=w+w) (BitVec.ofNat w 0))
  simp only [rootGuess,count_select,wordConstant_count,zero_add] at hc
  have hm := mod_count w
  simp only [euclidStep,count_pair,wordMux_count,rootModulus,rootGuess,count_select,wordConstant_count]
  omega

lemma euclidPrefix_count (w k : ℕ) :
    (euclidPrefix w k).net.count ≤ k*(216*w*w+300*w+100) := by
  induction k with
  | zero => simp [euclidPrefix]
  | succ k ih =>
    rw [euclidPrefix,count_comp]
    have := euclidStep_count w
    rw [Nat.succ_mul]
    omega

lemma gcdNet_count (w : ℕ) : (gcdNet w).net.count ≤ 2*w*(216*w*w+300*w+100) := by
  simpa only [gcdNet,count_comp,rootModulus,count_select,add_zero] using euclidPrefix_count w (2*w)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionCircuit
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

lemma cfProduct_count (w : ℕ) : (cfProduct w).net.count ≤ 90*w*w+100*w+12 := by
  simp only [cfProduct,count_comp,count_pair,cfHead,cfP,cfQ,cfTail,rootModulus,rootGuess,
    count_select,zero_add,add_zero]
  have := mul_count w
  have := add_count w
  omega

lemma cfCombine_count (w : ℕ) : (cfCombine w).net.count ≤ 90*w*w+400*w+100 := by
  have hc := equalOn_count (cfP w) (wordConstant (n:=w+(w+w)) (BitVec.ofNat w 0))
  simp only [cfP,cfTail,rootModulus,count_comp,count_select,wordConstant_count,zero_add] at hc
  have hp := cfProduct_count w
  simp only [cfCombine,count_pair,wordMux_count,cfHead,cfP,cfTail,rootModulus,
    count_comp,count_select,wordConstant_count]
  omega

lemma convergentNet_count (w k : ℕ) :
    (convergentNet w k).net.count ≤ (k+1)*(600*w*w+600*w+120) := by
  induction k with
  | zero =>
    simp only [convergentNet,count_pair,wordConstant_count]
    have := div_count w
    nlinarith
  | succ k ih =>
    simp only [convergentNet,count_comp,count_pair,cfHead,cfTail,rootGuess,count_select]
    have := div_count w
    have := mod_count w
    have := cfCombine_count w
    nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NaturalExpressionCircuit
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

lemma natSubOn_count {k w : ℕ} (a b : BooleanNetwork k w) :
    (natSubOn a b).net.count ≤ 2*a.net.count+2*b.net.count+214*w+15 := by
  have hc := wordLe_count b a
  have hs := sub_count w
  simp only [natSubOn,wordMux_count,count_comp,count_pair,wordConstant_count]
  omega

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LabelRecoveryCircuit
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

lemma pairChoice_count (w : ℕ) : (pairChoice w).net.count ≤ 120*w+31 := by
  have hc := equalOn_count ((rootModulus (w+w)).comp (rootModulus w))
    (wordConstant (n:=(w+w)+(w+w)) (BitVec.ofNat w 0))
  simp only [rootModulus,count_select,count_comp,wordConstant_count,zero_add] at hc
  simp only [pairChoice,wordMux_count,rootGuess,rootModulus,count_select]
  omega

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorPreparation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma tensorWidth_eq (q K : ℕ) : tensorWidth q K=K*q := by
  induction K with
  | zero => simp [tensorWidth]
  | succ K ih => simp [tensorWidth,ih,Nat.add_mul,Nat.add_comm]

lemma tensorProgram_length {q : ℕ} (ops : List (Instruction q)) (K : ℕ) :
    (tensorProgram ops K).length=K*ops.length := by
  induction K with
  | zero => simp [tensorProgram]
  | succ K ih => rw [tensorProgram,parallelProgram_length,ih]; ring

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open Exactness RepeatedTrials OrderTrial
namespace OrderSlots

lemma program_length (n : ℕ) :
    (program n).length ≤ n^5*(2+((sampleExponent n+2)+4*OrderSample.scratch n (sampleExponent n+2)+
      2*n+(sampleExponent n+2)*(998*(sampleExponent n+2)+49)+2*(sampleExponent n+5))+
      3*n+retentionBits n)+2*n+Completion.transitionWidth n+coinWidth n := by
  have hh := OrderSample.completeSampler_length n (sampleExponent n)
  have hr : (rawProgram n (sampleExponent n) n).length ≤
      2+((sampleExponent n+2)+4*OrderSample.scratch n (sampleExponent n+2)+
      2*n+(sampleExponent n+2)*(998*(sampleExponent n+2)+49)+2*(sampleExponent n+5))+
      3*n+retentionBits n := by
    simp only [rawProgram,parallelProgram_length,hadamardPrefix_length,guessProgram_length]
    omega
  unfold program
  rw [Completion.program_length,tensorProgram_length]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ hr) _) _) _

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PreparedOracle
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

lemma preparedOracle_length {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) :
    (preparedOracle c hr ops).length ≤ 4*c.net.count+2*m+ops.length := by
  have hh := oracleOn_length c hr
  simp only [preparedOracle,List.length_append,targetProgram,List.length_map]
  omega

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorWiring
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma tensorNetwork_count {n q K : ℕ} (f : Fin K → BooleanNetwork n q) :
    (tensorNetwork f).net.count=∑ i,(f i).net.count := by
  induction K with
  | zero => simp [tensorNetwork]
  | succ K ih => simp only [tensorNetwork,count_pair,ih,Fin.sum_univ_succ]
lemma tensorNetwork_count_le {n q K c : ℕ} (f : Fin K → BooleanNetwork n q)
    (hf : ∀ i,(f i).net.count ≤ c) : (tensorNetwork f).net.count ≤ K*c := by
  rw [tensorNetwork_count]
  calc
    _ ≤ ∑ _ : Fin K,c := Finset.sum_le_sum (fun i _ => hf i)
    _ = _ := by simp

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderNetworks
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

namespace BooleanNetwork

lemma packNet_count {k n m : ℕ} (r : ℕ) (a : BooleanNetwork k n) (b : BooleanNetwork k m) :
    (packNet r a b).net.count=a.net.count+b.net.count+r := by
  simp only [packNet,count_pair,Completion.zeros_count]

end BooleanNetwork

namespace OrderSlots

lemma samplerZeroNet_count (w b : ℕ) :
    (samplerZeroNet w b).net.count=Triangular.width b+w+OrderSample.scratch w b := by
  simp only [samplerZeroNet,packNet_count,count_pair,count_select,Completion.zeros_count,zero_add]

lemma rawZeroNet_count (n : ℕ) :
    (rawZeroNet n).net.count ≤ OrderTrial.rawWidth n (sampleExponent n) n := by
  simp only [rawZeroNet,count_pair,Completion.zeros_count,samplerZeroNet_count]
  dsimp [OrderTrial.rawWidth,OrderSample.width,OrderSample.inputWidth]
  omega

lemma ordinaryZeroNet_count (n : ℕ) :
    (ordinaryZeroNet n).net.count ≤ n^5*OrderTrial.rawWidth n (sampleExponent n) n :=
  tensorNetwork_count_le _ (fun _=>rawZeroNet_count n)

lemma initialNet_count (n : ℕ) : (initialNet n).net.count ≤
    n^5*OrderTrial.rawWidth n (sampleExponent n) n+2*n+Completion.transitionWidth n+coinWidth n := by
  rw [initialNet,Completion.initialNet_count]
  have h := ordinaryZeroNet_count n
  dsimp only [coinWidth]
  omega

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SamplerDecodeCircuit
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
namespace OrderTrial

lemma samplerSelectedNet_count {k u b : ℕ} (a m : BooleanNetwork k u)
    (z : BooleanNetwork k (OrderSample.width u b)) :
    (samplerSelectedNet a m z).net.count ≤
      3*z.net.count+a.net.count+m.net.count+3*b+Triangular.work b+
        OrderSample.scratch u b+98*OrderSample.width u b+21 := by
  have h := equalOn_count z (packNet (OrderSample.scratch u b)
    ((a.pair m).pair (triangularSelectedNet (z.comp (sampleYNet u b))))
    (z.comp (sampleUNet u b)))
  simp only [packNet_count,count_pair,triangularSelectedNet,Completion.zeros_count,
    count_comp,sampleYNet,sampleUNet,count_select] at h
  dsimp only [samplerSelectedNet,triangularSelectedNet,sampleYNet,sampleUNet]
  omega

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MinimumCandidateCircuit
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

lemma minimumChoice_count (w : ℕ) : (minimumChoice w).net.count≤300*w+60 := by
  have h₁ := equalOn_count (leftNet w w) (wordConstant (n:=w+w) (BitVec.ofNat w 0))
  have h₂ := equalOn_count (rightNet w w) (wordConstant (n:=w+w) (BitVec.ofNat w 0))
  have h₃ := wordLt_count (leftNet w w) (rightNet w w)
  simp only [leftNet,rightNet,count_select,wordConstant_count] at h₁ h₂ h₃
  simp only [minimumChoice,wordMux_count,leftNet,rightNet,count_select]
  omega

lemma minimumNet_count {k w K c : ℕ} (f : Fin K → BooleanNetwork k w)
    (h : ∀ i,(f i).net.count ≤ c) : (minimumNet f).net.count≤w+K*(c+300*w+60) := by
  induction K with
  | zero => simp only [minimumNet,wordConstant_count,zero_mul,add_zero,le_refl]
  | succ K ih =>
    have hh := ih (fun i=>f i.succ) (fun i=>h i.succ)
    have hc := minimumChoice_count w
    rw [minimumNet,count_comp,count_pair]
    have h0 := h 0
    nlinarith

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma powOn_count {k w : ℕ} (a m e : BooleanNetwork k w) :
    (powOn a m e).net.count ≤ a.net.count+m.net.count+e.net.count+
      w+w*(3672*w*w+436*w+36) := by
  have h := modularPower_count w w
  simp only [powOn,count_comp,count_pair,count_rewire]
  omega

lemma stripOn_count {k w c : ℕ} (a m q v : BooleanNetwork k w)
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hq : q.net.count ≤ c) (hv : v.net.count ≤ c) :
    (stripOn a m q v).net.count ≤ stripStepBound w c := by
  have hdiv := div_count w
  have hmod := mod_count w
  have hpow := powOn_count a m ((v.pair q).comp (div w))
  have he0 := equalOn_count ((v.pair q).comp (mod w)) (wordConstant (n:=k) (BitVec.ofNat w 0))
  have he1 := equalOn_count (powOn a m ((v.pair q).comp (div w))) (wordConstant (n:=k) (BitVec.ofNat w 1))
  simp only [count_comp,count_pair,wordConstant_count] at hpow he0 he1
  simp only [stripOn,wordMux_count,count_band,count_comp,count_pair]
  dsimp [stripStepBound]
  nlinarith

lemma stripUpdate_count {k w c : ℕ} (a m q : BooleanNetwork k w)
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hq : q.net.count ≤ c) :
    (stripUpdate a m q).net.count ≤ stripStepBound w c := by
  simp only [stripUpdate,count_pair,count_select,zero_add]
  exact stripOn_count _ _ _ _ (by simpa using ha) (by simpa using hm) (by simpa using hq) (by simp)

lemma stripScan_count {k w c : ℕ} (a m : BooleanNetwork k w) (qs : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hq : ∀ q∈qs,q.net.count ≤ c) :
    (stripScan a m qs).net.count ≤ qs.length*stripStepBound w c := by
  induction qs with
  | nil => simp [stripScan]
  | cons q qs ih =>
    have hh := stripUpdate_count a m q ha hm (hq q (by simp))
    have ht := ih (fun r hr => hq r (by simp [hr]))
    simp only [stripScan,count_comp,List.length_cons]
    nlinarith

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LabelValidationCircuit
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

lemma labelValidNet_count {k w c : ℕ} (n : ℕ) (a m d j : BooleanNetwork k w)
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hd : d.net.count ≤ c) (hj : j.net.count ≤ c) :
    (labelValidNet n a m d j).net.count ≤
      9*c+2*w*(216*w*w+300*w+100)+w+w*(3672*w*w+436*w+36)+344*w+70 := by
  have h0 := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 0)) d
  have hB := wordLt_count d (wordConstant (n:=k) (BitVec.ofNat w (2^n)))
  have hjd := wordLt_count j d
  have hg := equalOn_count ((j.pair d).comp (gcdNet w)) (wordConstant (n:=k) (BitVec.ofNat w 1))
  have hp := equalOn_count (powOn a m d) (wordConstant (n:=k) (BitVec.ofNat w 1))
  have hgc := gcdNet_count w
  have hpow := powOn_count a m d
  simp only [count_comp,count_pair,wordConstant_count] at h0 hB hjd hg hp
  simp only [labelValidNet,count_band]
  omega

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionSharing
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
namespace NatExpr
variable {v : Type*}

lemma compile_shared_count {k w c : ℕ} (vars : v → BooleanNetwork k w)
    (hc : ∀ i, (vars i).net.count ≤ c) (e : NatExpr v) :
    (e.compile vars).net.count ≤ e.sharedCost*(operationBound w+c) := by
  induction e with
  | var i => simpa only [compile,sharedCost,one_mul] using (hc i).trans (Nat.le_add_left c _)
  | const d => simp only [compile,sharedCost,one_mul,wordConstant_count,operationBound]; omega
  | add a b ia ib =>
    have hh := add_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | mul a b ia ib =>
    have hh := mul_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | sub a b ia ib =>
    have hh := natSubOn_count (a.compile vars) (b.compile vars)
    change (natSubOn (a.compile vars) (b.compile vars)).net.count ≤ _
    simp only [sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | div a b ia ib =>
    have hh := div_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | mod a b ia ib =>
    have hh := mod_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | iteLe a b d e ia ib id ie =>
    have hh := wordLe_count (a.compile vars) (b.compile vars)
    simp only [compile,wordMux_count,sharedCost]
    dsimp [operationBound] at *
    nlinarith

lemma template_shared_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.template vars).net.count ≤
      e.sharedCost*(operationBound (e.templateWidth b)+c+e.templateWidth b) := by
  unfold template
  have hh := e.compile_shared_count (fun i => (vars i).comp (resizeWord b (e.templateWidth b)))
    (c:=c+e.templateWidth b) (by
      intro i
      rw [count_comp]
      exact Nat.add_le_add (hc i) (resizeWord_count _ _))
  simpa only [Nat.add_assoc] using hh

end NatExpr
namespace OrderTrial.Expressions
variable {v : Type*}

lemma coveringPow_sharedCost (d : NatExpr v) (n : ℕ) :
    (coveringPow d n).sharedCost=n*(d.sharedCost+3)+1 := by
  induction n with
  | zero => simp [coveringPow,NatExpr.sharedCost]
  | succ n ih => simp only [coveringPow,NatExpr.sharedCost,ih] <;> ring

lemma coveringPow_size (d : NatExpr v) (n : ℕ) :
    (coveringPow d n).size=n*(d.size+3)+1 := by
  induction n with
  | zero => simp [coveringPow,NatExpr.size]
  | succ n ih => simp only [coveringPow,NatExpr.size,ih] <;> ring

end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetentionCircuit
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
namespace NatExpr
variable {v : Type*}
lemma isOne_shared_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.isOne vars).net.count ≤
      e.sharedCost*(operationBound (e.templateWidth b)+c+e.templateWidth b)+
        100*(e.templateWidth b)+21 := by
  have he := e.template_shared_count vars hc
  have hh := equalOn_count (e.template vars) (wordConstant (n:=k) (BitVec.ofNat (e.templateWidth b) 1))
  simp only [wordConstant_count] at hh
  exact hh.trans (by omega)
end NatExpr

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolyBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

namespace PolyBound
lemma const (c : ℕ) : PolyBound (fun _ => c) :=
  ⟨Polynomial.C c, fun _ => by simp⟩
lemma id : PolyBound (fun n => n) := ⟨Polynomial.X, fun _ => by simp⟩
lemma add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n + g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p+q, fun n => by simpa using Nat.add_le_add (hp n) (hq n)⟩
lemma mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n * g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p*q, fun n => by simpa using Nat.mul_le_mul (hp n) (hq n)⟩
lemma pow {f : ℕ → ℕ} (hf : PolyBound f) (k : ℕ) :
    PolyBound (fun n => f n ^ k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k, fun n => by simpa using Nat.pow_le_pow_left (hp n) k⟩
lemma of_le {f g : ℕ → ℕ} (hg : PolyBound g) (h : ∀ n, f n ≤ g n) : PolyBound f := by
  obtain ⟨p,hp⟩ := hg
  exact ⟨p, fun n => (h n).trans (hp n)⟩
lemma max {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩)
lemma sub {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n-g n) :=
  hf.of_le (fun _ => Nat.sub_le _ _)
lemma div {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n/g n) :=
  hf.of_le (fun _ => Nat.div_le_self _ _)
lemma mod {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n%g n) :=
  hf.of_le (fun _ => Nat.mod_le _ _)
lemma ite {f g : ℕ → ℕ} (p : ℕ → Prop) [∀ n, Decidable (p n)]
    (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => if p n then f n else g n) :=
  (hf.max hg).of_le (fun n => by split_ifs <;> omega)

lemma eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

lemma comp {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f (g n)) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  refine ⟨p.comp q, fun n => ?_⟩
  rw [Polynomial.eval_comp]
  exact (hp (g n)).trans (eval_mono p (hq n))

lemma natSize {f : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => (f n).size) :=
  hf.of_le (fun _ => Nat.size_le.mpr (Nat.lt_two_pow_self))
end PolyBound




end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalPowerCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
namespace NatExpr
variable {v : Type*}

lemma pow_size (a : NatExpr v) (k : ℕ) : (a.pow k).size=k*(a.size+1)+1 := by
  induction k with
  | zero=>simp [pow,size]
  | succ k ih=>simp only [pow,size,ih]; ring
lemma pow_sharedCost (a : NatExpr v) (k : ℕ) :
    (a.pow k).sharedCost=k*(a.sharedCost+1)+1 := by
  induction k with
  | zero=>simp [pow,sharedCost]
  | succ k ih=>simp only [pow,sharedCost,ih]; ring
lemma pow_maxConst (a : NatExpr v) (k : ℕ) : (a.pow k).maxConst ≤ Nat.max a.maxConst 1 := by
  induction k with
  | zero=>exact le_max_right _ _
  | succ k ih=>exact max_le ih (le_max_left _ _)

end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionResources
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

lemma nat_size_max (a b : ℕ) : (max a b).size = max a.size b.size := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Nat.size_le_size h)]
  · rw [max_eq_left h, max_eq_left (Nat.size_le_size h)]

namespace NatExpr
variable {v : Type*}

lemma weight_add (a b : NatExpr v) : (add a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_sub (a b : NatExpr v) : (sub a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_mul (a b : NatExpr v) : (mul a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_div (a b : NatExpr v) : (div a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_mod (a b : NatExpr v) : (mod a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_iteLe (a b c d : NatExpr v) :
    (iteLe a b c d).weight ≤ 2*(a.weight+b.weight+c.weight+d.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma size_le_weight (a : NatExpr v) : a.size ≤ a.weight := by dsimp [weight]; omega
lemma sharedCost_le_weight (a : NatExpr v) : a.sharedCost ≤ a.weight := by dsimp [weight]; omega
lemma constSize_le_weight (a : NatExpr v) : a.maxConst.size ≤ a.weight := by dsimp [weight]; omega
lemma weight_pow (a : NatExpr v) (k : ℕ) :
    (a.pow k).weight ≤ (k+1)*(a.weight+3) := by
  have h := Nat.size_le_size (pow_maxConst a k)
  rw [nat_size_max, Nat.size_one] at h
  have h' : (a.pow k).maxConst.size ≤ a.maxConst.size+1 := h.trans (by omega)
  simp only [weight,pow_size,pow_sharedCost]
  nlinarith
lemma templateWidth_le (a : NatExpr v) (b : ℕ) :
    a.templateWidth b ≤ (b+a.weight+1)*a.weight := by
  exact Nat.mul_le_mul (by have := a.constSize_le_weight; omega) a.size_le_weight

end NatExpr

namespace NatExprPoly
variable {v : ℕ → Type*} {a b c d : ∀ n, NatExpr (v n)}
lemma var (i : ∀ n, v n) : NatExprPoly (fun n => .var (i n)) := by
  simpa only [NatExprPoly,NatExpr.weight_var] using PolyBound.const 2
lemma const {f : ℕ → ℕ} (h : PolyBound (fun n => (f n).size)) :
    NatExprPoly (fun n => NatExpr.const (f n) : ∀ n, NatExpr (v n)) := by
  simpa only [NatExprPoly,NatExpr.weight_const] using h.add (PolyBound.const 2)
lemma add (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .add (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_add (a n) (b n))
lemma sub (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .sub (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_sub (a n) (b n))
lemma mul (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .mul (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_mul (a n) (b n))
lemma div (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .div (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_div (a n) (b n))
lemma mod (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .mod (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_mod (a n) (b n))
lemma iteLe (ha : NatExprPoly a) (hb : NatExprPoly b) (hc : NatExprPoly c) (hd : NatExprPoly d) :
    NatExprPoly (fun n => .iteLe (a n) (b n) (c n) (d n)) :=
  ((PolyBound.const 2).mul ((((PolyBound.add ha hb).add hc).add hd).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_iteLe (a n) (b n) (c n) (d n))
lemma pow {f : ℕ → ℕ} (ha : NatExprPoly a) (hf : PolyBound f) :
    NatExprPoly (fun n => (a n).pow (f n)) :=
  ((hf.add (PolyBound.const 1)).mul (PolyBound.add ha (PolyBound.const 3))).of_le
    (fun n => NatExpr.weight_pow (a n) (f n))
end NatExprPoly
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolyAt
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
namespace PolyAt
variable {α : Sort*} {len f g : α→ℕ}
lemma const (len : α→ℕ) (c : ℕ) : PolyAt len (fun _=>c) :=
  ⟨Polynomial.C c,fun _=>by simp⟩
lemma self (len : α→ℕ) : PolyAt len len := ⟨Polynomial.X,fun _=>by simp⟩
lemma add (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a+g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p+q,fun a=>by simpa using Nat.add_le_add (hp a) (hq a)⟩
lemma mul (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a*g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p*q,fun a=>by simpa using Nat.mul_le_mul (hp a) (hq a)⟩
lemma pow (hf : PolyAt len f) (k : ℕ) : PolyAt len (fun a=>f a^k) := by
  obtain ⟨p,hp⟩:=hf
  exact ⟨p^k,fun a=>by simpa using Nat.pow_le_pow_left (hp a) k⟩
lemma of_le (hg : PolyAt len g) (h : ∀a,f a≤g a) : PolyAt len f := by
  obtain ⟨p,hp⟩:=hg
  exact ⟨p,fun a=>(h a).trans (hp a)⟩
lemma sub (hf : PolyAt len f) : PolyAt len (fun a=>f a-g a) := hf.of_le fun _=>Nat.sub_le _ _
lemma div (hf : PolyAt len f) : PolyAt len (fun a=>f a/g a) := hf.of_le fun _=>Nat.div_le_self _ _
lemma mod (hf : PolyAt len f) : PolyAt len (fun a=>f a%g a) := hf.of_le fun _=>Nat.mod_le _ _
lemma max (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>max (f a) (g a)) :=
  (hf.add hg).of_le fun _=>Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩
lemma pull {β : Sort*} (hf : PolyAt len f) (g : β→α) :
    PolyAt (fun b=>len (g b)) (fun b=>f (g b)) := by
  obtain ⟨p,hp⟩:=hf; exact ⟨p,fun b=>hp (g b)⟩
lemma ofPoly {f : ℕ→ℕ} (hf : PolyBound f) (len : α→ℕ) :
    PolyAt len (fun a=>f (len a)) := PolyAt.pull hf len
lemma comp {h : ℕ→ℕ} (hh : PolyBound h) (hf : PolyAt len f) :
    PolyAt len (fun a=>h (f a)) := by
  obtain ⟨p,hp⟩:=hh; obtain ⟨q,hq⟩:=hf
  refine ⟨p.comp q,fun a=>?_⟩
  simpa only [Polynomial.eval_comp] using
    (hp (f a)).trans (PolyBound.eval_mono p (hq a))
lemma natSize (hf : PolyAt len f) : PolyAt len (fun a=>(f a).size) :=
  hf.of_le fun _=>Nat.size_le.mpr Nat.lt_two_pow_self
end PolyAt

end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace NetworkAt
variable {α : Type*} {len a b c : α→ℕ}
lemma select (h : ∀x,Fin (b x)→Fin (a x)) : NetworkAt len (fun x=>BooleanNetwork.select (h x)) := by
  simpa only [NetworkAt,count_select] using PolyAt.const len 0
lemma comp {f : ∀x,BooleanNetwork (a x) (b x)} {g : ∀x,BooleanNetwork (b x) (c x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) : NetworkAt len (fun x=>(f x).comp (g x)) := by
  simpa only [NetworkAt,count_comp] using PolyAt.add hf hg
lemma pair {f : ∀x,BooleanNetwork (a x) (b x)} {g : ∀x,BooleanNetwork (a x) (c x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) : NetworkAt len (fun x=>(f x).pair (g x)) := by
  simpa only [NetworkAt,count_pair] using PolyAt.add hf hg
lemma rewire {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f)
    (h : ∀x,Fin (c x)→Fin (b x)) : NetworkAt len (fun x=>(f x).rewire (h x)) := by
  simpa only [NetworkAt,count_rewire] using hf
lemma constant (h : α→Bool) : NetworkAt len (fun x=>BooleanNetwork.constant (n:=a x) (h x)) := by
  simpa only [NetworkAt,count_constant] using PolyAt.const len 1
lemma of_le {f : ∀x,BooleanNetwork (a x) (b x)} {bound : α→ℕ} (hb : PolyAt len bound)
    (h : ∀x,(f x).net.count≤bound x) : NetworkAt len f := hb.of_le h
lemma bnot {f : ∀x,BooleanNetwork (a x) 1} (hf : NetworkAt len f) :
    NetworkAt len (fun x=>(f x).bnot) := by
  simpa only [NetworkAt,count_bnot] using PolyAt.add hf (PolyAt.const len 1)
lemma band {f g : ∀x,BooleanNetwork (a x) 1} (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>(f x).band (g x)) := by
  simpa only [NetworkAt,count_band] using (PolyAt.add hf hg).add (PolyAt.const len 1)
lemma bor {f g : ∀x,BooleanNetwork (a x) 1} (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>(f x).bor (g x)) := by
  simpa only [NetworkAt,count_bor] using (PolyAt.add hf hg).add (PolyAt.const len 4)
lemma wordConstant (v : ∀x,BitVec (b x)) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordConstant (n:=a x) (v x)) := by
  simpa only [NetworkAt,wordConstant_count] using hb
lemma zeroWord {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.zeroWord (f x)) :=
  of_le ((PolyAt.add hf ((PolyAt.const len 97).mul hb)).add (PolyAt.const len 21))
    fun x=>zeroWord_count (f x)
lemma equalOn {f g : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f)
    (hg : NetworkAt len g) (hb : PolyAt len b) : NetworkAt len (fun x=>BitArithmetic.equalOn (f x) (g x)) :=
  of_le (((PolyAt.add hf hg).add ((PolyAt.const len 96).mul hb)).add (PolyAt.const len 21))
    fun x=>equalOn_count (f x) (g x)
lemma resizeWord (ha : PolyAt len a) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.resizeWord (a x) (b x)) := by
  apply of_le (PolyAt.add ha hb)
  intro x
  have h:=BitArithmetic.resizeWord_count (a x) (b x)
  omega
lemma all {ls : ∀x,List (BooleanNetwork (a x) 1)} (hl : PolyAt len (fun x=>(ls x).length))
    (h : ∃p : Polynomial ℕ,∀ x f, f∈ls x → f.net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>BooleanNetwork.all (ls x)) := by
  obtain ⟨p,hp⟩:=h
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  exact of_le ((hl.mul (hc.add (PolyAt.const len 1))).add (PolyAt.const len 1))
    fun x=>all_count (ls x) (hp x)
lemma all_ofFn {k : α→ℕ} {f : ∀x,Fin (k x)→BooleanNetwork (a x) 1} (hk : PolyAt len k)
    (hf : NetworkAt (fun xi : Σx,Fin (k x)=>len xi.1) (fun xi=>f xi.1 xi.2)) :
    NetworkAt len (fun x=>BooleanNetwork.all (List.ofFn (f x))) := by
  obtain ⟨p,hp⟩:=hf
  apply all (by simpa only [List.length_ofFn] using hk)
  refine ⟨p,?_⟩
  intro x g hg
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hg
  exact hp ⟨x,i⟩
lemma pull {β : Type*} {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (g : β→α) :
    NetworkAt (fun y=>len (g y)) (fun y=>f (g y)) := PolyAt.pull hf g
lemma ofPoly {a b : ℕ→ℕ} {f : ∀n,BooleanNetwork (a n) (b n)} (hf : NetworkPoly f)
    (len : α→ℕ) : NetworkAt len (fun x=>f (len x)) := PolyAt.ofPoly hf len
end NetworkAt
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork

namespace NatExprAt
variable {α : Type*} {len a b : α→ℕ} {v : α→Type*} {e : ∀x,NatExpr (v x)}
lemma ofPoly {v : ℕ→Type*} {e : ∀n,NatExpr (v n)} (he : NatExprPoly e) (len : α→ℕ) :
    NatExprAt len (fun x=>e (len x)) := PolyAt.ofPoly he len
lemma sharedCost (he : NatExprAt len e) : PolyAt len (fun x=>(e x).sharedCost) :=
  PolyAt.of_le he fun x=>(e x).sharedCost_le_weight
lemma templateWidth (he : NatExprAt len e) (hb : PolyAt len b) :
    PolyAt len (fun x=>(e x).templateWidth (b x)) :=
  PolyAt.of_le (((hb.add he).add (PolyAt.const len 1)).mul he)
    fun x=>(e x).templateWidth_le (b x)
lemma operationBound {f : α→ℕ} (hf : PolyAt len f) :
    PolyAt len (fun x=>NatExpr.operationBound (f x)) := by
  unfold NatExpr.operationBound
  repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
lemma isOne {vars : ∀x,v x→BooleanNetwork (a x) (b x)}
    (he : NatExprAt len e) (hb : PolyAt len b)
    (hv : ∃p : Polynomial ℕ,∀x i,(vars x i).net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>(e x).isOne (vars x)) := by
  obtain ⟨p,hp⟩:=hv
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  have hw:=he.templateWidth hb
  apply NetworkAt.of_le
    (((he.sharedCost.mul (((operationBound hw).add hc).add hw)).add
      ((PolyAt.const len 100).mul hw)).add (PolyAt.const len 21))
  exact fun x=>(e x).isOne_shared_count (vars x) (hp x)
end NatExprAt
end ExactQuantumFactoring

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkAtArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a b c d : α→ℕ}
lemma wordMux {s : ∀x,BooleanNetwork (a x) 1} {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hs : NetworkAt len s) (hf : NetworkAt len f) (hg : NetworkAt len g) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordMux (s x) (f x) (g x)) := by
  simpa only [NetworkAt,wordMux_count] using ((hs.add hf).add hg).add ((PolyAt.const len 7).mul hb)
lemma wordLt {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordLt (f x) (g x)) :=
  of_le (((hf.add hg).add ((PolyAt.const len 48).mul hb)).add (PolyAt.const len 8))
    fun x=>wordLt_count (f x) (g x)
lemma wordLe {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordLe (f x) (g x)) := (hg.wordLt hf hb).bnot
lemma toWidth {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f)
    (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>OrderTrial.toWidth (c x) (f x)) :=
  hf.comp (resizeWord hb hc)
lemma modularPower (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>BitArithmetic.modularPower (b x) (c x)) := by
  apply of_le (bound:=fun x=>b x+c x*(3672*b x*b x+436*b x+36))
  · exact hb.add (hc.mul (((PolyAt.const len 3672).mul hb |>.mul hb).add
      ((PolyAt.const len 436).mul hb) |>.add (PolyAt.const len 36)))
  · exact fun x=>modularPower_count (b x) (c x)
lemma gcdNet (hb : PolyAt len b) : NetworkAt len (fun x=>BitArithmetic.gcdNet (b x)) := by
  apply of_le (bound:=fun x=>2*b x*(216*b x*b x+300*b x+100))
  · exact ((PolyAt.const len 2).mul hb).mul
      ((((PolyAt.const len 216).mul hb).mul hb).add ((PolyAt.const len 300).mul hb) |>.add
        (PolyAt.const len 100))
  · exact fun x=>gcdNet_count (b x)
lemma convergentNet (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>BitArithmetic.convergentNet (b x) (c x)) := by
  apply of_le (bound:=fun x=>(c x+1)*(600*b x*b x+600*b x+120))
  · exact (hc.add (PolyAt.const len 1)).mul
      ((((PolyAt.const len 600).mul hb).mul hb).add ((PolyAt.const len 600).mul hb) |>.add
        (PolyAt.const len 120))
  · exact fun x=>convergentNet_count (b x) (c x)
lemma boundedRootNet (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>BitArithmetic.boundedRootNet (b x) (c x)) := by
  have hr : PolyAt len (fun x=>rootWidth (b x)) := by
    unfold rootWidth; repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  apply of_le (bound:=fun x=>rootWidth (b x)+b x*(230*rootWidth (b x)+21+
      c x*(90*rootWidth (b x)*rootWidth (b x)+14*rootWidth (b x)+6)))
  · exact hr.add (hb.mul (((PolyAt.const len 230).mul hr |>.add (PolyAt.const len 21)).add
      (hc.mul ((((PolyAt.const len 90).mul hr).mul hr).add ((PolyAt.const len 14).mul hr) |>.add
        (PolyAt.const len 6)))))
  · exact fun x=>boundedRootNet_count (b x) (c x)
end NetworkAt
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RecoveryPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a b : α→ℕ}
lemma varsFin {ι : Type*} [Fintype ι] {v : ∀x,ι→BooleanNetwork (a x) (b x)}
    (h : ∀i,NetworkAt len (fun x=>v x i)) :
    ∃p : Polynomial ℕ,∀x i,(v x i).net.count≤p.eval (len x) := by
  classical
  change ∀i,∃p : Polynomial ℕ,∀x,(v x i).net.count≤p.eval (len x) at h
  choose p hp using h
  refine ⟨∑i,p i,fun x i=>?_⟩
  rw [Polynomial.eval_finsetSum]
  exact (hp i x).trans (Finset.single_le_sum (f:=fun j=>(p j).eval (len x)) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i))
end NetworkAt
namespace OrderTrial
variable {α : Type*} {len a w steps : α→ℕ}
lemma checkedConvergent_poly {Q B k : ∀x,BooleanNetwork (a x) (w x)}
    (hQ : NetworkAt len Q) (hB : NetworkAt len B) (hk : NetworkAt len k)
    (hw : PolyAt len w) (hi : PolyAt len steps) :
    NetworkAt len (fun x=>checkedConvergent (steps x) (Q x) (B x) (k x)) := by
  let cv := fun x=>(k x |>.pair (Q x)).comp (convergentNet (w x) (steps x))
  have hcv : NetworkAt len cv := (hk.pair hQ).comp (NetworkAt.convergentNet hw hi)
  have hd : NetworkAt len (fun x=>(cv x).comp (rootGuess (w x))) :=
    hcv.comp (NetworkAt.select _)
  have hj : NetworkAt len (fun x=>(cv x).comp (rootModulus (w x))) :=
    hcv.comp (NetworkAt.select _)
  have hv : ∃p : Polynomial ℕ,∀x i,
      (![Q x,B x,k x,(cv x).comp (rootGuess (w x)),(cv x).comp (rootModulus (w x))] i).net.count
        ≤p.eval (len x) := by
    apply NetworkAt.varsFin
    intro i; fin_cases i
    · exact hQ
    · exact hB
    · exact hk
    · exact hd
    · exact hj
  have he : NatExprAt len (fun _ : α=>binCheckExpr) := PolyAt.const len binCheckExpr.weight
  have hp := he.isOne hw hv
  have hz := NetworkAt.wordConstant (a:=a) (fun x=>BitVec.ofNat (w x) 0) hw
  exact (hp.wordMux hd hz hw).pair (hp.wordMux hj hz hw)

lemma recoveryNet_count_of_bound {n w K c : ℕ} (Q B k : BooleanNetwork n w)
    (hc : ∀i,i<K → (checkedConvergent i Q B k).net.count ≤ c) :
    (recoveryNet Q B k K).net.count≤2*w+K*(c+120*w+31) := by
  induction K with
  | zero => simp only [recoveryNet,count_pair,wordConstant_count,zero_mul,add_zero];omega
  | succ K ih =>
    have hh := ih (fun i hi=>hc i (by omega))
    have hi := hc K (by omega)
    have hp := pairChoice_count w
    simp only [recoveryNet,count_pair,count_comp]
    nlinarith

lemma recoveryNet_poly {Q B k : ∀x,BooleanNetwork (a x) (w x)}
    (hQ : NetworkAt len Q) (hB : NetworkAt len B) (hk : NetworkAt len k)
    (hw : PolyAt len w) (hsteps : PolyAt len steps) :
    NetworkAt len (fun x=>recoveryNet (Q x) (B x) (k x) (steps x)) := by
  let index : Type _ := Σx:α,Fin (steps x)
  let param : index→α := Sigma.fst
  have hi : PolyAt (fun z:index=>len z.1) (fun z=>z.2.val) :=
    (hsteps.pull param).of_le fun z=>z.2.isLt.le
  have hh:=checkedConvergent_poly (hQ.pull param) (hB.pull param) (hk.pull param)
    (hw.pull param) hi
  obtain ⟨p,hp⟩:=hh
  have hpoly : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply NetworkAt.of_le (bound:=fun x=>2*w x+steps x*(p.eval (len x)+120*w x+31))
  · exact ((PolyAt.const len 2).mul hw).add
      (hsteps.mul ((hpoly.add ((PolyAt.const len 120).mul hw)).add (PolyAt.const len 31)))
  · intro x
    exact recoveryNet_count_of_bound (Q x) (B x) (k x) (fun i hi=>hp ⟨x,⟨i,hi⟩⟩)
end OrderTrial
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AdaptivePrepared
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

lemma appendPrepared_length {p q r : ℕ} (A : List (Instruction p)) (c : BooleanNetwork p q)
    (hc : c.net.count ≤ r) (ops : List (Instruction q)) :
    (appendPrepared A c hc ops).length ≤ A.length+4*c.net.count+2*q+ops.length := by
  have h := preparedOracle_length c hc ops
  simp only [appendPrepared,List.length_append,firstProgram_length]
  omega

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhaseOracle
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

namespace BooleanNetwork

lemma phaseOracle_length {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r) :
    (phaseOracle c hr).length ≤ 8*c.net.count+6 := by
  have h := oracleOn_length c hr
  simp only [phaseOracle, List.length_append, List.length_cons, List.length_nil]
  omega

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalAmplification
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

lemma amplificationProgram_length {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r) :
    (amplificationProgram ops good zero hg hz).length ≤
      3*ops.length+8*good.net.count+8*zero.net.count+12 := by
  have h₁ := phaseOracle_length good hg
  have h₂ := phaseOracle_length zero hz
  simp only [amplificationProgram,List.length_append,firstProgram_length,
    List.length_map,List.length_reverse]
  omega

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MaskedPreparation
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

lemma maskedPrefix_length (n k : ℕ) (h : k ≤ n) : (maskedPrefix n k h).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [maskedPrefix,List.length_append,List.length_singleton,ih]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListSamplerCircuit
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


namespace ExactQuantumFactoring.ListSampler
open Exactness BitArithmetic BooleanNetwork

lemma circuit_length (n : ℕ) : (circuit n).length ≤ 4*work n+3*n := by
  have h := oracleOn_length (listMaskNet n) (show (listMaskNet n).net.count ≤ n+work n from
    (listMaskNet_count n).trans (Nat.le_add_left _ _))
  have hc : (listMaskNet n).net.count ≤ work n := listMaskNet_count n
  simp only [circuit,List.length_append,List.length_map,maskedPrefix_length]
  omega

end ExactQuantumFactoring.ListSampler


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListSlots
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

lemma program_length (n : ℕ) : (program n).length ≤
    n^5*(4*ListSampler.work n+3*n)+2*n+Completion.transitionWidth n+
      Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5) := by
  rw [program,Completion.program_length,ordinaryProgram,tensorProgram_length]
  have hh := Nat.mul_le_mul_left (n^5) (ListSampler.circuit_length n)
  omega

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionNetworks
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

lemma encodeNet_count {k n K c : ℕ} (f : Fin K → BooleanNetwork k n)
    (hf : ∀ i,(f i).net.count ≤ c) : (encodeNet f).net.count ≤ n*(K+1)*(c+1) := by
  apply count_vector_le
  intro i
  dsimp only
  split_ifs with h
  · rw [dite_eq_left h,count_rewire]
    exact (hf _).trans (Nat.le_add_right _ _)
  · rw [dite_eq_right h]
    change 1 ≤ c+1
    omega

end TransitionWords
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListNetworks
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

lemma ordinaryNet_count (n : ℕ) : (ordinaryNet n).net.count ≤ Completion.transitionWidth n := by
  have h := TransitionWords.encodeNet_count
    (fun i : Fin (n^5) => (tensorSelect (ListSampler.width n) (n^5) i).comp (sampleNet n))
    (c:=0) (by intro i; simp only [count_comp,tensorSelect,sampleNet,count_select]; omega)
  change (TransitionWords.encodeNet (fun i : Fin (n^5) =>
    (tensorSelect (ListSampler.width n) (n^5) i).comp (sampleNet n))).net.count ≤ n*(n^5+1)
  simpa only [Nat.zero_add,Nat.mul_one] using h

lemma outputNet_count (n : ℕ) : (outputNet n).net.count ≤
    8*Completion.transitionWidth n+194*n+21 := by
  have h := Completion.outputNet_count (ordinaryNet n) (2*n) (n*n^5)
  have hh := ordinaryNet_count n
  change (Completion.outputNet _ _ _).net.count ≤ _
  nlinarith

lemma singleZeroNet_count (n : ℕ) : (singleZeroNet n).net.count ≤ ListSampler.width n := by
  unfold singleZeroNet
  apply (count_vector_le _ (c:=1) ?_).trans (by omega)
  intro i
  by_cases h : i.val<n
  · rw [dite_eq_left h,count_bit]; omega
  · rw [dite_eq_right h,count_constant]

lemma ordinaryZeroNet_count (n : ℕ) : (ordinaryZeroNet n).net.count ≤ n^5*ListSampler.width n :=
  tensorNetwork_count_le _ (fun _ => singleZeroNet_count n)

lemma initialNet_count (n : ℕ) : (initialNet n).net.count ≤ n^5*ListSampler.width n+
    2*n+Completion.transitionWidth n+Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5) := by
  rw [initialNet,Completion.initialNet_count]
  have h := ordinaryZeroNet_count n
  omega

lemma launch_length (n : ℕ) : (launch n).length ≤
    4*work n+2*width n+(program n).length := preparedOracle_length _ _ _

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplit
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

lemma baseNet_count {n : ℕ} (i : Fin (n^5)) :
    (baseNet i).net.count=(PhysicalListSlots.outputNet n).net.count := by
  simp only [baseNet,count_rewire,count_comp,listWires,count_select,zero_add]

lemma orderInitialNet_count {n : ℕ} (i : Fin (n^5)) :
    (orderInitialNet i).net.count=(PhysicalListSlots.outputNet n).net.count+(OrderSlots.initialNet n).net.count := by
  simp only [orderInitialNet,count_comp,count_pair,baseNet_count,modulusWires,count_select,add_zero]

lemma ordersInitialNet_count (n : ℕ) : (ordersInitialNet n).net.count=
    n^5*((PhysicalListSlots.outputNet n).net.count+(OrderSlots.initialNet n).net.count) := by
  rw [ordersInitialNet,tensorNetwork_count]
  simp only [orderInitialNet_count,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

lemma program_length (n : ℕ) : (program n).length ≤
    (PhysicalListSlots.launch n).length+4*work n+2*ordersWidth n+n^5*(OrderSlots.program n).length := by
  have h := appendPrepared_length (PhysicalListSlots.launch n) (ordersInitialNet n) le_rfl (ordersProgram n)
  simpa only [program,work,ordersProgram,tensorProgram_length] using h

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplitLaunch
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

namespace FixedSplit

lemma initialNet_count (n : ℕ) : (initialNet n).net.count=
    PhysicalListSlots.width n+PhysicalListSlots.work n+ordersWidth n+work n := by
  simp only [initialNet,packNet_count,count_select,Completion.zeros_count,zero_add]

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PreparationPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PreparationPolynomial

lemma sampleExponent : PolyBound OrderSlots.sampleExponent := by
  unfold OrderSlots.sampleExponent; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma retentionBits : PolyBound OrderTrial.retentionBits := by
  unfold OrderTrial.retentionBits; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma transitionWidth : PolyBound Completion.transitionWidth := by
  unfold Completion.transitionWidth; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma samplerWork : PolyBound ListSampler.work := by
  unfold ListSampler.work; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma samplerWidth : PolyBound ListSampler.width := by
  change PolyBound (fun n=>n+n+(n+ListSampler.work n))
  have := samplerWork; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma sampleScratch : PolyBound (fun n=>OrderSample.scratch n (OrderSlots.sampleExponent n+2)) := by
  unfold OrderSample.scratch
  have := sampleExponent; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma sampleWidth : PolyBound (fun n=>OrderSample.width n (OrderSlots.sampleExponent n+2)) := by
  unfold OrderSample.width OrderSample.inputWidth
  have := sampleExponent; have := sampleScratch; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma rawWidth : PolyBound (fun n=>OrderTrial.rawWidth n (OrderSlots.sampleExponent n) n) := by
  unfold OrderTrial.rawWidth OrderTrial.guessWidth
  have := sampleWidth; have := retentionBits; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma listCoin : PolyBound (fun n=>Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5)) := by
  unfold Completion.coinBits
  have := transitionWidth; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma orderCoin : PolyBound OrderSlots.coinWidth := by
  unfold OrderSlots.coinWidth Completion.coinBits
  have := transitionWidth; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma listWidth : PolyBound PhysicalListSlots.width := by
  unfold PhysicalListSlots.width PhysicalListSlots.ordinaryWidth
  simp only [tensorWidth_eq]
  have := samplerWidth; have := transitionWidth; have := listCoin; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma orderWidth : PolyBound OrderSlots.width := by
  unfold OrderSlots.width OrderSlots.ordinaryWidth
  simp only [tensorWidth_eq]
  have := rawWidth; have := transitionWidth; have := orderCoin; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma listOutput : PolyBound (fun n=>(PhysicalListSlots.outputNet n).net.count) := by
  apply PolyBound.of_le (g:=fun n=>8*Completion.transitionWidth n+194*n+21)
  · have := transitionWidth; repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · exact PhysicalListSlots.outputNet_count
lemma listWork : PolyBound PhysicalListSlots.work := by
  apply PolyBound.of_le (g:=fun n=>n^5*ListSampler.width n+2*n+Completion.transitionWidth n+
      Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5))
  · have := samplerWidth;have := transitionWidth;have:=listCoin;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · exact PhysicalListSlots.initialNet_count
lemma orderWork : PolyBound (fun n=>(OrderSlots.initialNet n).net.count) := by
  apply PolyBound.of_le (g:=fun n=>n^5*OrderTrial.rawWidth n (OrderSlots.sampleExponent n) n+
      2*n+Completion.transitionWidth n+OrderSlots.coinWidth n)
  · have := rawWidth;have:=transitionWidth;have:=orderCoin;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · exact OrderSlots.initialNet_count
lemma listSteps : PolyBound (fun n=>(PhysicalListSlots.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>n^5*(4*ListSampler.work n+3*n)+2*n+Completion.transitionWidth n+
      Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5))
  · have:=samplerWork;have:=transitionWidth;have:=listCoin;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · exact PhysicalListSlots.program_length
lemma orderSteps : PolyBound (fun n=>(OrderSlots.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>n^5*(2+((OrderSlots.sampleExponent n+2)+
      4*OrderSample.scratch n (OrderSlots.sampleExponent n+2)+2*n+
      (OrderSlots.sampleExponent n+2)*(998*(OrderSlots.sampleExponent n+2)+49)+
      2*(OrderSlots.sampleExponent n+5))+3*n+OrderTrial.retentionBits n)+2*n+
      Completion.transitionWidth n+OrderSlots.coinWidth n)
  · have:=sampleExponent;have:=sampleScratch;have:=retentionBits
    have:=transitionWidth;have:=orderCoin;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · exact OrderSlots.program_length
lemma listLaunchWidth : PolyBound PhysicalListSlots.launchWidth := by
  unfold PhysicalListSlots.launchWidth
  have:=listWidth;have:=listWork;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma listLaunchSteps : PolyBound (fun n=>(PhysicalListSlots.launch n).length) := by
  apply PolyBound.of_le (g:=fun n=>4*PhysicalListSlots.work n+2*PhysicalListSlots.width n+
      (PhysicalListSlots.program n).length)
  · have:=listWork;have:=listWidth;have:=listSteps;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · exact PhysicalListSlots.launch_length
lemma splitWork : PolyBound FixedSplit.work := by
  change PolyBound (fun n=>(FixedSplit.ordersInitialNet n).net.count)
  simp only [FixedSplit.ordersInitialNet_count]
  have:=listOutput;have:=orderWork;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma ordersWidth : PolyBound FixedSplit.ordersWidth := by
  unfold FixedSplit.ordersWidth
  simp only [tensorWidth_eq]
  have:=orderWidth;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma splitWidth : PolyBound FixedSplit.width := by
  unfold FixedSplit.width
  have:=listLaunchWidth;have:=ordersWidth;have:=splitWork;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma splitSteps : PolyBound (fun n=>(FixedSplit.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>(PhysicalListSlots.launch n).length+4*FixedSplit.work n+
      2*FixedSplit.ordersWidth n+n^5*(OrderSlots.program n).length)
  · have:=listLaunchSteps;have:=splitWork;have:=ordersWidth;have:=orderSteps;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · exact FixedSplit.program_length
lemma splitInitial : PolyBound (fun n=>(FixedSplit.initialNet n).net.count) := by
  simp only [FixedSplit.initialNet_count]
  have:=listWidth;have:=listWork;have:=ordersWidth;have:=splitWork;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)

end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalExpressionResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

namespace PolyBound
lemma twoPowSize {f : ℕ → ℕ} (hf : PolyBound f) :
    PolyBound (fun n => (2^(f n)).size) := by
  simpa only [Nat.size_pow] using hf.add (PolyBound.const 1)
end PolyBound

namespace NatExprPoly
variable {v : ℕ → Type*}
lemma ite (p : ℕ → Prop) [∀ n, Decidable (p n)] {a b : ∀ n, NatExpr (v n)}
    (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => if p n then a n else b n) := by
  change PolyBound _
  convert PolyBound.ite p ha hb using 1
  all_goals try with_reducible_and_instances rfl
  funext n; dsimp only; split_ifs <;> rfl
lemma constPoly {f : ℕ → ℕ} (hf : PolyBound f) :
    NatExprPoly (fun n => NatExpr.const (f n) : ∀ n, NatExpr (v n)) := const hf.natSize
end NatExprPoly

namespace IntExprPoly
variable {v : ℕ → Type*} {a b c d : ∀ n, IntExpr (v n)}
lemma ofNat {f : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) :
    IntExprPoly (fun n => IntExpr.ofNat (f n)) :=
  ⟨hf, NatExprPoly.constPoly (PolyBound.const 0)⟩
lemma ofInt {f : ℕ → ℤ} (hf : PolyBound (fun n => (f n).natAbs.size)) :
    IntExprPoly (fun n => IntExpr.ofInt (f n) : ∀ n, IntExpr (v n)) := by
  constructor <;> apply NatExprPoly.const
  · exact hf.of_le (fun n => Nat.size_le_size (by omega))
  · exact hf.of_le (fun n => Nat.size_le_size (by omega))
lemma negation (ha : IntExprPoly a) : IntExprPoly (fun n => (a n).negation) := ⟨ha.2,ha.1⟩
lemma add (ha : IntExprPoly a) (hb : IntExprPoly b) : IntExprPoly (fun n => (a n).add (b n)) :=
  ⟨ha.1.add hb.1,ha.2.add hb.2⟩
lemma sub (ha : IntExprPoly a) (hb : IntExprPoly b) : IntExprPoly (fun n => (a n).sub (b n)) :=
  ha.add hb.negation
lemma mul (ha : IntExprPoly a) (hb : IntExprPoly b) : IntExprPoly (fun n => (a n).mul (b n)) :=
  ⟨(ha.1.mul hb.1).add (ha.2.mul hb.2),(ha.2.mul hb.1).add (ha.1.mul hb.2)⟩
lemma scale {f : ∀ n, NatExpr (v n)} (ha : IntExprPoly a) (hf : NatExprPoly f) :
    IntExprPoly (fun n => (a n).scale (f n)) := ha.mul (ofNat hf)
lemma toNat (ha : IntExprPoly a) : NatExprPoly (fun n => (a n).toNat) := ha.1.sub ha.2
lemma natAbs (ha : IntExprPoly a) : NatExprPoly (fun n => (a n).natAbs) :=
  (ha.1.sub ha.2).add (ha.2.sub ha.1)
lemma iteLe {f g : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) (hg : NatExprPoly g)
    (hc : IntExprPoly c) (hd : IntExprPoly d) :
    IntExprPoly (fun n => IntExpr.iteLe (f n) (g n) (c n) (d n)) :=
  ⟨hf.iteLe hg hc.1 hd.1,hf.iteLe hg hc.2 hd.2⟩
lemma ifLe (ha : IntExprPoly a) (hb : IntExprPoly b)
    (hc : IntExprPoly c) (hd : IntExprPoly d) :
    IntExprPoly (fun n => IntExpr.ifLe (a n) (b n) (c n) (d n)) :=
  iteLe (ha.1.add hb.2) (hb.1.add ha.2) hc hd
lemma ite (p : ℕ → Prop) [∀ n, Decidable (p n)] (ha : IntExprPoly a) (hb : IntExprPoly b) :
    IntExprPoly (fun n => if p n then a n else b n) := by
  constructor
  · convert NatExprPoly.ite p ha.1 hb.1 using 1 <;> first | (with_reducible_and_instances rfl) | (funext n; dsimp only; split_ifs <;> rfl)
  · convert NatExprPoly.ite p ha.2 hb.2 using 1 <;> first | (with_reducible_and_instances rfl) | (funext n; dsimp only; split_ifs <;> rfl)
lemma signedPower {f : ℕ → ℕ} (ha : IntExprPoly a) (hf : PolyBound f) :
    IntExprPoly (fun n => (a n).signedPower (f n)) :=
  ite (fun n => Even (f n)) (ofNat (ha.natAbs.pow hf))
    (iteLe ha.2 ha.1 (ofNat (ha.natAbs.pow hf)) (ofNat (ha.natAbs.pow hf)).negation)
lemma ceilRatioNat {f : ∀ n, NatExpr (v n)} (ha : IntExprPoly a) (hf : NatExprPoly f) :
    NatExprPoly (fun n => (a n).ceilRatioNat (f n)) :=
  ((ha.toNat.add hf).sub (NatExprPoly.constPoly (PolyBound.const 1))).div hf
lemma floorRatio {f : ∀ n, NatExpr (v n)} (ha : IntExprPoly a) (hf : NatExprPoly f) :
    IntExprPoly (fun n => (a n).floorRatio (f n)) :=
  (ofNat (ha.toNat.div hf)).sub (ofNat (ha.negation.ceilRatioNat hf))
end IntExprPoly

namespace RatExprPoly
variable {v : ℕ → Type*} {a b c d : ∀ n, RatExpr (v n)}
lemma ofNat {f : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) :
    RatExprPoly (fun n => RatExpr.ofNat (f n)) :=
  ⟨IntExprPoly.ofNat hf,NatExprPoly.constPoly (PolyBound.const 1)⟩
lemma ofInt {f : ∀ n, IntExpr (v n)} (hf : IntExprPoly f) :
    RatExprPoly (fun n => RatExpr.ofInt (f n)) :=
  ⟨hf,NatExprPoly.constPoly (PolyBound.const 1)⟩
lemma const {f : ℕ → ℚ} (hn : PolyBound (fun n => (f n).num.natAbs.size))
    (hd : PolyBound (fun n => (f n).den.size)) :
    RatExprPoly (fun n => RatExpr.const (f n) : ∀ n, RatExpr (v n)) :=
  ⟨IntExprPoly.ofInt hn,NatExprPoly.const hd⟩
lemma constant (r : ℚ) : RatExprPoly (fun _ => RatExpr.const r : ∀ n, RatExpr (v n)) :=
  const (PolyBound.const _) (PolyBound.const _)
lemma normalize (ha : RatExprPoly a) : RatExprPoly (fun n => (a n).normalize) :=
  ⟨IntExprPoly.iteLe ha.2 (NatExprPoly.constPoly (PolyBound.const 0))
    (IntExprPoly.ofInt (PolyBound.const 0)) ha.1,
   ha.2.iteLe (NatExprPoly.constPoly (PolyBound.const 0))
    (NatExprPoly.constPoly (PolyBound.const 1)) ha.2⟩
lemma add (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).add (b n)) :=
  ⟨(ha.normalize.1.scale hb.normalize.2).add (hb.normalize.1.scale ha.normalize.2),
    ha.normalize.2.mul hb.normalize.2⟩
lemma negation (ha : RatExprPoly a) : RatExprPoly (fun n => (a n).negation) := ⟨ha.1.negation,ha.2⟩
lemma sub (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).sub (b n)) :=
  ha.add hb.negation
lemma mul (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).mul (b n)) :=
  ⟨ha.1.mul hb.1,ha.2.mul hb.2⟩
lemma inverse (ha : RatExprPoly a) : RatExprPoly (fun n => (a n).inverse) :=
  ⟨ha.1.scale ha.2,ha.1.natAbs.mul ha.1.natAbs⟩
lemma div (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).div (b n)) :=
  ha.mul hb.inverse
lemma pow (ha : RatExprPoly a) (k : ℕ) : RatExprPoly (fun n => (a n).pow k) := by
  induction k with
  | zero => exact constant 1
  | succ k ih => exact ih.mul ha
lemma signedPower {f : ℕ → ℕ} (ha : RatExprPoly a) (hf : PolyBound f) :
    RatExprPoly (fun n => (a n).signedPower (f n)) := ⟨ha.1.signedPower hf,ha.2.pow hf⟩
lemma repeatedSuccess {f : ℕ → ℕ} (ha : RatExprPoly a) (hf : PolyBound f) :
    RatExprPoly (fun n => (a n).repeatedSuccess (f n)) :=
  (constant 1).sub (((constant 1).sub ha).signedPower hf)
lemma ifNatLe {f g : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) (hg : NatExprPoly g)
    (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifNatLe (f n) (g n) (c n) (d n)) :=
  ⟨IntExprPoly.iteLe hf hg hc.1 hd.1,hf.iteLe hg hc.2 hd.2⟩
lemma ifIntLe {f g : ∀ n, IntExpr (v n)} (hf : IntExprPoly f) (hg : IntExprPoly g)
    (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifIntLe (f n) (g n) (c n) (d n)) :=
  ifNatLe (hf.1.add hg.2) (hg.1.add hf.2) hc hd
lemma ifLe (ha : RatExprPoly a) (hb : RatExprPoly b) (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifLe (a n) (b n) (c n) (d n)) :=
  ifIntLe (ha.normalize.1.scale hb.normalize.2) (hb.normalize.1.scale ha.normalize.2) hc hd
lemma ifLt (ha : RatExprPoly a) (hb : RatExprPoly b) (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifLt (a n) (b n) (c n) (d n)) := hb.ifLe ha hd hc
lemma ifEq (ha : RatExprPoly a) (hb : RatExprPoly b) (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifEq (a n) (b n) (c n) (d n)) := ha.ifLe hb (hb.ifLe ha hc hd) hd
lemma max (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).max (b n)) :=
  ha.ifLe hb hb ha
lemma min (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).min (b n)) :=
  ha.ifLe hb ha hb
lemma ceilNat (ha : RatExprPoly a) : NatExprPoly (fun n => (a n).ceilNat) := ha.1.ceilRatioNat ha.2
lemma floor (ha : RatExprPoly a) : IntExprPoly (fun n => (a n).floor) := ha.1.floorRatio ha.2
lemma ceil (ha : RatExprPoly a) : IntExprPoly (fun n => (a n).ceil) := ha.negation.floor.negation
end RatExprPoly
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolynomialExpressionResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
namespace RatExprPoly
variable {v : ℕ → Type*}
lemma ite (p : ℕ → Prop) [∀ n, Decidable (p n)] {a b : ∀ n, RatExpr (v n)}
    (ha : RatExprPoly a) (hb : RatExprPoly b) :
    RatExprPoly (fun n => if p n then a n else b n) := by
  constructor
  · convert IntExprPoly.ite p ha.1 hb.1 using 1 <;> first | (with_reducible_and_instances rfl) | (funext n; dsimp only; split_ifs <;> rfl)
  · convert NatExprPoly.ite p ha.2 hb.2 using 1 <;> first | (with_reducible_and_instances rfl) | (funext n; dsimp only; split_ifs <;> rfl)
lemma sum {f : ℕ → ∀ n, RatExpr (v n)} (hf : ∀ i, RatExprPoly (f i)) (k : ℕ) :
    RatExprPoly (fun n => RatExpr.sum (fun i => f i n) k) := by
  induction k with
  | zero => exact constant 0
  | succ k ih => exact ih.add (hf k)
end RatExprPoly

namespace PolyExprPoly
variable {v : ℕ → Type*} {a b : ∀ n, PolyExpr (v n)}
lemma C {r : ∀ n, RatExpr (v n)} (hr : RatExprPoly r) : PolyExprPoly (fun n => .C (r n)) := by
  intro k
  by_cases h : k=0
  · simpa only [PolyExpr.coeff,ite_eq_left h] using hr
  · simpa only [PolyExpr.coeff,ite_eq_right h] using (RatExprPoly.constant (v:=v) 0)
lemma X : PolyExprPoly (fun _ => PolyExpr.X : ∀ n, PolyExpr (v n)) := by
  intro k
  by_cases h : k=1
  · simpa only [PolyExpr.coeff,ite_eq_left h] using (RatExprPoly.constant (v:=v) 1)
  · simpa only [PolyExpr.coeff,ite_eq_right h] using (RatExprPoly.constant (v:=v) 0)
lemma constant (r : ℚ) : PolyExprPoly (fun _ => PolyExpr.const r : ∀ n, PolyExpr (v n)) :=
  C (RatExprPoly.constant r)
lemma add (ha : PolyExprPoly a) (hb : PolyExprPoly b) : PolyExprPoly (fun n => (a n).add (b n)) :=
  fun k => (ha k).add (hb k)
lemma negation (ha : PolyExprPoly a) : PolyExprPoly (fun n => (a n).negation) :=
  fun k => (ha k).negation
lemma sub (ha : PolyExprPoly a) (hb : PolyExprPoly b) : PolyExprPoly (fun n => (a n).sub (b n)) :=
  ha.add hb.negation
lemma mul (ha : PolyExprPoly a) (hb : PolyExprPoly b) : PolyExprPoly (fun n => (a n).mul (b n)) :=
  fun k => RatExprPoly.sum (fun i => (ha i).mul (hb (k-i))) (k+1)
lemma pow (ha : PolyExprPoly a) (k : ℕ) : PolyExprPoly (fun n => (a n).pow k) := by
  induction k with
  | zero => exact constant 1
  | succ k ih => exact ih.mul ha
end PolyExprPoly

namespace OrderTrial.Expressions
variable {v : Type*}
lemma coveringPow_maxConst (d : NatExpr v) (k : ℕ) :
    (coveringPow d k).maxConst ≤ max d.maxConst (2^k) := by
  induction k with
  | zero => exact le_max_right _ _
  | succ k ih =>
    have h : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact max_le (max_le (le_max_left _ _) (h.trans (le_max_right _ _)))
      (max_le (ih.trans (max_le_max_left _ h)) (le_max_right _ _))
lemma coveringPow_weight (d : NatExpr v) (k : ℕ) :
    (coveringPow d k).weight ≤ (k+1)*(d.weight+7) := by
  have h := Nat.size_le_size (coveringPow_maxConst d k)
  rw [nat_size_max,Nat.size_pow] at h
  have hh : (coveringPow d k).maxConst.size ≤ d.maxConst.size+k+1 := h.trans (by omega)
  simp only [NatExpr.weight,coveringPow_size,coveringPow_sharedCost]
  nlinarith
lemma coveringPow_poly {v : ℕ → Type*} {d : ∀ n, NatExpr (v n)} {f : ℕ → ℕ}
    (hd : NatExprPoly d) (hf : PolyBound f) :
    NatExprPoly (fun n => coveringPow (d n) (f n)) :=
  ((hf.add (PolyBound.const 1)).mul (PolyBound.add hd (PolyBound.const 7))).of_le
    (fun n => coveringPow_weight (d n) (f n))
end OrderTrial.Expressions

end ExactQuantumFactoring

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ConcreteExpressionResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
namespace PolyExpr
variable {v : Type*}
lemma comp_X (a : PolyExpr v) : a.comp X=a := by
  induction a with
  | C c => rfl
  | X => rfl
  | add a b ia ib => simp only [comp,ia,ib]
  | negation a ia => simp only [comp,ia]
  | mul a b ia ib => simp only [comp,ia,ib]
lemma comp_comp (a b c : PolyExpr v) : (a.comp b).comp c=a.comp (b.comp c) := by
  induction a with
  | C r => rfl
  | X => rfl
  | add a b ia ib => simp only [comp,ia,ib]
  | negation a ia => simp only [comp,ia]
  | mul a b ia ib => simp only [comp,ia,ib]
end PolyExpr

end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolySchemaPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring

namespace PolySchemaPoly
variable {v : ℕ → Type*} {a b : ∀ n, PolyExpr (v n)}
lemma coeffs (ha : PolySchemaPoly a) : PolyExprPoly a := by
  simpa only [PolyExpr.comp_X] using ha (fun _=>PolyExpr.X) PolyExprPoly.X
lemma C {r : ∀ n, RatExpr (v n)} (hr : RatExprPoly r) : PolySchemaPoly (fun n => .C (r n)) :=
  fun _ _ => PolyExprPoly.C hr
lemma X : PolySchemaPoly (fun _ => PolyExpr.X : ∀ n, PolyExpr (v n)) := fun _ hb => hb
lemma constant (r : ℚ) : PolySchemaPoly (fun _ => PolyExpr.const r : ∀ n, PolyExpr (v n)) :=
  C (RatExprPoly.constant r)
lemma add (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).add (b n)) := fun c hc => (ha c hc).add (hb c hc)
lemma negation (ha : PolySchemaPoly a) : PolySchemaPoly (fun n => (a n).negation) :=
  fun c hc => (ha c hc).negation
lemma sub (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).sub (b n)) := ha.add hb.negation
lemma mul (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).mul (b n)) := fun c hc => (ha c hc).mul (hb c hc)
lemma pow (ha : PolySchemaPoly a) (k : ℕ) : PolySchemaPoly (fun n => (a n).pow k) := by
  induction k with
  | zero => exact constant 1
  | succ k ih => exact ih.mul ha
lemma comp (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).comp (b n)) := by
  intro c hc
  simpa only [PolyExpr.comp_comp] using ha (fun n => (b n).comp (c n)) (hb c hc)
end PolySchemaPoly


namespace OrderTrial.Expressions
variable {v : ℕ → Type*} {d Q B j u : ∀ n, NatExpr (v n)}
  {η : ∀ n, RatExpr (v n)} {q q₀ q₁ : ∀ n, IntExpr (v n)}
lemma dynamicRamp_poly (hq : IntExprPoly q) (a : ℤ) :
    PolySchemaPoly (fun n => dynamicRamp (q n) a) := by
  have ha : IntExprPoly (fun _=>IntExpr.ofInt a : ∀ n, IntExpr (v n)) :=
    IntExprPoly.ofInt (PolyBound.const _)
  unfold dynamicRamp
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma dynamicRampLin_poly (hq : IntExprPoly q) (a : ℤ) :
    PolySchemaPoly (fun n => dynamicRampLin (q n) a) := by
  have ha : IntExprPoly (fun _=>IntExpr.ofInt a : ∀ n, IntExpr (v n)) :=
    IntExprPoly.ofInt (PolyBound.const _)
  unfold dynamicRampLin
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma dynamicSplineRe_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicSplineRe (q n)) := by
  have h0 := dynamicRamp_poly hq 0
  have h2 := dynamicRamp_poly hq 2
  have h4 := dynamicRamp_poly hq 4
  unfold dynamicSplineRe
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma dynamicSplineIm_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicSplineIm (q n)) := by
  have h0 := dynamicRamp_poly hq (-1)
  have h2 := dynamicRamp_poly hq 1
  have h4 := dynamicRamp_poly hq 3
  have h5 := dynamicRamp_poly hq 5
  unfold dynamicSplineIm
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma dynamicPhaseRe_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicPhaseRe (q n)) := by
  have h0 := dynamicRampLin_poly hq 0
  have h2 := dynamicRampLin_poly hq 2
  have h4 := dynamicRampLin_poly hq 4
  unfold dynamicPhaseRe
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma dynamicPhaseIm_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicPhaseIm (q n)) := by
  have h0 := dynamicRampLin_poly hq (-1)
  have h2 := dynamicRampLin_poly hq 1
  have h4 := dynamicRampLin_poly hq 3
  have h5 := dynamicRampLin_poly hq 5
  unfold dynamicPhaseIm
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma linearPoly_poly (hd : NatExprPoly d) (hη : RatExprPoly η) :
    PolySchemaPoly (fun n => linearPoly (d n) (η n)) := by
  unfold linearPoly
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma integralZero_poly {A : ∀ n, PolyExpr (v n)} (hd : NatExprPoly d) (hA : PolySchemaPoly A) :
    PolySchemaPoly (fun n => integralZero (d n) (A n)) := by
  have hlin := linearPoly_poly hd (RatExprPoly.constant 0)
  unfold integralZero
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma integralSlope_poly {A C : ∀ n, PolyExpr (v n)} (hd : NatExprPoly d)
    (hη : RatExprPoly η) (hA : PolySchemaPoly A) (hC : PolySchemaPoly C) :
    PolySchemaPoly (fun n => integralSlope (d n) (η n) (A n) (C n)) := by
  have hlin := linearPoly_poly hd hη
  have hzero := linearPoly_poly hd (RatExprPoly.constant 0)
  unfold integralSlope
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma dynamicMassZero_poly (hd : NatExprPoly d) (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicMassZero (d n) (q n)) :=
  ((integralZero_poly hd (dynamicPhaseRe_poly hq)).pow 2).add
    ((integralZero_poly hd (dynamicPhaseIm_poly hq)).pow 2)
lemma dynamicMassSlope_poly (hd : NatExprPoly d) (hη : RatExprPoly η)
    (hq0 : IntExprPoly q₀) (hq1 : IntExprPoly q₁) :
    PolySchemaPoly (fun n => dynamicMassSlope (d n) (η n) (q₀ n) (q₁ n)) :=
  ((integralSlope_poly hd hη (dynamicSplineRe_poly hq0) (dynamicSplineRe_poly hq1)).pow 2).add
    ((integralSlope_poly hd hη (dynamicSplineIm_poly hq0) (dynamicSplineIm_poly hq1)).pow 2)
lemma dynamicMassCoeff_poly (hd : NatExprPoly d) (hη : RatExprPoly η)
    (hq0 : IntExprPoly q₀) (hq1 : IntExprPoly q₁) (k : ℕ) :
    RatExprPoly (fun n => dynamicMassCoeff (d n) (η n) (q₀ n) (q₁ n) k) :=
  hη.ifEq (RatExprPoly.constant 0) ((dynamicMassZero_poly hd hq0).coeffs k)
    ((dynamicMassSlope_poly hd hη hq0 hq1).coeffs k)
end OrderTrial.Expressions
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialExpressionResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
namespace NatExprPoly
variable {v : ℕ → Type*} {a b : ∀ n, NatExpr (v n)}
lemma min (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => (a n).min (b n)) := ha.iteLe hb ha hb
lemma max (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => (a n).max (b n)) := ha.iteLe hb hb ha
end NatExprPoly
namespace RatExprPoly
lemma sumList {v : ℕ → Type*} {α : Type*} {f : α → ∀ n, RatExpr (v n)}
    (hf : ∀ i, RatExprPoly (f i)) (xs : List α) :
    RatExprPoly (fun n => RatExpr.sumList (fun i => f i n) xs) := by
  induction xs with
  | nil => exact constant 0
  | cons i xs ih => exact (hf i).add ih
end RatExprPoly

namespace OrderTrial.Expressions
variable {v : ℕ → Type*} {a b η : ∀ n, RatExpr (v n)}
  {Q B d j t u lo hi : ∀ n, NatExpr (v n)}
lemma powerSum_poly (ha : RatExprPoly a) (q : ℕ) :
    RatExprPoly (fun n => powerSum q (a n)) := by
  rcases q with _|_|_|_|_|q <;> simp only [powerSum] <;> repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma fiveTerm_poly {f : ℕ → ∀ n, RatExpr (v n)} (hf : ∀ i, RatExprPoly (f i))
    (hl : NatExprPoly lo) (hh : NatExprPoly hi) :
    RatExprPoly (fun n => fiveTerm (fun i => f i n) (lo n) (hi n)) := by
  exact RatExprPoly.ifNatLe hl hh (RatExprPoly.sum (fun i => (hf i).mul
    ((powerSum_poly (RatExprPoly.ofNat hh) i).sub (powerSum_poly (RatExprPoly.ofNat hl) i))) 5) (RatExprPoly.constant 0)
lemma linear_poly (ha : RatExprPoly a) (hb : RatExprPoly b)
    (hl : NatExprPoly lo) (hh : NatExprPoly hi) :
    RatExprPoly (fun n => linear (a n) (b n) (lo n) (hi n)) := by
  apply fiveTerm_poly _ hl hh
  intro q
  exact RatExprPoly.ite (fun _=>q=0) ha
    (RatExprPoly.ite (fun _=>q=1) hb (RatExprPoly.constant 0))
lemma ramp_poly (ha : RatExprPoly a) (hb : RatExprPoly b) (hd : NatExprPoly d) :
    RatExprPoly (fun n => ramp (a n) (b n) (d n)) := by
  have hx := (ha.negation.div hb).ceilNat
  have h1 := linear_poly ha hb hx hd
  have h2 := linear_poly ha hb (NatExprPoly.constPoly (PolyBound.const 0)) (hd.min hx)
  unfold ramp
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma phaseRe_poly (ha : RatExprPoly a) (hb : RatExprPoly b) (hd : NatExprPoly d) :
    RatExprPoly (fun n => phaseRe (a n) (b n) (d n)) := by
  have h1 := linear_poly (ha.add ((RatExprPoly.constant 1).div (RatExprPoly.constant 2))) hb
    (NatExprPoly.constPoly (PolyBound.const 0)) hd
  have h2 := ramp_poly ha hb hd
  have h3 := ramp_poly (ha.sub ((RatExprPoly.constant 1).div (RatExprPoly.constant 2))) hb hd
  have h4 := ramp_poly (ha.sub (RatExprPoly.constant 1)) hb hd
  unfold phaseRe
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma phaseIm_poly (ha : RatExprPoly a) (hb : RatExprPoly b) (hd : NatExprPoly d) :
    RatExprPoly (fun n => phaseIm (a n) (b n) (d n)) := by
  have h1 := linear_poly (ha.add ((RatExprPoly.constant 1).div (RatExprPoly.constant 2))) hb
    (NatExprPoly.constPoly (PolyBound.const 0)) hd
  have h2 := ramp_poly (ha.add ((RatExprPoly.constant 1).div (RatExprPoly.constant 4))) hb hd
  have h3 := ramp_poly (ha.sub ((RatExprPoly.constant 1).div (RatExprPoly.constant 4))) hb hd
  have h4 := ramp_poly (ha.sub ((RatExprPoly.constant 3).div (RatExprPoly.constant 4))) hb hd
  have h5 := ramp_poly (ha.sub ((RatExprPoly.constant 5).div (RatExprPoly.constant 4))) hb hd
  unfold phaseIm
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma binE_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    NatExprPoly (fun n => binE (Q n) (d n) (j n)) := by
  unfold binE
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma error_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n => error (Q n) (d n) (j n)) := by
  have h := binE_poly hQ hd hj
  unfold error
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma offset_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j)
    (ht : NatExprPoly t) : RatExprPoly (fun n => offset (Q n) (d n) (j n) (t n)) := by
  have h := error_poly hQ hd hj
  unfold offset
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma slope_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n => slope (Q n) (d n) (j n)) := by
  have h := error_poly hQ hd hj
  unfold slope
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma count_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (ht : NatExprPoly t) :
    NatExprPoly (fun n => count (Q n) (d n) (t n)) := by
  unfold count
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma probability_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j)
    (ht : NatExprPoly t) : RatExprPoly (fun n => probability (Q n) (d n) (j n) (t n)) := by
  have ho := offset_poly hQ hd hj ht
  have hs := slope_poly hQ hd hj
  have hc := count_poly hQ hd ht
  have hr := phaseRe_poly ho hs hc
  have hi := phaseIm_poly ho hs hc
  unfold probability
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma rounded_poly (hd : NatExprPoly d) (ha : RatExprPoly a) :
    RatExprPoly (fun n => rounded (d n) (a n)) := by unfold rounded; repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma roundingDen_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) :
    NatExprPoly (fun n => roundingDen (Q n) (B n)) := hQ.mul (hB.pow (PolyBound.const 8))
lemma quarter_poly (ha : RatExprPoly a) : IntExprPoly (fun n => quarter (a n)) := by
  unfold quarter; repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma majorantE_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) (hd : NatExprPoly d)
    (hj : NatExprPoly j) (hu : NatExprPoly u) :
    RatExprPoly (fun n => majorantE (Q n) (B n) (d n) (j n) (u n)) := by
  have he := error_poly hQ hd hj
  have h0 := quarter_poly ((RatExprPoly.ofNat hu).div (RatExprPoly.ofNat hd))
  have h1 := quarter_poly (((RatExprPoly.ofNat hu).div (RatExprPoly.ofNat hd)).add he)
  have hs := RatExprPoly.sum (fun k =>
    (rounded_poly (roundingDen_poly hQ hB) (dynamicMassCoeff_poly hd he h0 h1 k)).mul
      ((RatExprPoly.ofNat hu).pow k)) 5
  unfold majorantE
  exact hs.add ((RatExprPoly.constant 64).div (RatExprPoly.ofNat hQ))
end OrderTrial.Expressions
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_StaticMajorantResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : ℕ → Type*} {d Q B j : ∀ n, NatExpr (v n)} {η : ∀ n, RatExpr (v n)}
lemma rampPoly_poly (q a : ℤ) :
    PolySchemaPoly (fun _ => rampPoly q a : ∀ n, PolyExpr (v n)) := by
  unfold rampPoly
  split <;> repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma rampLin_poly (q a : ℤ) :
    PolySchemaPoly (fun _ => rampLin q a : ∀ n, PolyExpr (v n)) := by
  unfold rampLin
  split <;> repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma splineRePoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => splineRePoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampPoly_poly (v:=v) q 0
  have h2 := rampPoly_poly (v:=v) q 2
  have h4 := rampPoly_poly (v:=v) q 4
  unfold splineRePoly
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma splineImPoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => splineImPoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampPoly_poly (v:=v) q (-1)
  have h2 := rampPoly_poly (v:=v) q 1
  have h4 := rampPoly_poly (v:=v) q 3
  have h5 := rampPoly_poly (v:=v) q 5
  unfold splineImPoly
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma phaseRePoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => phaseRePoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampLin_poly (v:=v) q 0
  have h2 := rampLin_poly (v:=v) q 2
  have h4 := rampLin_poly (v:=v) q 4
  unfold phaseRePoly
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma phaseImPoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => phaseImPoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampLin_poly (v:=v) q (-1)
  have h2 := rampLin_poly (v:=v) q 1
  have h4 := rampLin_poly (v:=v) q 3
  have h5 := rampLin_poly (v:=v) q 5
  unfold phaseImPoly
  repeat' (with_reducible_and_instances first | assumption | exact PolySchemaPoly.X | exact PolySchemaPoly.constant _ | apply PolySchemaPoly.C | apply PolySchemaPoly.add | apply PolySchemaPoly.sub | apply PolySchemaPoly.mul | apply PolySchemaPoly.negation | apply PolySchemaPoly.pow | apply PolySchemaPoly.comp | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma massZero_poly (hd : NatExprPoly d) (q : ℤ) :
    PolySchemaPoly (fun n => massZero (d n) q) :=
  ((integralZero_poly hd (phaseRePoly_poly q)).pow 2).add
    ((integralZero_poly hd (phaseImPoly_poly q)).pow 2)
lemma massSlope_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q₀ q₁ : ℤ) :
    PolySchemaPoly (fun n => massSlope (d n) (η n) q₀ q₁) :=
  ((integralSlope_poly hd hη (splineRePoly_poly q₀) (splineRePoly_poly q₁)).pow 2).add
    ((integralSlope_poly hd hη (splineImPoly_poly q₀) (splineImPoly_poly q₁)).pow 2)
lemma massCoeff_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q₀ q₁ : ℤ) (k : ℕ) :
    RatExprPoly (fun n => massCoeff (d n) (η n) q₀ q₁ k) :=
  hη.ifEq (RatExprPoly.constant 0) ((massZero_poly hd q₀).coeffs k)
    ((massSlope_poly hd hη q₀ q₁).coeffs k)
lemma low_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q : ℤ×ℤ) :
    NatExprPoly (fun n => low (d n) (η n) q) := by
  unfold low
  apply NatExprPoly.max <;> repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma high_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q : ℤ×ℤ) :
    NatExprPoly (fun n => high (d n) (η n) q) := by
  unfold high
  apply NatExprPoly.min hd
  apply NatExprPoly.min <;> repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma pieceSum_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) (hd : NatExprPoly d)
    (hj : NatExprPoly j) (q : ℤ×ℤ) :
    RatExprPoly (fun n => pieceSum (Q n) (B n) (d n) (j n) q) := by
  have he := error_poly hQ hd hj
  have hl := low_poly hd he q
  have hh := high_poly hd he q
  have hs := fiveTerm_poly
    (fun k => rounded_poly (roundingDen_poly hQ hB) (massCoeff_poly hd he q.1 q.2 k)) hl hh
  unfold pieceSum
  exact hs.add ((RatExprPoly.ofNat (hh.sub hl)).mul
    ((RatExprPoly.constant 64).div (RatExprPoly.ofNat hQ)))
lemma majorantSumE_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) (hd : NatExprPoly d)
    (hj : NatExprPoly j) :
    RatExprPoly (fun n => majorantSumE (Q n) (B n) (d n) (j n)) :=
  (RatExprPoly.sumList (fun q => pieceSum_poly hQ hB hd hj q) quarterList).div
    (RatExprPoly.constant 2)
end ExactQuantumFactoring.OrderTrial.Expressions

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetentionExpressionResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : ℕ→Type*} {d Q B j t : ∀ n,NatExpr (v n)} {f : ℕ→ℕ}
lemma lambdaE_poly (hf : PolyBound f) (hd : NatExprPoly d) :
    RatExprPoly (fun n=>lambdaE (f n) (d n)) := by
  have hh := coveringPow_poly hd hf
  unfold lambdaE
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma coefficientE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>coefficientE (f n) (Q n) (B n) (d n) (j n)) := by
  have hh := lambdaE_poly hf hd
  have hs := majorantSumE_poly hQ hB hd hj
  have hc : NatExprPoly (fun n=>NatExpr.const (2^(10*f n)) : ∀ n,NatExpr (v n)) :=
    NatExprPoly.const ((PolyBound.const 10).mul hf).twoPowSize
  unfold coefficientE
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma remainderE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>remainderE (f n) (Q n) (B n) (d n) (j n)) :=
  (lambdaE_poly hf hd).sub ((coefficientE_poly hf hQ hB hd hj).mul (majorantSumE_poly hQ hB hd hj))
lemma discrepancyE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) (ht : NatExprPoly t) :
    RatExprPoly (fun n=>discrepancyE (f n) (Q n) (B n) (d n) (j n) (t n)) := by
  have hm := majorantE_poly hQ hB hd hj ((hj.mul ht).mod hd)
  have hp := probability_poly hQ hd hj ht
  have hc := coefficientE_poly hf hQ hB hd hj
  unfold discrepancyE
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma thirdRetentionE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>thirdRetentionE (f n) (Q n) (B n) (d n) (j n)) := by
  have hr := remainderE_poly hf hQ hB hd hj
  unfold thirdRetentionE
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma firstE_poly (hf : PolyBound f) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>firstE (f n) (d n) (j n)) := by
  apply coefficientE_poly hf _ (NatExprPoly.const hf.twoPowSize) hd hj
  apply NatExprPoly.const
  simpa only [←pow_mul] using (hf.mul (PolyBound.const 16)).twoPowSize
lemma secondE_poly (hf : PolyBound f) (hd : NatExprPoly d) (hj : NatExprPoly j)
    (ht : NatExprPoly t) : RatExprPoly (fun n=>secondE (f n) (d n) (j n) (t n)) := by
  apply discrepancyE_poly hf _ (NatExprPoly.const hf.twoPowSize) hd hj ht
  apply NatExprPoly.const
  simpa only [←pow_mul] using (hf.mul (PolyBound.const 16)).twoPowSize
lemma lastE_poly (hf : PolyBound f) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>lastE (f n) (d n) (j n)) := by
  apply thirdRetentionE_poly hf _ (NatExprPoly.const hf.twoPowSize) hd hj
  apply NatExprPoly.const
  simpa only [←pow_mul] using (hf.mul (PolyBound.const 16)).twoPowSize
end ExactQuantumFactoring.OrderTrial.Expressions

namespace ExactQuantumFactoring
lemma thresholdExpr_poly {v : ℕ→Type*} {T : ℕ→ℕ} {p : ∀ n,RatExpr (v n)}
    {c : ∀ n,NatExpr (v n)} (hT : PolyBound T) (hp : RatExprPoly p) (hc : NatExprPoly c) :
    NatExprPoly (fun n=>thresholdExpr (T n) (p n) (c n)) := by
  have hh : NatExprPoly (fun n=>NatExpr.const (2^(T n)) : ∀ n,NatExpr (v n)) :=
    NatExprPoly.const hT.twoPowSize
  unfold thresholdExpr
  repeat' (with_reducible_and_instances first | assumption | exact NatExprPoly.var _ | exact RatExprPoly.constant _ | exact PolyExprPoly.X | exact PolyExprPoly.constant _ | apply RatExprPoly.ofNat | apply RatExprPoly.ofInt | apply RatExprPoly.normalize | apply RatExprPoly.add | apply RatExprPoly.sub | apply RatExprPoly.mul | apply RatExprPoly.negation | apply RatExprPoly.inverse | apply RatExprPoly.div | apply RatExprPoly.pow | apply RatExprPoly.ifNatLe | apply RatExprPoly.ifIntLe | apply RatExprPoly.ifLe | apply RatExprPoly.ifLt | apply RatExprPoly.ifEq | apply RatExprPoly.max | apply RatExprPoly.min | apply IntExprPoly.ofNat | apply IntExprPoly.add | apply IntExprPoly.sub | apply IntExprPoly.mul | apply IntExprPoly.scale | apply IntExprPoly.negation | apply IntExprPoly.iteLe | apply IntExprPoly.ifLe | apply IntExprPoly.toNat | apply IntExprPoly.natAbs | apply IntExprPoly.ceilRatioNat | apply IntExprPoly.floorRatio | apply RatExprPoly.ceilNat | apply RatExprPoly.floor | apply RatExprPoly.ceil | apply PolyExprPoly.C | apply PolyExprPoly.add | apply PolyExprPoly.sub | apply PolyExprPoly.mul | apply PolyExprPoly.negation | apply PolyExprPoly.pow | apply NatExprPoly.add | apply NatExprPoly.sub | apply NatExprPoly.mul | apply NatExprPoly.div | apply NatExprPoly.mod | apply NatExprPoly.iteLe | apply NatExprPoly.const | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialNetworkPolynomial
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace OrderTrial
variable {α : Type*} {len k w : α→ℕ}
lemma decodeVars_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t) (hc : NetworkAt len c) :
    ∃p : Polynomial ℕ,∀x (i : DecodeVar),
      ((match i with | .den=>d x | .num=>j x | .residue=>t x | .coin=>c x) :
        BooleanNetwork (k x) (w x)).net.count≤p.eval (len x) := by
  obtain ⟨p,hp⟩:=((hd.add hj).add ht).add hc
  refine ⟨p,fun x i=>?_⟩
  have h:=hp x
  dsimp only at h
  cases i <;> dsimp only <;> omega

lemma firstRetNet_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hw : PolyAt len w) :
    NetworkAt len (fun x=>firstRetNet (len x) (d x) (j x) (t x) (c x)) := by
  have hE : RatExprPoly (fun n=>Expressions.firstE n (.var DecodeVar.den) (.var .num)) :=
    Expressions.firstE_poly PolyBound.id (NatExprPoly.var _) (NatExprPoly.var _)
  have hT:=thresholdExpr_poly PreparationPolynomial.retentionBits hE
    (NatExprPoly.var (fun _=>DecodeVar.coin))
  exact (NatExprAt.ofPoly hT len).isOne hw (decodeVars_poly hd hj ht hc)
lemma secondRetNet_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hw : PolyAt len w) :
    NetworkAt len (fun x=>secondRetNet (len x) (d x) (j x) (t x) (c x)) := by
  have hE : RatExprPoly (fun n=>Expressions.secondE n (.var DecodeVar.den) (.var .num) (.var .residue)) :=
    Expressions.secondE_poly PolyBound.id (NatExprPoly.var _) (NatExprPoly.var _) (NatExprPoly.var _)
  have hT:=thresholdExpr_poly PreparationPolynomial.retentionBits hE
    (NatExprPoly.var (fun _=>DecodeVar.coin))
  exact (NatExprAt.ofPoly hT len).isOne hw (decodeVars_poly hd hj ht hc)
lemma thirdRetNet_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hw : PolyAt len w) :
    NetworkAt len (fun x=>thirdRetNet (len x) (d x) (j x) (t x) (c x)) := by
  have hE : RatExprPoly (fun n=>Expressions.lastE n (.var DecodeVar.den) (.var .num)) :=
    Expressions.lastE_poly PolyBound.id (NatExprPoly.var _) (NatExprPoly.var _)
  have hT:=thresholdExpr_poly PreparationPolynomial.retentionBits hE
    (NatExprPoly.var (fun _=>DecodeVar.coin))
  exact (NatExprAt.ofPoly hT len).isOne hw (decodeVars_poly hd hj ht hc)
lemma labelValidNet_poly {a m d j : ∀x,BooleanNetwork (k x) (w x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hj : NetworkAt len j) (hw : PolyAt len w) :
    NetworkAt len (fun x=>labelValidNet (len x) (a x) (m x) (d x) (j x)) := by
  let c:=fun x=>(a x).net.count+(m x).net.count+(d x).net.count+(j x).net.count
  have hc : PolyAt len c:=((ha.add hm).add hd).add hj
  have hg : PolyAt len (fun x=>2*w x*(216*w x*w x+300*w x+100)) := by
    exact ((PolyAt.const len 2).mul hw).mul ((((PolyAt.const len 216).mul hw).mul hw).add
      ((PolyAt.const len 300).mul hw) |>.add (PolyAt.const len 100))
  have hp : PolyAt len (fun x=>w x+w x*(3672*w x*w x+436*w x+36)) := by
    exact hw.add (hw.mul ((((PolyAt.const len 3672).mul hw).mul hw).add
      ((PolyAt.const len 436).mul hw) |>.add (PolyAt.const len 36)))
  apply NetworkAt.of_le (bound:=fun x=>9*c x+
    (2*w x*(216*w x*w x+300*w x+100))+(w x+w x*(3672*w x*w x+436*w x+36))+344*w x+70)
  · repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  · intro x
    have h:=labelValidNet_count (len x) (a x) (m x) (d x) (j x)
      (c:=c x) (by dsimp [c];omega) (by dsimp [c];omega)
      (by dsimp [c];omega) (by dsimp [c];omega)
    omega
lemma trialAcceptOn_poly {a m mode d j t c : ∀x,BooleanNetwork (k x) (w x)}
    {selected : ∀x,BooleanNetwork (k x) 1}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hmode : NetworkAt len mode)
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hs : NetworkAt len selected) (hw : PolyAt len w) :
    NetworkAt len (fun x=>trialAcceptOn (len x) (a x) (m x) (mode x) (d x) (j x) (t x) (c x) (selected x)) := by
  have h2:=NetworkAt.wordConstant (a:=k) (fun x=>BitVec.ofNat (w x) 2) hw
  have h3:=NetworkAt.wordConstant (a:=k) (fun x=>BitVec.ofNat (w x) 3) hw
  have h1:=firstRetNet_poly hd hj ht hc hw
  have hsecond:=secondRetNet_poly hd hj ht hc hw
  have hthird:=thirdRetNet_poly hd hj ht hc hw
  exact (labelValidNet_poly ha hm hd hj hw).band
    (((hmode.wordLt h2 hw).band (hs.band h1)).bor
      (((hmode.equalOn h2 hw).band ((ht.wordLt hd hw).band hsecond)).bor
        ((hmode.equalOn h3 hw).band hthird)))
end OrderTrial
end ExactQuantumFactoring

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RawDecoderPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace OrderTrial
lemma rawMode_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawMode r).net.count=r.net.count := by
  simp only [rawMode,leftNet,count_comp,count_select,Nat.add_zero]
lemma rawSample_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawSample r).net.count=r.net.count := by
  simp only [rawSample,leftNet,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawGuesses_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawGuesses r).net.count=r.net.count := by
  simp only [rawGuesses,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawDen_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawDen r).net.count=r.net.count := by
  simp only [rawDen,rawGuesses_count,leftNet,count_comp,count_select,Nat.add_zero]
lemma rawNum_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawNum r).net.count=r.net.count := by
  simp only [rawNum,rawGuesses_count,leftNet,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawResidue_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawResidue r).net.count=r.net.count := by
  simp only [rawResidue,rawGuesses_count,leftNet,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawCoin_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawCoin r).net.count=r.net.count := by
  simp only [rawCoin,rawGuesses_count,rightNet,count_comp,count_select,Nat.add_zero]
lemma decodeSteps_poly : PolyBound (fun n=>decodeSteps (OrderSlots.sampleExponent n)) := by
  unfold decodeSteps
  have:=PreparationPolynomial.sampleExponent
  repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma decodeWidth_poly : PolyBound (fun n=>decodeWidth n (OrderSlots.sampleExponent n) n) := by
  have hs:=PreparationPolynomial.sampleExponent
  have ht:=decodeSteps_poly
  have hcf : PolyBound (fun n=>cfWidth (OrderSlots.sampleExponent n+3) (decodeSteps (OrderSlots.sampleExponent n))) := by
    unfold cfWidth;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  have hr:=PreparationPolynomial.retentionBits
  unfold decodeWidth;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)

variable {α : Type*} {len k : α→ℕ}
  {r : ∀x,BooleanNetwork (k x) (rawWidth (len x) (OrderSlots.sampleExponent (len x)) (len x))}
lemma recoveredPairNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>recoveredPairNet (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  have hs:=PolyAt.ofPoly PreparationPolynomial.sampleExponent len
  have hrs : NetworkAt len (fun x=>rawSample (r x)) := by
    simpa only [NetworkAt,rawSample_count] using hr
  have hy : NetworkAt len (fun x=>(rawSample (r x)).comp (sampleYNet (len x) (OrderSlots.sampleExponent (len x)+2))) :=
    hrs.comp (NetworkAt.select _)
  exact recoveryNet_poly (NetworkAt.wordConstant _ hw) (NetworkAt.wordConstant _ hw)
    (hy.toWidth (hs.add (PolyAt.const len 2)) hw) hw (PolyAt.ofPoly decodeSteps_poly len)
lemma trialPairNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>trialPairNet (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  have hn:=PolyAt.self len
  have hm : NetworkAt len (fun x=>rawMode (r x)) := by
    simpa only [NetworkAt,rawMode_count] using hr
  have hd : NetworkAt len (fun x=>rawDen (r x)) := by
    simpa only [NetworkAt,rawDen_count] using hr
  have hj : NetworkAt len (fun x=>rawNum (r x)) := by
    simpa only [NetworkAt,rawNum_count] using hr
  exact ((hm.toWidth (PolyAt.const len 2) hw).wordLt (NetworkAt.wordConstant _ hw) hw).wordMux
    (recoveredPairNet_poly hr) ((hd.toWidth hn hw).pair (hj.toWidth hn hw)) (hw.add hw)
lemma trialDenNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>trialDenNet (r x)) :=
  (trialPairNet_poly hr).comp (NetworkAt.select _)
lemma trialNumNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>trialNumNet (r x)) :=
  (trialPairNet_poly hr).comp (NetworkAt.select _)

lemma samplerSelectedNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    {z : ∀x,BooleanNetwork (k x) (OrderSample.width (len x) (OrderSlots.sampleExponent (len x)+2))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hz : NetworkAt len z) :
    NetworkAt len (fun x=>samplerSelectedNet (a x) (m x) (z x)) := by
  have hs := PolyAt.ofPoly PreparationPolynomial.sampleExponent len
  have hscratch := PolyAt.ofPoly PreparationPolynomial.sampleScratch len
  have hwidth := PolyAt.ofPoly PreparationPolynomial.sampleWidth len
  have hwork : PolyAt len (fun x=>Triangular.work (OrderSlots.sampleExponent (len x)+2)) := by
    unfold Triangular.work;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  have hrest : PolyAt len (fun x=>3*(OrderSlots.sampleExponent (len x)+2)+
      Triangular.work (OrderSlots.sampleExponent (len x)+2)+
      OrderSample.scratch (len x) (OrderSlots.sampleExponent (len x)+2)+
      98*OrderSample.width (len x) (OrderSlots.sampleExponent (len x)+2)+21) := by
    exact (((((PolyAt.const len 3).mul (hs.add (PolyAt.const len 2))).add hwork).add hscratch).add
      ((PolyAt.const len 98).mul hwidth)).add (PolyAt.const len 21)
  apply NetworkAt.of_le (bound:=fun x=>3*(z x).net.count+(a x).net.count+(m x).net.count+
      (3*(OrderSlots.sampleExponent (len x)+2)+Triangular.work (OrderSlots.sampleExponent (len x)+2)+
      OrderSample.scratch (len x) (OrderSlots.sampleExponent (len x)+2)+
      98*OrderSample.width (len x) (OrderSlots.sampleExponent (len x)+2)+21))
  · exact (((PolyAt.const len 3).mul hz).add ha |>.add hm).add hrest
  · intro x
    have h:=samplerSelectedNet_count (a x) (m x) (z x)
    omega
lemma rawAcceptNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len r) :
    NetworkAt len (fun x=>rawAcceptNet (a x) (m x) (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  have hn:=PolyAt.self len
  have hmode : NetworkAt len (fun x=>rawMode (r x)) := by
    simpa only [NetworkAt,rawMode_count] using hr
  have ht : NetworkAt len (fun x=>rawResidue (r x)) := by
    simpa only [NetworkAt,rawResidue_count] using hr
  have hc : NetworkAt len (fun x=>rawCoin (r x)) := by
    simpa only [NetworkAt,rawCoin_count] using hr
  have hs : NetworkAt len (fun x=>rawSample (r x)) := by
    simpa only [NetworkAt,rawSample_count] using hr
  exact trialAcceptOn_poly (ha.toWidth hn hw) (hm.toWidth hn hw)
    (hmode.toWidth (PolyAt.const len 2) hw) (trialDenNet_poly hr) (trialNumNet_poly hr)
    (ht.toWidth hn hw) (hc.toWidth (PolyAt.ofPoly PreparationPolynomial.retentionBits len) hw)
    (samplerSelectedNet_poly ha hm hs) hw
lemma trialValueNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len r) :
    NetworkAt len (fun x=>trialValueNet (a x) (m x) (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  exact (rawAcceptNet_poly ha hm hr).wordMux (trialDenNet_poly hr) (NetworkAt.wordConstant _ hw) hw
lemma trialSmallValueNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len r) :
    NetworkAt len (fun x=>trialSmallValueNet (a x) (m x) (r x)) :=
  (trialValueNet_poly ha hm hr).comp
    (NetworkAt.resizeWord (PolyAt.ofPoly decodeWidth_poly len) (PolyAt.self len))
end OrderTrial
end ExactQuantumFactoring

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderDecoderPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NetworkAt
variable {α : Type*} {len a w K : α→ℕ}
lemma minimumNet {f : ∀x,Fin (K x)→BooleanNetwork (a x) (w x)}
    (hK : PolyAt len K) (hw : PolyAt len w)
    (hf : NetworkAt (fun xi : Σx,Fin (K x)=>len xi.1) (fun xi=>f xi.1 xi.2)) :
    NetworkAt len (fun x=>OrderTrial.minimumNet (f x)) := by
  obtain ⟨p,hp⟩:=hf
  have hpoly : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply of_le (bound:=fun x=>w x+K x*(p.eval (len x)+300*w x+60))
  · exact hw.add (hK.mul ((hpoly.add ((PolyAt.const len 300).mul hw)).add (PolyAt.const len 60)))
  · exact fun x=>minimumNet_count (f x) (fun i=>hp ⟨x,i⟩)
end NetworkAt
namespace OrderSlots
variable {α : Type*} {len k : α→ℕ} {a m : ∀x,BooleanNetwork (k x) (len x)}
lemma usableOn_poly (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>usableOn (a x) (m x)) := by
  have hn:=PolyAt.self len
  exact (ha.wordLt hm hn).band
    (((ha.pair hm).comp (NetworkAt.gcdNet hn)).equalOn (NetworkAt.wordConstant _ hn) hn)
lemma orderResultNet_poly {raw : ∀x,BooleanNetwork (k x) (ordinaryWidth (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>orderResultNet (a x) (m x) (raw x)) := by
  let ix := Σx:α,Fin ((len x)^5)
  let param : ix→α:=Sigma.fst
  have hs : NetworkAt (fun xi:ix=>len xi.1)
      (fun xi=>(raw xi.1).comp (tensorSelect (rawWidth (len xi.1)
        (sampleExponent (len xi.1)) (len xi.1)) ((len xi.1)^5) xi.2)) :=
    (hr.pull param).comp (NetworkAt.select _)
  exact NetworkAt.minimumNet ((PolyAt.self len).pow 5) (PolyAt.self len)
    (trialSmallValueNet_poly (ha.pull param) (hm.pull param) hs)
lemma ordinaryOn_poly {raw : ∀x,BooleanNetwork (k x) (ordinaryWidth (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>ordinaryOn (a x) (m x) (raw x)) := by
  have hn:=PolyAt.self len
  exact ((usableOn_poly ha hm).wordMux (orderResultNet_poly ha hm hr)
    (NetworkAt.wordConstant _ hn) hn).comp
      (NetworkAt.resizeWord hn (PolyAt.ofPoly PreparationPolynomial.transitionWidth len))
lemma outputOn_poly {raw : ∀x,BooleanNetwork (k x) (width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>outputOn (a x) (m x) (raw x)) := by
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  have hra : NetworkAt len (fun x=>Completion.rareNet (ordinaryWidth (len x))
      (Completion.transitionWidth (len x)) (2*len x) ((len x+10)*(len x)^5)) := by
    apply NetworkAt.of_le (bound:=fun x=>97*(2*len x)+21)
    · repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
    · exact fun x=>Completion.rareNet_count ..
  exact (hr.comp hra).wordMux (hr.comp (NetworkAt.select _))
    (ordinaryOn_poly ha hm (hr.comp (NetworkAt.select _))) hw
end OrderSlots
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedStack
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

lemma stackPop_count (s w : ℕ) : (stackPop s w).net.count ≤ s*w*w := by
  apply wordBlocks_count
  intro i
  by_cases hi : i.val+1 < s
  · have he : (if h : i.val+1 < s then blockNet s w ⟨i.val+1,h⟩ else wordConstant 0) =
        blockNet s w ⟨i.val+1,hi⟩ := dite_eq_left hi
    have hh := congrArg (fun c : BooleanNetwork (s*w) w => c.net.count) he
    rw [hh,blockNet_count]
    omega
  · have he : (if h : i.val+1 < s then blockNet s w ⟨i.val+1,h⟩ else wordConstant 0) =
        wordConstant 0 := dite_eq_right hi
    have hh := congrArg (fun c : BooleanNetwork (s*w) w => c.net.count) he
    rw [hh,wordConstant_count]

lemma stackPush_count {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w)) :
    (stackPush a v).net.count ≤ s*w*(a.net.count+v.net.count) := by
  apply wordBlocks_count
  intro i
  by_cases hi : i.val=0
  · have he : (if h : i.val=0 then a else v.comp (blockNet s w ⟨i.val-1,by omega⟩))=a := dite_eq_left hi
    have hh := congrArg (fun c : BooleanNetwork k w => c.net.count) he
    rw [hh]
    omega
  · have he : (if h : i.val=0 then a else v.comp (blockNet s w ⟨i.val-1,by omega⟩))=
        v.comp (blockNet s w ⟨i.val-1,by omega⟩) := dite_eq_right hi
    have hh := congrArg (fun c : BooleanNetwork k w => c.net.count) he
    rw [hh,count_comp,blockNet_count]
    omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlBounds
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

lemma properOn_count {k w : ℕ} (m d : BooleanNetwork k w) :
    (properOn m d).net.count ≤ 2*m.net.count+3*d.net.count+216*w*w+250*w+45 := by
  have h1 := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 1)) d
  have h2 := wordLt_count d m
  have h3 := zeroWord_count ((m.pair d).comp (mod w))
  have h4 := mod_count w
  simp only [wordConstant_count] at h1
  simp only [count_comp,count_pair] at h3
  simp only [properOn,count_band]
  omega

namespace NodeCircuit

lemma popped_count (s w : ℕ) : (popped s w).net.count ≤ (s+1)*w*w := by
  simpa only [popped,count_comp,pending_count,zero_add] using stackPop_count (s+1) w
lemma quotient_count (s w : ℕ) : (quotient s w).net.count ≤ quotientBound w := by
  simpa only [quotient,quotientBound,count_comp,count_pair,top_count,divisor_count,zero_add]
    using div_count w
lemma isPrime_count (s w : ℕ) : (isPrime s w).net.count ≤ primeBound w := by
  simpa only [isPrime,primeBound,count_comp,top_count,zero_add] using primeWord_count w
lemma isDone_count (s w : ℕ) : (isDone s w).net.count ≤ 97*w+21 := by
  simpa only [isDone,top_count,zero_add] using zeroWord_count (top s w)
lemma isProper_count (s w : ℕ) : (isProper s w).net.count ≤ guardBound w := by
  simpa only [isProper,guardBound,top_count,divisor_count,mul_zero,zero_add] using
    properOn_count (top s w) (divisor s w)
lemma split_count (s w : ℕ) : (split s w).net.count ≤ splitBound s w := by
  have h1 := stackPush_count (quotient s w) (popped s w)
  have h2 := stackPush_count (divisor s w) (stackPush (quotient s w) (popped s w))
  rw [divisor_count,zero_add] at h2
  exact h2.trans (Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _
    (Nat.add_le_add (quotient_count s w) (popped_count s w)))))
lemma next_count (s w : ℕ) : (next s w).net.count ≤ nextBound s w := by
  have h1 := isDone_count s w
  have h2 := isPrime_count s w
  have h3 := isProper_count s w
  have h4 := popped_count s w
  have h5 := split_count s w
  simp only [next,wordMux_count,pending_count]
  dsimp only [nextBound]
  omega
lemma emitted_count (s w : ℕ) : (emitted s w).net.count ≤ primeBound w+8*w := by
  have h := isPrime_count s w
  simp only [emitted,wordMux_count,top_count,wordConstant_count]
  omega
lemma failed_count (s w : ℕ) : (failed s w).net.count ≤ 97*w+21+primeBound w+guardBound w+5 := by
  have h1 := isDone_count s w
  have h2 := isPrime_count s w
  have h3 := isProper_count s w
  simp only [failed,count_band,count_bnot]
  omega

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SplitDecoderPolynomial
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace BitArithmetic
lemma firstProperNet_count {k w c : ℕ} (m : BooleanNetwork k w)
    (ds : List (BooleanNetwork k w)) (h : ∀d∈ds,d.net.count ≤ c) :
    (firstProperNet m ds).net.count≤w+ds.length*(2*m.net.count+4*c+216*w*w+257*w+45) := by
  induction ds with
  | nil=>simp only [firstProperNet,wordConstant_count,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons d ds ih=>
    have hd:=h d (by simp)
    have ht:=ih (fun e he=>h e (by simp [he]))
    have hp:=properOn_count m d
    simp only [firstProperNet,wordMux_count,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
end BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a w e : α→ℕ}
lemma addNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.add (w x)) :=
  of_le (((PolyAt.const len 86).mul hw).add (PolyAt.const len 6)) fun x=>add_count (w x)
lemma subNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.sub (w x)) :=
  of_le (((PolyAt.const len 158).mul hw).add (PolyAt.const len 6)) fun x=>sub_count (w x)
lemma divNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.div (w x)) :=
  of_le (((((PolyAt.const len 216).mul hw).mul hw).add ((PolyAt.const len 56).mul hw)).add
    (PolyAt.const len 6)) fun x=>div_count (w x)
lemma modNet (hw : PolyAt len w) : NetworkAt len (fun x=>BitArithmetic.mod (w x)) :=
  of_le (((((PolyAt.const len 216).mul hw).mul hw).add ((PolyAt.const len 56).mul hw)).add
    (PolyAt.const len 6)) fun x=>mod_count (w x)
lemma properOn {m d : ∀x,BooleanNetwork (a x) (w x)}
    (hm : NetworkAt len m) (hd : NetworkAt len d) (hw : PolyAt len w) :
    NetworkAt len (fun x=>BitArithmetic.properOn (m x) (d x)) :=
  of_le ((((((PolyAt.const len 2).mul hm).add ((PolyAt.const len 3).mul hd)).add
    (((PolyAt.const len 216).mul hw).mul hw)).add ((PolyAt.const len 250).mul hw)).add
    (PolyAt.const len 45)) fun x=>properOn_count (m x) (d x)
lemma evenOn {m : ∀x,BooleanNetwork (a x) (w x)} (hm : NetworkAt len m) (hw : PolyAt len w) :
    NetworkAt len (fun x=>BitArithmetic.evenOn (m x)) :=
  ((hm.pair (wordConstant _ hw)).comp (modNet hw)).zeroWord hw
lemma halfWord {m : ∀x,BooleanNetwork (a x) (w x)} (hm : NetworkAt len m) (hw : PolyAt len w) :
    NetworkAt len (fun x=>BitArithmetic.halfWord (m x)) :=
  (hm.pair (wordConstant _ hw)).comp (divNet hw)
lemma halfPowerBits {b m : ∀x,BooleanNetwork (a x) (w x)} {d : ∀x,BooleanNetwork (a x) (e x)}
    (hb : NetworkAt len b) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hw : PolyAt len w) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.halfPowerBits (b x) (m x) (d x)) :=
  ((hb.pair hm).pair ((hd.halfWord he).rewire _)).comp (modularPower hw he)
lemma shiftedHalfBits {b m : ∀x,BooleanNetwork (a x) (w x)} {d : ∀x,BooleanNetwork (a x) (e x)}
    (hb : NetworkAt len b) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hw : PolyAt len w) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.shiftedHalfBits (b x) (m x) (d x)) :=
  ((((hb.halfPowerBits hm hd hw he).pair hm).comp (addNet hw)).pair
    (wordConstant _ hw)).comp (subNet hw)
lemma candidateBits {b m : ∀x,BooleanNetwork (a x) (w x)} {d : ∀x,BooleanNetwork (a x) (e x)}
    (hb : NetworkAt len b) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hw : PolyAt len w) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.candidateBits (b x) (m x) (d x)) :=
  (((hd.zeroWord he).bnot).band (hd.evenOn he)).wordMux
    (((hb.shiftedHalfBits hm hd hw he).pair hm).comp (gcdNet hw)) (wordConstant _ hw) hw
lemma firstProperNet {m : ∀x,BooleanNetwork (a x) (w x)} {ds : ∀x,List (BooleanNetwork (a x) (w x))}
    (hm : NetworkAt len m) (hw : PolyAt len w) (hL : PolyAt len (fun x=>(ds x).length))
    (h : ∃p : Polynomial ℕ,∀x d,d∈ds x → d.net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>BitArithmetic.firstProperNet (m x) (ds x)) := by
  obtain ⟨p,hp⟩:=h
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply of_le (hw.add (hL.mul ((((((PolyAt.const len 2).mul hm).add ((PolyAt.const len 4).mul hc)).add
    (((PolyAt.const len 216).mul hw).mul hw)).add ((PolyAt.const len 257).mul hw)).add
    (PolyAt.const len 45))))
  exact fun x=>firstProperNet_count (m x) (ds x) (hp x)
lemma rootOn {n : α→ℕ} {m : ∀x,BooleanNetwork (a x) (n x+1)} (hm : NetworkAt len m)
    (hn : PolyAt len n) (he : PolyAt len e) :
    NetworkAt len (fun x=>BitArithmetic.rootOn (n x) (e x) (m x)) := by
  have hr : PolyAt len (fun x=>rootWidth (n x)) := by unfold rootWidth;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  have hw:=hn.add (PolyAt.const len 1)
  exact ((hm.comp (resizeWord hw hr)).comp (boundedRootNet hn he)).comp (resizeWord hr hw)
lemma rootsOn {n : α→ℕ} {m : ∀x,BooleanNetwork (a x) (n x+1)} (hm : NetworkAt len m)
    (hn : PolyAt len n) : NetworkAt len (fun x=>BitArithmetic.rootsOn (n x) (m x)) := by
  let ix:=Σx:α,Fin (n x+1)
  have he : PolyAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val) :=
    (hn.add (PolyAt.const len 1) |>.pull Sigma.fst).of_le fun xi=>Nat.le_of_lt xi.2.isLt
  obtain ⟨p,hp⟩:=(hm.pull (Sigma.fst (β:=fun x=>Fin (n x+1)))).rootOn (hn.pull Sigma.fst) he
  apply firstProperNet hm (hn.add (PolyAt.const len 1))
    (by simpa only [List.length_map,List.length_range] using hn.add (PolyAt.const len 1))
  refine ⟨p,?_⟩
  intro x d hd
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hd
  exact hp ⟨x,⟨e,List.mem_range.mp he⟩⟩
end NetworkAt
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ActualDivisorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace FixedSplit
lemma actualBaseNet_poly : NetworkAt (fun xi:Σn,Fin (n^5)=>xi.1) (fun xi=>actualBaseNet xi.2) := by
  simpa only [NetworkAt,actualBaseNet,count_comp,launchWires,count_select,Nat.zero_add,
    baseNet_count] using PolyAt.ofPoly PreparationPolynomial.listOutput (fun xi:Σn,Fin (n^5)=>xi.1)
lemma modulusNet_poly : NetworkAt id modulusNet :=
  (NetworkAt.select _).comp (NetworkAt.select _)
lemma actualOrderRawNet_poly : NetworkAt (fun xi:Σn,Fin (n^5)=>xi.1) (fun xi=>actualOrderRawNet xi.2) :=
  (NetworkAt.select _).comp (NetworkAt.select _)
lemma actualOrderNet_poly : NetworkAt (fun xi:Σn,Fin (n^5)=>xi.1) (fun xi=>actualOrderNet xi.2) :=
  OrderSlots.outputOn_poly actualBaseNet_poly (modulusNet_poly.pull Sigma.fst) actualOrderRawNet_poly
lemma liftedModulus_poly : NetworkAt id liftedModulus :=
  modulusNet_poly.comp (NetworkAt.resizeWord (PolyAt.self id) ((PolyAt.self id).add (PolyAt.const id 1)))
lemma roots_poly : NetworkAt id (fun n=>rootsOn n (liftedModulus n)) :=
  liftedModulus_poly.rootsOn (PolyAt.self id)
lemma ordersBits_poly : NetworkAt id (fun n=>ordersBits (liftedModulus n) (actualPairs n)) := by
  let len : (Σn,Fin (n^5))→ℕ:=Sigma.fst
  have hn:=PolyAt.self len
  have hw:=hn.add (PolyAt.const len 1)
  have hm:=liftedModulus_poly.pull (Sigma.fst (β:=fun n=>Fin (n^5)))
  have he:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  obtain ⟨p,hp⟩:=((actualBaseNet_poly.comp (NetworkAt.resizeWord hn hw)).candidateBits hm
    actualOrderNet_poly hw he)
  apply NetworkAt.firstProperNet liftedModulus_poly
    ((PolyAt.self id).add (PolyAt.const id 1))
    (by simpa only [actualPairs,List.length_map,List.length_ofFn,id_eq] using (PolyAt.self (id : ℕ→ℕ)).pow 5)
  refine ⟨p,?_⟩
  intro n d hd
  obtain ⟨ar,har,rfl⟩:=List.mem_map.mp hd
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp har
  exact hp ⟨n,i⟩
lemma divisorNet_poly : NetworkPoly divisorNet := by
  have hn:=PolyAt.self (id : ℕ→ℕ)
  have hw:=hn.add (PolyAt.const id 1)
  exact (liftedModulus_poly.evenOn hw).wordMux (NetworkAt.wordConstant _ hw)
    ((liftedModulus_poly.properOn roots_poly hw).wordMux roots_poly ordersBits_poly hw) hw
end FixedSplit
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimeComponentCircuit
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

lemma primeComponent_count {k n c : ℕ} (m p : BooleanNetwork k n)
    (hm : m.net.count ≤ c) (hp : p.net.count ≤ c) :
    (primeComponent m p).net.count≤primeComponentBound n c := by
  have hr:=resizeWord_count n (componentWidth n)
  have hr':=resizeWord_count (componentWidth n) n
  have hprod:=productNet_count (List.replicate n (p.comp (resizeWord n (componentWidth n))))
    (c:=c+componentWidth n) (by
      intro q hq
      have he:=(List.mem_replicate.mp hq).2
      subst q
      rw [count_comp]
      omega)
  have hg:=gcdNet_count (componentWidth n)
  simp only [List.length_replicate] at hprod
  simp only [primeComponent,count_comp,count_pair]
  dsimp only [primeComponentBound]
  omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalMachine
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma width_eq (t : ℕ) : M.width t=c+t*(FixedSplit.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [width]
  | succ t ih=>simp only [width,ih];ring

lemma program_length (t : ℕ) : (M.program t).length≤
    t*(4*M.initWork+2*FixedSplit.width n+(FixedSplit.program n).length+4*M.updateWork+2*c) := by
  induction t with
  | zero=>simp [program]
  | succ t ih=>
    have hp := appendPrepared_length (M.program t) (M.initNet t) (M.initNet_count t).le (FixedSplit.program n)
    have hu := oracleOn_length (M.updateNet t) (M.updateNet_count t).le
    simp only [M.initNet_count] at hp
    simp only [M.updateNet_count] at hu
    simp only [program,List.length_append,firstProgram_length]
    rw [Nat.succ_mul]
    omega

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MachineInitialization
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

lemma initialNet_count (t : ℕ) : (M.initialNet t).net.count=
    t*(FixedSplit.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [initialNet, count_select]
  | succ t ih=>
    simp only [initialNet,packNet_count,Completion.zeros_count,ih]
    ring

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeMachine
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma width_eq (t : ℕ) : M.width t=c+t*(NodeKernel.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [width]
  | succ t ih=>simp only [width,ih];ring

lemma program_length (t : ℕ) : (M.program t).length≤
    t*(4*M.initWork+2*NodeKernel.width n+(NodeKernel.program n).length+4*M.updateWork+2*c) := by
  induction t with
  | zero=>simp [program]
  | succ t ih=>
    have hp := appendPrepared_length (M.program t) (M.initNet t) (M.initNet_count t).le (NodeKernel.program n)
    have hu := oracleOn_length (M.updateNet t) (M.updateNet_count t).le
    simp only [M.initNet_count] at hp
    simp only [M.updateNet_count] at hu
    simp only [program,List.length_append,firstProgram_length]
    rw [Nat.succ_mul]
    omega

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SortingCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma keepHead_count {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r)) :
    (keepHead c).net.count=c.net.count := by
  simp only [keepHead,count_pair,count_comp,headNet,tailNet,count_select,zero_add]

lemma compareStep_count (w r : ℕ) : (compareStep w r).net.count ≤ 498*w+114 := by
  have hp := paddedPair_count (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))
  simp only [headNet,tailNet,count_comp,count_select,mul_zero,zero_add] at hp
  simp only [compareStep,count_pair,wordMux_count,headNet,tailNet,count_comp,count_select]
  omega

lemma insertNet_count (w r : ℕ) : (insertNet w r).net.count ≤ r*(498*w+114) := by
  induction r with
  | zero=>simp [insertNet,count_select]
  | succ r ih=>
    have hc := compareStep_count w r
    rw [insertNet,count_comp,keepHead_count,Nat.succ_mul]
    omega
/-- Quadratic number of word comparisons, each a polynomial Boolean network.
No expanded sorting expression duplicates its recursively generated circuits. -/
theorem sortNet_count (w r : ℕ) : (sortNet w r).net.count ≤ r*r*(498*w+114) := by
  induction r with
  | zero=>simp [sortNet,count_select]
  | succ r ih=>
    have hc := insertNet_count w r
    rw [sortNet,count_comp,keepHead_count]
    calc
      _ ≤ r*r*(498*w+114)+r*(498*w+114) := Nat.add_le_add ih hc
      _ ≤ (r+1)*(r+1)*(498*w+114) := by nlinarith

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeHistoryAccess
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

lemma firstNodeNet_count (t : ℕ) : (M.firstNodeNet t).net.count=0 := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [firstNodeNet,count_comp,previousNet,count_comp,count_select,ih,add_zero]

end NodeMachine
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

lemma dividesOn_count {k n : ℕ} (p m : BooleanNetwork k n) :
    (dividesOn p m).net.count ≤ p.net.count+m.net.count+216*n*n+154*n+27 := by
  have hh:=zeroWord_count ((m.pair p).comp (mod n))
  have hd:=mod_count n
  simp only [count_comp,count_pair] at hh
  exact hh.trans (by omega)

lemma leastDivisorTest_count {k n c : ℕ} (ps : List (BooleanNetwork k n))
    (m p : BooleanNetwork k n) (hps : ∀ q∈ps,q.net.count ≤ c)
    (hm : m.net.count ≤ c) (hp : p.net.count ≤ c) :
    (leastDivisorTest ps m p).net.count≤ps.length*(4*c+216*n*n+202*n+42)+1 := by
  have hh:=all_count (ps.map (fun q=>(dividesOn q m).bnot.bor (wordLe p q)))
    (c:=4*c+216*n*n+202*n+41) (by
      intro b hb
      obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hb
      have hd:=dividesOn_count q m
      have hl:=wordLe_count p q
      have hqc:=hps q hq
      simp only [count_bor,count_bnot]
      omega)
  change (all (ps.map (fun q=>(dividesOn q m).bnot.bor (wordLe p q)))).net.count ≤ _
  simp only [List.length_map] at hh
  omega

lemma componentCongruence_count {k n c : ℕ} (ps : List (BooleanNetwork k n))
    (a m p : BooleanNetwork k n) (hps : ∀ q∈ps,q.net.count ≤ c)
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hp : p.net.count ≤ c) :
    (componentCongruence ps a m p).net.count ≤ componentCongruenceBound n ps.length c := by
  have hq:=primeComponent_count m p hm hp
  have hl:=leastDivisorTest_count ps m p hps hm hp
  have he:=equalOn_count ((a.pair (primeComponent m p)).comp (mod n))
    (wordMux (leastDivisorTest ps m p) (wordConstant (BitVec.ofNat n 1))
      (natSubOn (primeComponent m p) (wordConstant (BitVec.ofNat n 1))))
  have hs:=natSubOn_count (primeComponent m p) (wordConstant (BitVec.ofNat n 1))
  have hd:=mod_count n
  simp only [count_comp,count_pair,wordMux_count,wordConstant_count] at he hs
  change (equalOn _ _).net.count≤_
  dsimp only [componentCongruenceBound]
  omega

lemma tableCanonicalNet_count {k n c : ℕ} (ps : List (BooleanNetwork k n))
    (a m : BooleanNetwork k n) (hps : ∀ q∈ps,q.net.count ≤ c)
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) :
    (tableCanonicalNet ps a m).net.count≤tableCanonicalBound n ps.length c := by
  have hl:=wordLt_count a m
  have hall:=all_count (ps.map (fun p=>(dividesOn p m).bnot.bor (componentCongruence ps a m p)))
    (c:=2*c+216*n*n+154*n+32+componentCongruenceBound n ps.length c) (by
      intro b hb
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hb
      have hc:=componentCongruence_count ps a m p hps ha hm (hps p hp)
      have hd:=dividesOn_count p m
      have hp':=hps p hp
      simp only [count_bor,count_bnot]
      omega)
  simp only [List.length_map] at hall
  have hr : 2*c+216*n*n+154*n+32+componentCongruenceBound n ps.length c+1 =
      2*c+216*n*n+154*n+33+componentCongruenceBound n ps.length c := by omega
  rw [hr] at hall
  simp only [tableCanonicalNet,count_band,tableCanonicalBound]
  omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ChildQueueBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
open BooleanNetwork

lemma wordMember_count {k w c : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (wordMember a as).net.count ≤ as.length*(2*c+96*w+25)+1 := by
  have h := any_count (as.map (fun b=>(a.pair b).comp (wordEq w))) (c:=2*c+96*w+21) (by
    intro d hd
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hd
    have hh := hs b hb
    have he := wordEq_count w
    simp only [count_comp,count_pair]
    omega)
  simpa only [wordMember,List.length_map,Nat.add_assoc] using h

lemma active_count {k w c : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (active a as).net.count ≤ c+49*w+11+as.length*(2*c+96*w+25) := by
  have hm := wordMember_count a as ha hs
  have hl := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 2)) a
  rw [wordConstant_count] at hl
  simp only [active,count_band,count_bnot]
  omega

lemma pushOne_count {k w c : ℕ} (s : ℕ) (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (pushOne s a as).net.count ≤ oneBound s w c as.length := by
  have hac := active_count a as ha hs
  have hsub := sub_count w
  have hh : ((((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))).net.count ≤
      c+159*w+6 := by
    simp only [count_comp,count_pair,liftWord,source,count_select,zero_add,wordConstant_count]
    omega
  have hpush := stackPush_count (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))
    (queue k s w)
  simp only [queue,count_select,add_zero] at hpush
  have hpush' := hpush.trans (Nat.mul_le_mul_left (s*w) hh)
  simp only [pushOne,count_pair,wordMux_count,count_comp,source,queue,count_select,zero_add,add_zero]
  dsimp only [oneBound]
  omega

lemma oneBound_mono (s w c : ℕ) {r t : ℕ} (h : r ≤ t) : oneBound s w c r ≤ oneBound s w c t := by
  have hh := Nat.mul_le_mul_right (2*c+96*w+25) h
  dsimp only [oneBound]
  omega

/-- The all-child queue update is quadratic in the number of prime fields,
not an exponentially duplicated expression. Bounds hold on ALL inputs. -/
theorem pushAll_count {k w c : ℕ} (s : ℕ) (as : List (BooleanNetwork k w))
    (hs : ∀ b∈as,b.net.count ≤ c) :
    (pushAll s as).net.count ≤ as.length*oneBound s w c as.length := by
  induction as with
  | nil=>simp [pushAll,count_select]
  | cons a as ih=>
    have ha := hs a (by simp)
    have ht : ∀ b∈as,b.net.count ≤ c := fun b hb=> hs b (by simp [hb])
    have hi := ih ht
    have hp := pushOne_count s a as ha ht
    have hb := oneBound_mono s w c (Nat.le_succ as.length)
    simp only [pushAll,count_comp,List.length_cons]
    calc
      _ ≤ as.length*oneBound s w c as.length+oneBound s w c as.length := Nat.add_le_add hi hp
      _ ≤ as.length*oneBound s w c (as.length+1)+oneBound s w c (as.length+1) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hb) hb
      _ = _ := by ring

end ExactQuantumFactoring.BitArithmetic.ChildQueue


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TwoAdicCircuit
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

lemma bequiv_count {k : ℕ} (a b : BooleanNetwork k 1) :
    (bequiv a b).net.count=2*a.net.count+2*b.net.count+9 := by
  simp only [bequiv,count_bnot,count_bxor]

lemma sameTwoVal_count {k n : ℕ} (a b : BooleanNetwork k n) :
    (sameTwoVal a b).net.count≤n*(2*a.net.count+2*b.net.count+864*n*n+616*n+118)+1 := by
  have hh:=all_count (List.ofFn (fun i : Fin n=>bequiv (a.comp (dividesNet n (2^i.val)))
    (b.comp (dividesNet n (2^i.val)))) )
    (c:=2*a.net.count+2*b.net.count+864*n*n+616*n+117) (by
      intro c hc
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc
      have hd:=dividesNet_count n (2^i.val)
      simp only [bequiv_count,count_comp]
      nlinarith)
  change (all _).net.count≤_
  simp only [List.length_ofFn] at hh
  have hr : 2*a.net.count+2*b.net.count+864*n*n+616*n+117+1=
      2*a.net.count+2*b.net.count+864*n*n+616*n+118 := by omega
  rwa [hr] at hh
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ClosedLevelCircuit
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

lemma oddPartNet_count {k n c : ℕ} (a : BooleanNetwork k n) (ha : a.net.count ≤ c) :
    (oddPartNet a).net.count≤oddPartBound n c := by
  have hp:=primeComponent_count a (wordConstant (BitVec.ofNat n 2))
    (c:=c+n) (by omega) (by rw [wordConstant_count];omega)
  have hd:=div_count n
  simp only [oddPartNet,count_comp,count_pair]
  dsimp only [oddPartBound]
  omega

lemma closedLevelNet_count {k n c : ℕ} (a : BooleanNetwork k n) (ha : a.net.count ≤ c) (t : ℕ) :
    (closedLevelNet a t).net.count ≤ closedLevelBound n c := by
  have ho:=oddPartNet_count a ha
  have hd:=dividesNet_count n (2^t)
  have hm:=mul_count n
  rw [closedLevelNet]
  by_cases ht : t=0
  · rw [ite_eq_left ht]
    dsimp only [closedLevelBound];omega
  · rw [ite_eq_right ht]
    by_cases htn : t<n
    · rw [ite_eq_left htn,wordMux_count,count_comp,count_comp,count_pair,
        wordConstant_count,wordConstant_count]
      dsimp only [closedLevelBound]
      nlinarith
    · rw [ite_eq_right htn,wordConstant_count]
      dsimp only [closedLevelBound]
      omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalHeightResources
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
lemma nat_size_mul_le (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.size_le.mp (le_refl b.size)).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.size_le.mp (le_refl a.size)) (by positivity))
lemma nat_size_add_le (a b : ℕ) : (a+b).size ≤ a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha : a<2^(a.size+b.size) :=
    (Nat.size_le.mp (le_refl a.size)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hb : b<2^(a.size+b.size) :=
    (Nat.size_le.mp (le_refl b.size)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  rw [pow_succ]
  omega
lemma nat_size_pow_le (a k : ℕ) : (a^k).size ≤ k*a.size+1 := by
  apply Nat.size_le.mpr
  have h : a^k ≤ (2^a.size)^k := Nat.pow_le_pow_left (Nat.size_le.mp (le_refl a.size)).le k
  rw [← pow_mul,Nat.mul_comm a.size] at h
  rw [pow_succ]
  have hp : 0<2^(k*a.size) := by positivity
  omega

namespace PolyBound
lemma sizeMul {f g : ℕ → ℕ} (hf : PolyBound (fun n => (f n).size))
    (hg : PolyBound (fun n => (g n).size)) : PolyBound (fun n => (f n*g n).size) :=
  (hf.add hg).of_le (fun n => nat_size_mul_le (f n) (g n))
lemma sizeAdd {f g : ℕ → ℕ} (hf : PolyBound (fun n => (f n).size))
    (hg : PolyBound (fun n => (g n).size)) : PolyBound (fun n => (f n+g n).size) :=
  ((hf.add hg).add (const 1)).of_le (fun n => nat_size_add_le (f n) (g n))
lemma sizePow {f g : ℕ → ℕ} (hf : PolyBound (fun n => (f n).size))
    (hg : PolyBound g) : PolyBound (fun n => (f n^g n).size) :=
  ((hg.mul hf).add (const 1)).of_le (fun n => nat_size_pow_le (f n) (g n))
end PolyBound

namespace RatHeightPoly
variable {a b : ℕ → ℚ}
lemma constant (q : ℚ) : RatHeightPoly (fun _=>q) := ⟨PolyBound.const _,PolyBound.const _⟩
lemma intCast {f : ℕ → ℤ} (hf : PolyBound (fun n=>(f n).natAbs.size)) :
    RatHeightPoly (fun n => (f n : ℚ)) := by
  constructor
  · simpa using hf
  · exact PolyBound.of_le (PolyBound.const 1) (fun n => by simp)
lemma add (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n+b n) := by
  constructor
  · apply ((ha.1.sizeMul hb.2).sizeAdd (hb.1.sizeMul ha.2)).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.num_add]
    apply (Int.natAbs_ediv_le_natAbs _ _).trans
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using
      (Int.natAbs_add_le ((a n).num*(b n).den) ((b n).num*(a n).den))
  · apply (ha.2.sizeMul hb.2).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.den_add]
    exact Nat.div_le_self _ _
lemma neg (ha : RatHeightPoly a) : RatHeightPoly (fun n=> -(a n)) := by
  constructor
  · simpa only [Rat.neg_num,Int.natAbs_neg] using ha.1
  · simpa only [Rat.neg_den] using ha.2
lemma sub (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n-b n) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg
lemma mul (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n*b n) := by
  constructor
  · apply (ha.1.sizeMul hb.1).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.mul_num]
    convert Int.natAbs_ediv_le_natAbs ((a n).num*(b n).num) _ using 1
    all_goals try with_reducible_and_instances rfl
    exact (Int.natAbs_mul _ _).symm
  · apply (ha.2.sizeMul hb.2).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.mul_den]
    exact Nat.div_le_self _ _
lemma inv (ha : RatHeightPoly a) : RatHeightPoly (fun n=>(a n)⁻¹) := by
  constructor
  · apply ha.2.of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_sign]
    split_ifs <;> simp
  · apply (ha.1.add (PolyBound.const 1)).of_le
    intro n
    rw [Rat.den_inv]
    split_ifs
    · simp only [Nat.size_one]; omega
    · omega
lemma div (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n/b n) := by
  simpa only [div_eq_mul_inv] using ha.mul hb.inv
lemma pow {f : ℕ→ℕ} (ha : RatHeightPoly a) (hf : PolyBound f) :
    RatHeightPoly (fun n=>(a n)^(f n)) := by
  constructor
  · simpa only [Rat.num_pow,Int.natAbs_pow] using ha.1.sizePow hf
  · simpa only [Rat.den_pow] using ha.2.sizePow hf
end RatHeightPoly
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_VerifiedTreeBounds
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
lemma resultField_count (n : ℕ) (i : Fin n) : (resultField n i).net.count≤n := by
  have h:=resizeWord_count (n+1) n
  simpa only [resultField,count_comp,NodeStateCircuit.output,count_select,blockNet,count_vector,
    Nat.zero_add] using h
lemma sortedOutput_count (n : ℕ) : (sortedOutput n).net.count ≤ resultBound n := by
  have h₁:=tensorNetwork_count_le (resultField n) (resultField_count n)
  have h₂:=SortedWords.sortNet_count n n
  simp only [sortedOutput,count_comp]
  unfold resultBound
  omega
end PhysicalNode
namespace PhysicalTree
lemma nodeResult_count (n : ℕ) : (nodeResult n).net.count≤PhysicalNode.resultBound n := by
  have h:=PhysicalNode.sortedOutput_count n
  simpa only [nodeResult,count_comp,SplitMachine.currentNet,count_select,Nat.zero_add] using h
lemma resultFields_count (n : ℕ) (i : Fin n) : (resultFields n i).net.count≤PhysicalNode.resultBound n := by
  simpa only [resultFields,count_comp,tensorSelect,count_select,Nat.add_zero] using nodeResult_count n
end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
lemma previousNet_count (t : ℕ) : (M.previousNet t).net.count=0 := by
  simp only [previousNet,count_comp,count_select,Nat.add_zero]
lemma lastNodeNet_count (t : ℕ) : (M.lastNodeNet t).net.count=0 := by
  simp only [lastNodeNet,count_comp,count_select,Nat.add_zero]
lemma rowQuery_count (t : ℕ) : (M.rowQuery t).net.count=M.query.net.count := by
  simp only [rowQuery,count_comp,M.previousNet_count,currentNet,count_select,Nat.zero_add]
lemma rowFields_count (t : ℕ) (i : Fin n) :
    (M.rowFields t i).net.count≤PhysicalNode.resultBound n := by
  simpa only [rowFields,count_comp,M.lastNodeNet_count,Nat.zero_add] using
    PhysicalTree.resultFields_count n i
lemma rowVerifiedNet_count (t : ℕ) : (M.rowVerifiedNet t).net.count≤M.rowBound := by
  have h₁:=zeroWord_count (M.rowQuery t)
  have h₂:=factorVerifierOn_count (M.rowQuery t) (M.rowFields t)
    (c:=M.query.net.count+PhysicalNode.resultBound n) (by rw [M.rowQuery_count];omega)
    (by intro i;exact (M.rowFields_count t i).trans (Nat.le_add_left _ _))
  rw [M.rowQuery_count] at h₁
  simp only [rowVerifiedNet,count_bor]
  unfold rowBound
  omega
lemma verifiedNet_count (t : ℕ) : (M.verifiedNet t).net.count≤t*(M.rowBound+1)+1 := by
  induction t with
  | zero=>simp only [verifiedNet,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ t ih=>
    have h:=M.rowVerifiedNet_count t
    simp only [verifiedNet,count_band,count_comp,M.previousNet_count,Nat.zero_add]
    nlinarith
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

lemma logNets_length (t : ℕ) : (M.logNets t).length=t := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [logNets,List.length_cons,List.length_map,ih]

lemma logNets_counts (t : ℕ) : ∀ r∈M.logNets t,
    r.1.net.count≤M.query.net.count ∧ r.2.net.count≤PhysicalNode.resultBound n := by
  induction t with
  | zero=>simp only [logNets,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ t ih=>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨(M.rowQuery_count t).le,?_⟩
      simpa only [count_comp,M.lastNodeNet_count,Nat.zero_add] using PhysicalTree.nodeResult_count n
    · change r ∈ (M.logNets t).map (fun a=>((M.previousNet t).comp a.1,
        (M.previousNet t).comp a.2)) at hr
      obtain ⟨a,ha,he⟩:=List.mem_map.mp hr
      subst r
      simpa only [count_comp,M.previousNet_count,Nat.zero_add] using ih a ha

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableOrderCircuit
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

lemma tableFactor_count {k n : ℕ} (label p : BooleanNetwork k n) :
    (tableFactor label p).net.count≤label.net.count+2*p.net.count+220*n+50 := by
  have hl:=zeroWord_count label
  have hp:=zeroWord_count p
  simp only [tableFactor,wordMux_count,count_bor,wordConstant_count]
  omega

lemma tableNets_counts {k n c : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n)))
    (hc : ∀ r∈rows,r.1.net.count ≤ c ∧ ∀ p∈r.2,p.net.count ≤ c) :
    ∀ p∈tableNets rows,p.net.count≤3*c+220*n+50 := by
  intro p hp
  obtain ⟨r,hr,hp⟩:=List.mem_flatMap.mp hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  have H:=hc r hr
  have Hq:=H.2 q hq
  exact (tableFactor_count r.1 q).trans (by omega)

lemma orderFromList_count {k w c : ℕ} (a m : BooleanNetwork k w)
    (qs : List (BooleanNetwork k w)) (ha : a.net.count ≤ c) (hm : m.net.count ≤ c)
    (hq : ∀ q∈qs,q.net.count ≤ c) :
    (orderFromList a m qs).net.count≤
      qs.length*(c+90*w*w+14*w+6+stripStepBound w c)+w := by
  have hp:=productNet_count qs hq
  have hs:=stripScan_count a m qs ha hm hq
  simp only [orderFromList,count_comp,count_pair,count_select,zero_add,Nat.add_zero]
  nlinarith

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

lemma tableOrderPrimes_length {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    (tableOrderPrimes rows).length=n*(tableNets rows).length := by
  simp only [tableOrderPrimes,List.length_flatten,List.map_replicate,List.length_map,
    List.sum_replicate,smul_eq_mul]

lemma tableOrder_count {k n c : ℕ} (a m : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n)))
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c)
    (hr : ∀ r∈rows,r.1.net.count ≤ c ∧ ∀ p∈r.2,p.net.count ≤ c) :
    (tableOrder a m rows).net.count ≤ tableOrderBound n (tableNets rows).length c := by
  let w:=tableOrderWidth n (tableNets rows).length
  let C:=3*c+220*n+50+w
  have hres:=resizeWord_count n w
  have hp : ∀ p∈tableOrderPrimes rows,p.net.count ≤ C := by
    intro p hp
    obtain ⟨ps,hps,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hps).2
    subst ps
    obtain ⟨r,hr',rfl⟩:=List.mem_map.mp hp
    have H:=tableNets_counts rows hr r hr'
    rw [count_comp]
    exact Nat.add_le_add H hres
  have hs:=orderFromList_count (a.comp (resizeWord n w)) (m.comp (resizeWord n w))
    (tableOrderPrimes rows) (c:=C)
    (by rw [count_comp];dsimp [C];omega)
    (by rw [count_comp];dsimp [C];omega) hp
  rw [tableOrderPrimes_length] at hs
  have hsmall:=resizeWord_count w n
  change _ ≤ _+n
  simp only [tableOrder,count_comp]
  exact Nat.add_le_add hs hsmall

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

lemma fieldRows_counts (t : ℕ) : ∀ r∈M.fieldRows t,
    r.1.net.count ≤ M.query.net.count ∧ ∀ p∈r.2,p.net.count ≤ PhysicalNode.resultBound n := by
  intro r hr
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr
  have hh:=M.logNets_counts t a ha
  refine ⟨hh.1,?_⟩
  intro p hp
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp
  simpa only [count_comp,tensorSelect,count_select,Nat.add_zero] using hh.2

lemma fieldRows_table_length (t : ℕ) : (tableNets (M.fieldRows t)).length=t*n := by
  have h : ∀ a : BooleanNetwork (M.width t) n×BooleanNetwork (M.width t) (tensorWidth n n),
      (List.ofFn (fun i : Fin n => tableFactor a.1 (a.2.comp (tensorSelect n n i)))).length=n :=
    fun _=>List.length_ofFn
  simp only [tableNets,fieldRows,List.flatMap_map,Function.comp_def,List.map_ofFn,
    List.length_flatMap]
  simp only [h,List.map_const',List.sum_replicate,smul_eq_mul,M.logNets_length]

lemma retainedOrder_count {b : ℕ} (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (ha : a.net.count ≤ b) (hm : m.net.count ≤ b)
    (hq : M.query.net.count ≤ b) (hr : PhysicalNode.resultBound n ≤ b) :
    (M.retainedOrder t a m).net.count ≤ tableOrderBound n (t*n) b := by
  have hh:=tableOrder_count a m (M.fieldRows t) ha hm (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  rwa [M.fieldRows_table_length] at hh

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

lemma retainedCanonical_count {b : ℕ} (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (ha : a.net.count≤b) (hm : m.net.count≤b)
    (hq : M.query.net.count≤b) (hr : PhysicalNode.resultBound n≤b) :
    (M.retainedCanonical t a m).net.count≤tableCanonicalBound n (t*n) (3*b+220*n+50) := by
  have hf:=tableNets_counts (M.fieldRows t) (c:=b) (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  have h:=tableCanonicalNet_count (tableNets (M.fieldRows t)) a m hf
    (ha.trans (by omega)) (hm.trans (by omega))
  rwa [M.fieldRows_table_length] at h
end NodeMachine

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TotientCircuit
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

lemma totientPair_count {k w c : ℕ} (q v a : BooleanNetwork k w)
    (hq : q.net.count ≤ c) (hv : v.net.count ≤ c) (ha : a.net.count ≤ c) :
    (totientPair q v a).net.count ≤ totientStepBound w c := by
  have hd := div_count w
  have hm := mod_count w
  have hmul := mul_count w
  have hzero := zeroWord_count ((v.pair q).comp (mod w))
  have hz := zeroWord_count ((((v.pair q).comp (div w)).pair q).comp (mod w))
  have hs := natSubOn_count q (wordConstant (n:=k) (BitVec.ofNat w 1))
  simp only [count_comp,count_pair,wordConstant_count] at hzero hz hs
  simp only [totientPair,count_pair,wordMux_count,count_comp]
  dsimp only [totientStepBound]
  nlinarith

lemma totientUpdate_count {k w c : ℕ} (q : BooleanNetwork k w) (hq : q.net.count ≤ c) :
    (totientUpdate q).net.count ≤ totientStepBound w c := by
  simp only [totientUpdate,count_pair,count_select,zero_add]
  exact totientPair_count _ _ _ (by simpa using hq) (by simp) (by simp)

lemma totientScanNet_count {k w c : ℕ} (qs : List (BooleanNetwork k w))
    (hq : ∀ q∈qs,q.net.count ≤ c) :
    (totientScanNet qs).net.count ≤ qs.length*totientStepBound w c := by
  induction qs with
  | nil=>simp [totientScanNet]
  | cons q qs ih=>
    have hh:=totientUpdate_count q (hq q (List.mem_cons_self))
    have ht:=ih (fun q h=>hq q (List.mem_cons_of_mem _ h))
    simp only [totientScanNet,count_comp,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

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

lemma totientFromList_count {k w c : ℕ} (v : BooleanNetwork k w)
    (qs : List (BooleanNetwork k w)) (hq : ∀ q∈qs,q.net.count ≤ c) :
    (totientFromList v qs).net.count ≤ v.net.count+w+qs.length*totientStepBound w c := by
  have hh:=totientScanNet_count qs hq
  simp only [totientFromList,count_comp,count_pair,count_select,zero_add,Nat.add_zero,
    wordConstant_count]
  omega

lemma tableTotient_count {k n c : ℕ} (v : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n)))
    (hv : v.net.count ≤ c)
    (hr : ∀ r∈rows,r.1.net.count ≤ c ∧ ∀ p∈r.2,p.net.count ≤ c) :
    (tableTotient v rows).net.count ≤ tableTotientBound n (tableNets rows).length c := by
  have hp : ∀ p∈List.flatten (List.replicate n (tableNets rows)),p.net.count ≤ 3*c+220*n+50 := by
    intro p hp
    obtain ⟨qs,hqs,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hqs).2
    subst qs
    exact tableNets_counts rows hr p hp
  have hh:=totientFromList_count v _ hp
  simp only [List.length_flatten,List.map_replicate,List.sum_replicate,smul_eq_mul] at hh
  exact hh.trans (by dsimp only [tableTotientBound];omega)
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

lemma primesPhiNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count ≤ c) (hp : ∀ p∈ps,p.net.count ≤ c) :
    (primesPhiNet m ps).net.count ≤ c+n+(n*ps.length)*totientStepBound n c := by
  have hh:=totientFromList_count m (List.flatten (List.replicate n ps)) (c:=c) (by
    intro p hp'
    obtain ⟨qs,hqs,hp'⟩:=List.mem_flatten.mp hp'
    have he:=(List.mem_replicate.mp hqs).2
    subst qs
    exact hp p hp')
  simp only [List.length_flatten,List.map_replicate,List.sum_replicate,smul_eq_mul] at hh
  exact hh.trans (by omega)
end BitArithmetic
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

lemma componentPhiNet_count {k n c : ℕ} (m p : BooleanNetwork k n)
    (hm : m.net.count ≤ c) (hp : p.net.count ≤ c) :
    (componentPhiNet m p).net.count ≤ componentPhiBound n c := by
  have hq:=primeComponent_count m p hm hp
  have hd:=div_count n
  have hs:=natSubOn_count (primeComponent m p) (((primeComponent m p).pair p).comp (div n))
  simp only [count_comp,count_pair] at hs
  change (natSubOn _ _).net.count≤_
  dsimp only [componentPhiBound]
  nlinarith

lemma componentLevelNet_count {k n c : ℕ} (m p : BooleanNetwork k n)
    (hm : m.net.count ≤ c) (hp : p.net.count ≤ c) (t : ℕ) :
    (componentLevelNet m p t).net.count ≤ componentLevelBound n c := by
  have hc:=closedLevelNet_count (componentPhiNet m p) (componentPhiNet_count m p hm hp) t
  have hd:=dividesOn_count p m
  rw [componentLevelNet,wordMux_count,wordConstant_count]
  dsimp only [componentLevelBound]
  nlinarith
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DistinctProductCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma occursLater_count {k n c : ℕ} (p : BooleanNetwork k n) (ps : List (BooleanNetwork k n))
    (hp : p.net.count ≤ c) (hps : ∀ q∈ps,q.net.count ≤ c) :
    (occursLater p ps).net.count≤ps.length*(2*c+96*n+25)+1 := by
  have hh:=any_count (ps.map (fun q=>(p.pair q).comp (wordEq n)))
    (c:=2*c+96*n+21) (by
      intro q hq
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hq
      have h:=hps b hb
      have hw:=wordEq_count n
      rw [count_comp,count_pair]
      omega)
  simpa only [occursLater,List.length_map,Nat.add_assoc] using hh

lemma distinctProductNet_count {k n c d : ℕ} (value : BooleanNetwork k n→BooleanNetwork k n)
    (ps : List (BooleanNetwork k n))
    (hp : ∀ p∈ps,p.net.count ≤ c) (hv : ∀ p∈ps,(value p).net.count≤d) :
    (distinctProductNet value ps).net.count≤
      ps.length*(d+90*n*n+22*n+7+ps.length*(2*c+96*n+25))+n := by
  induction ps with
  | nil=>simp [distinctProductNet,wordConstant_count]
  | cons p ps ih=>
    have hps:=fun q hq=>hp q (List.mem_cons_of_mem p hq)
    have hvs:=fun q hq=>hv q (List.mem_cons_of_mem p hq)
    have hi:=ih hps hvs
    have ho:=occursLater_count p ps (hp p (by simp)) hps
    have hd:=hv p (by simp)
    have hm:=mul_count n
    simp only [distinctProductNet,count_comp,count_pair,wordMux_count,wordConstant_count,
      List.length_cons]
    nlinarith
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

namespace BitArithmetic

lemma tableLevelNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count ≤ c)
    (hp : ∀ p∈ps,p.net.count ≤ c) (t : ℕ) :
    (tableLevelNet m ps t).net.count≤
      ps.length*(componentLevelBound n c+90*n*n+22*n+7+ps.length*(2*c+96*n+25))+n := by
  exact distinctProductNet_count _ _ hp (fun p hh=>componentLevelNet_count m p hm (hp p hh) t)
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordSumCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma sumNet_count {k w c : ℕ} (as : List (BooleanNetwork k w))
    (h : ∀ a∈as,a.net.count ≤ c) :
    (sumNet as).net.count≤as.length*(c+86*w+6)+w := by
  induction as with
  | nil=>simp [sumNet,wordConstant_count]
  | cons a as ih=>
    have ha:=h a (by simp)
    have hi:=ih (fun b hb=>h b (by simp [hb]))
    have hh:=add_count w
    simp only [sumNet,count_comp,count_pair,List.length_cons]
    nlinarith
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

lemma tableBadCountNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count ≤ c) (hp : ∀ p∈ps,p.net.count ≤ c) :
    (tableBadCountNet m ps).net.count≤tableBadCountBound n ps.length c := by
  have hh:=sumNet_count (List.ofFn (fun t : Fin (n+1)=>tableLevelNet m ps t.val)) (by
    intro q hq
    obtain ⟨t,rfl⟩:=List.mem_ofFn.mp hq
    exact tableLevelNet_count m ps hm hp t.val)
  simpa only [tableBadCountNet,tableBadCountBound,List.length_ofFn] using hh

lemma tableFavorableCountNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count ≤ c) (hp : ∀ p∈ps,p.net.count ≤ c) :
    (tableFavorableCountNet m ps).net.count≤tableFavorableCountBound n ps.length c := by
  have hphi:=primesPhiNet_count m ps hm hp
  have hbad:=tableBadCountNet_count m ps hm hp
  have hs:=natSubOn_count (primesPhiNet m ps) (tableBadCountNet m ps)
  change (natSubOn _ _).net.count≤_
  dsimp only [tableFavorableCountBound]
  omega
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

lemma retainedFavorableCount_count {b : ℕ} (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (hm : m.net.count ≤ b) (hq : M.query.net.count ≤ b) (hr : PhysicalNode.resultBound n ≤ b) :
    (M.retainedFavorableCount t m).net.count ≤
      tableFavorableCountBound n (t*n) (3*b+220*n+50) := by
  have hp:=tableNets_counts (M.fieldRows t) (c:=b) (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  have hh:=tableFavorableCountNet_count m (tableNets (M.fieldRows t))
    (c:=3*b+220*n+50) (by omega) hp
  rwa [M.fieldRows_table_length] at hh
end NodeMachine
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

lemma retainedTotient_count {b : ℕ} (t : ℕ) (v : BooleanNetwork (M.width t) n)
    (hv : v.net.count ≤ b) (hq : M.query.net.count ≤ b) (hr : PhysicalNode.resultBound n ≤ b) :
    (M.retainedTotient t v).net.count ≤ tableTotientBound n (t*n) b := by
  have hh:=tableTotient_count v (M.fieldRows t) hv (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  rwa [M.fieldRows_table_length] at hh

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletionFilterPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
namespace RatExprPoly
lemma ofHeight {v : ℕ→Type*} {q : ℕ→ℚ} (h : RatHeightPoly q) :
    RatExprPoly (fun n=>RatExpr.const (q n) : ∀n,RatExpr (v n)) := const h.1 h.2
end RatExprPoly
namespace Completion.Expressions
variable {v : ℕ→Type*} {W t : ℕ→ℕ} {s z : ∀n,RatExpr (v n)}
lemma ordinaryMass_poly (ht : PolyBound t) (hs : RatExprPoly s) :
    RatExprPoly (fun n=>ordinaryMass (t n) (s n)) :=
  (RatExprPoly.ofHeight ((RatHeightPoly.constant 1).sub
    ((RatHeightPoly.constant 1).div ((RatHeightPoly.constant 2).pow ht)))).mul hs
lemma coefficient_poly (hW : PolyBound W) (ht : PolyBound t)
    (hs : RatExprPoly s) (hz : RatExprPoly z) :
    RatExprPoly (fun n=>coefficient (W n) (t n) (s n) (z n)) := by
  have hp : RatExprPoly (fun n=>RatExpr.const ((2:ℚ)^(W n+t n+2)) : ∀n,RatExpr (v n)) :=
    RatExprPoly.ofHeight ((RatHeightPoly.constant 2).pow ((hW.add ht).add (PolyBound.const 2)))
  exact (RatExprPoly.ofInt (hp.mul (hz.div (ordinaryMass_poly ht hs))).floor).div hp
lemma guess_poly (hW : PolyBound W) (ht : PolyBound t)
    (hs : RatExprPoly s) (hz : RatExprPoly z) :
    RatExprPoly (fun n=>guess (W n) (t n) (s n) (z n)) :=
  ((hz.sub ((coefficient_poly hW ht hs hz).mul (ordinaryMass_poly ht hs))).mul
    (RatExprPoly.ofHeight ((RatHeightPoly.constant 2).pow hW))).div
    (RatExprPoly.ofHeight ((RatHeightPoly.constant 1).div ((RatHeightPoly.constant 2).pow ht)))
lemma listRateCoin_poly : RatExprPoly (fun n=>listRateCoin n (n^5)) :=
  ((RatExprPoly.ofNat (NatExprPoly.var (fun _=>1))).div
    (RatExprPoly.ofNat (OrderTrial.Expressions.coveringPow_poly
      (NatExprPoly.var (fun _=>0)) PolyBound.id))).repeatedSuccess (PolyBound.id.pow 5)
lemma orderRateCoin_poly : RatExprPoly (fun n=>orderRateCoin n (n^5)) :=
  ((RatExprPoly.ofNat (NatExprPoly.var (fun _=>1))).mul
    (OrderTrial.Expressions.lambdaE_poly PolyBound.id
      (NatExprPoly.var (fun _=>0)))).repeatedSuccess (PolyBound.id.pow 5)
end Completion.Expressions
lemma retentionNet_at {α : Type*} {len a b : α→ℕ} {v : ℕ→Type*} {T : ℕ→ℕ}
    {p : ∀n,RatExpr (v n)} {c : ∀n,NatExpr (v n)}
    {vars : ∀x,v (len x)→BooleanNetwork (a x) (b x)}
    (hT : PolyBound T) (hp : RatExprPoly p) (hc : NatExprPoly c)
    (hb : PolyAt len b) (hv : ∃q : Polynomial ℕ,∀x i,(vars x i).net.count≤q.eval (len x)) :
    NetworkAt len (fun x=>retentionNet (T (len x)) (p (len x)) (c (len x)) (vars x)) :=
  (NatExprAt.ofPoly (thresholdExpr_poly hT hp hc) len).isOne hb hv
namespace Completion
lemma predicateFilter_at {α : Type*} {len a b : α→ℕ} {v : ℕ→Type*} {W t d : ℕ→ℕ}
    {s z : ∀n,RatExpr (v n)} {coin : ∀n,NatExpr (v n)}
    {vars : ∀x,v (len x)→BooleanNetwork (a x) (b x)}
    {branch : ∀x,BooleanNetwork (a x) (t (len x))}
    {good guessGood : ∀x,BooleanNetwork (a x) 1}
    (hW : PolyBound W) (ht : PolyBound t) (hd : PolyBound d)
    (hs : RatExprPoly s) (hz : RatExprPoly z) (hc : NatExprPoly coin)
    (hb : PolyAt len b) (hv : ∃q : Polynomial ℕ,∀x i,(vars x i).net.count≤q.eval (len x))
    (hbranch : NetworkAt len branch) (hgood : NetworkAt len good) (hguess : NetworkAt len guessGood) :
    NetworkAt len (fun x=>predicateFilter (W:=W (len x)) (d (len x))
      (s (len x)) (z (len x)) (vars x) (branch x) (coin (len x)) (good x) (guessGood x)) := by
  have hT : PolyBound (fun n=>coinBits (W n) (t n) (d n)) := by
    unfold coinBits;repeat' (first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  have ho:=retentionNet_at hT (Expressions.coefficient_poly hW ht hs hz) hc hb hv
  have hg:=retentionNet_at hT (Expressions.guess_poly hW ht hs hz) hc hb hv
  have hr:=hbranch.zeroWord (PolyAt.ofPoly ht len)
  exact (hr.bnot.band (hgood.band ho)).bor (hr.band (hguess.band hg))
end Completion
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeInitialization
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma initialNet_count (t : ℕ) : (M.initialNet t).net.count=
    t*(NodeKernel.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [initialNet, count_select]
  | succ t ih=>
    simp only [initialNet,packNet_count,Completion.zeros_count,ih]
    ring

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QuarterPreparation
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
open Exactness OrderTrial

namespace Quarter
lemma program_length {q : ℕ} (P : List (Instruction q)) (n : ℕ) :
    (program P n).length=P.length+1+n*n+D n := Completion.program_length P (n*n) 1 (n^11)

end Quarter
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreePadding
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
namespace PhysicalTree

lemma padProgram_length (n : ℕ) : (padProgram n).length=padding n*n := by
  rw [padProgram,tensorProgram_length,hadamardPrefix_length]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreePhysicalPreparation
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
open BooleanNetwork BitArithmetic Exactness OrderTrial

namespace PhysicalTree

lemma launchProgram_length (n : ℕ) : (launchProgram n).length≤
    4*launchWork n+2*width n+((machine n).program (steps n)).length :=
  preparedOracle_length _ _ _
lemma paddedProgram_length (n : ℕ) : (paddedProgram n).length≤
    4*launchWork n+2*width n+((machine n).program (steps n)).length+padding n*n := by
  rw [paddedProgram,parallelProgram_length,padProgram_length]
  exact Nat.add_le_add_right (launchProgram_length n) _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeQuarterPhysical
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

namespace PhysicalTree
lemma quarterProgram_length (n : ℕ) :
    (quarterProgram n).length=(paddedProgram n).length+1+n*n+Quarter.D n :=
  Quarter.program_length _ _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ZeroOutside
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
open BooleanNetwork Exactness

lemma zeroOutside_count {q : ℕ} (I : Finset (Fin q)) : (zeroOutside I).net.count≤2*q+1 := by
  have h : ∀ c∈List.ofFn (fun i : Fin q => if i∈I then constant true else (bit i).bnot),
      c.net.count≤1 := by
    intro c hc
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc
    by_cases hi : i∈I
    · rw [ite_eq_left hi]
      exact le_rfl
    · rw [ite_eq_right hi]
      exact le_rfl
  simpa only [zeroOutside,List.length_ofFn,Nat.reduceAdd,Nat.mul_comm] using all_count _ h

namespace PhysicalTree

lemma zeroNet_count (n : ℕ) : (zeroNet n).net.count≤2*quarterWidth n+1 :=
  zeroOutside_count _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeReadout
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
open BooleanNetwork BitArithmetic Exactness

lemma readoutProgram_length {q m r : ℕ} (P : List (Instruction q))
    (c : BooleanNetwork q m) (hr : c.net.count ≤ r) :
    (readoutProgram P c hr).length≤P.length+4*c.net.count+2*m := by
  have hh:=oracleOn_length c hr
  simp only [readoutProgram,List.length_append,firstProgram_length]
  omega

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactoringCircuit
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
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma finalCircuit_length (ℓ : ℕ) :
    (finalCircuit ℓ).instructions.length=
      (factoringProgram (paddedLength ℓ) (paddedLength_pos ℓ)).length := by
  exact List.length_map _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeStateBounds
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


namespace ExactQuantumFactoring.BitArithmetic.NodeStateCircuit
open BooleanNetwork

lemma pending_count (s w : ℕ) : (pending s w).net.count=0 := rfl
lemma output_count (s w : ℕ) : (output s w).net.count=0 := rfl
lemma bad_count (s w : ℕ) : (bad s w).net.count=0 := rfl
lemma old_count (s w : ℕ) : (old s w).net.count=0 := rfl
lemma supplied_count (s w : ℕ) : (supplied s w).net.count=0 := rfl
lemma nodeInput_count (s w : ℕ) : (nodeInput s w).net.count=0 := by
  simp only [nodeInput,count_pair,count_comp,old_count,pending_count,supplied_count,zero_add]
lemma top_count (s w : ℕ) : (top s w).net.count=0 := by
  simp only [top,count_comp,pending_count,blockNet_count,zero_add]
lemma nextPending_count (s w : ℕ) : (nextPending s w).net.count ≤ NodeCircuit.nextBound s w := by
  simpa only [nextPending,count_comp,nodeInput_count,zero_add] using NodeCircuit.next_count s w
lemma emission_count (s w : ℕ) : (emission s w).net.count ≤ NodeCircuit.primeBound w+8*w := by
  simpa only [emission,count_comp,nodeInput_count,zero_add] using NodeCircuit.emitted_count s w

lemma nextOutput_count (s w : ℕ) : (nextOutput s w).net.count ≤ outputBound s w := by
  have hz := zeroWord_count (emission s w)
  have he := emission_count s w
  have hs := stackPush_count (emission s w) ((old s w).comp (output s w))
  simp only [count_comp,old_count,output_count,add_zero] at hs
  have hs' : (stackPush (emission s w) ((old s w).comp (output s w))).net.count ≤
      (s+1)*w*(NodeCircuit.primeBound w+8*w) := hs.trans (Nat.mul_le_mul_left _ he)
  simp only [nextOutput,wordMux_count,count_comp,old_count,output_count,add_zero]
  dsimp only [outputBound]
  omega
lemma nextBad_count (s w : ℕ) : (nextBad s w).net.count ≤
    97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+9 := by
  calc
    (nextBad s w).net.count = (NodeCircuit.failed s w).net.count+4 := by
      simp only [nextBad,count_bor,count_comp,old_count,bad_count,nodeInput_count,zero_add]
    _ ≤ (97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+5)+4 :=
      Nat.add_le_add_right (NodeCircuit.failed_count s w) 4
    _ = 97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+9 := by omega

theorem step_count (s w : ℕ) : (step s w).net.count ≤ stepBound s w := by
  have h1 := nextPending_count s w
  have h2 := nextOutput_count s w
  have h3 := nextBad_count s w
  simp only [step,count_pair]
  exact Nat.add_le_add (Nat.add_le_add h1 h2) h3

end ExactQuantumFactoring.BitArithmetic.NodeStateCircuit


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BitArithmetic
namespace PreparationPolynomial
variable {α : Sort*} {len s w a b c : α→ℕ}
lemma cyclicMulBound_poly (hs : PolyAt len s) (hw : PolyAt len w)
    (ha : PolyAt len a) (hb : PolyAt len b) (hc : PolyAt len c) :
    PolyAt len (fun x=>cyclicMulBound (s x) (w x) (a x) (b x) (c x)) := by
  unfold cyclicMulBound
  have hwp:=hw.add (PolyAt.const len 1)
  exact (hs.mul hw).mul (hw.add (hs.mul ((((((ha.add hb).add ((PolyAt.const len 2).mul hc)).add
    (((((PolyAt.const len 1224).mul hw).mul hw).add ((PolyAt.const len 143).mul hw)).add (PolyAt.const len 12))).add
    ((PolyAt.const len 216).mul (hwp.pow 2))).add ((PolyAt.const len 142).mul hwp)).add (PolyAt.const len 15))))
lemma cyclicAddBound_poly (hs : PolyAt len s) (hw : PolyAt len w)
    (ha : PolyAt len a) (hb : PolyAt len b) (hc : PolyAt len c) :
    PolyAt len (fun x=>cyclicAddBound (s x) (w x) (a x) (b x) (c x)) := by
  unfold cyclicAddBound
  have hwp:=hw.add (PolyAt.const len 1)
  exact (hs.mul hw).mul ((((((ha.add hb).add hc).add ((PolyAt.const len 216).mul (hwp.pow 2))).add
    ((PolyAt.const len 142).mul hwp)).add (PolyAt.const len 15)))
lemma cyclicStepBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>cyclicStepBound (s x) (w x)) := by
  have h0:=PolyAt.const len 0
  have hm:=cyclicMulBound_poly hs hw h0 h0 h0
  exact ((cyclicMulBound_poly hs hw hm h0 h0).add hm).add ((PolyAt.const len 7).mul (hs.mul hw))
lemma cyclicTestBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>cyclicTestBound (s x) (w x)) := by
  have h0:=PolyAt.const len 0
  have hsw:=(hs.mul hw).mul hw
  have hstep:=hw.mul (cyclicStepBound_poly hs hw)
  exact (((((cyclicAddBound_poly hs hw hsw hsw h0).add hsw).add hstep).add
    (cyclicAddBound_poly hs hw (((PolyAt.const len 2).mul hsw).add hstep) hsw h0)).add
      ((PolyAt.const len 96).mul (hs.mul hw))).add (PolyAt.const len 21)
lemma rootWidth_poly : PolyBound rootWidth := by unfold rootWidth;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma perfectCheckBound_poly : PolyBound perfectCheckBound := by
  have hn:=PolyBound.id
  have hr:=rootWidth_poly
  have hb:=((((PolyBound.const 90).mul hr).mul hr).add ((PolyBound.const 14).mul hr)).add (PolyBound.const 6)
  exact ((((PolyBound.const 147).mul hr).add (PolyBound.const 31)).add
    (hn.mul ((((PolyBound.const 230).mul hr).add (PolyBound.const 21)).add (hn.mul hb)))).add (hn.mul hb)
lemma aksBranchBound_poly : PolyBound (fun n=>aksBranchBound n (n^8) (rootWidth n)) := by
  have hn:=PolyBound.id
  have hr:=rootWidth_poly
  have hc : PolyBound (fun n=>cyclicTestBound (n^8) (rootWidth n)) :=
    cyclicTestBound_poly ((PolyAt.self (id : ℕ→ℕ)).pow 8) hr
  have hbase:=(((((PolyBound.const 216).mul hr).mul hr).add ((PolyBound.const 154).mul hr)).add
    (PolyBound.const 27)).add (PolyBound.const 1)
  have hstep:=(((((PolyBound.const 3672).mul hr).mul hr).add ((PolyBound.const 436).mul hr)).add (PolyBound.const 36))
  have hord:=((hn.pow 2).mul ((((PolyBound.const 100).mul hr).add (PolyBound.const 23)).add (hr.mul hstep))).add (PolyBound.const 1)
  have hdiv:=(((PolyBound.const 8).mul (hn.pow 8)).mul
    (((((PolyBound.const 216).mul hr).mul hr).add ((PolyBound.const 203).mul hr)).add (PolyBound.const 38))).add (PolyBound.const 1)
  have hcon:=(((PolyBound.const 8).mul (hn.pow 8)).mul (hc.add (PolyBound.const 1))).add (PolyBound.const 1)
  exact (((hbase.add hord).add hdiv).add hcon).add (PolyBound.const 3)
lemma primalityBound_poly : PolyBound primalityBound := by
  have hn:=PolyBound.id
  exact (((hn.add (PolyBound.const 1)).mul (perfectCheckBound_poly.add (PolyBound.const 4))).add
    (PolyBound.const 1)).add (PolyBound.const 1) |>.add
      ((((hn.pow 8).add (PolyBound.const 1)).mul (aksBranchBound_poly.add (PolyBound.const 4))).add (PolyBound.const 1)) |>.add (PolyBound.const 1)
lemma primeBound_poly : PolyBound NodeCircuit.primeBound :=
  ((((PolyBound.const 49).mul PolyBound.id).add (PolyBound.const 10)).add rootWidth_poly).add primalityBound_poly
lemma guardBound_poly : PolyBound NodeCircuit.guardBound :=
  (((((PolyBound.const 216).mul PolyBound.id).mul PolyBound.id).add
    ((PolyBound.const 250).mul PolyBound.id)).add (PolyBound.const 45))
lemma quotientBound_poly : PolyBound NodeCircuit.quotientBound :=
  (((((PolyBound.const 216).mul PolyBound.id).mul PolyBound.id).add
    ((PolyBound.const 56).mul PolyBound.id)).add (PolyBound.const 6))
lemma nodeStepBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>NodeStateCircuit.stepBound (s x) (w x)) := by
  have hp:=PolyAt.comp primeBound_poly hw
  have hg:=PolyAt.comp guardBound_poly hw
  have hq:=PolyAt.comp quotientBound_poly hw
  have hn : PolyAt len (fun x=>NodeCircuit.nextBound (s x) (w x)) := by
    unfold NodeCircuit.nextBound NodeCircuit.splitBound
    repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  have ho : PolyAt len (fun x=>NodeStateCircuit.outputBound (s x) (w x)) := by
    unfold NodeStateCircuit.outputBound
    repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  unfold NodeStateCircuit.stepBound
  repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedNetworkPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace RetainedPolynomial
variable {α : Type*} {len n f c : α→ℕ}
lemma primeComponentBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>primeComponentBound (n x) (c x)) := by
  have hw : PolyAt len (fun x=>componentWidth (n x)) := by unfold componentWidth;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  unfold primeComponentBound
  exact (((hc.add hw).add (hw.add (hn.mul (((hc.add hw).add
    (((PolyAt.const len 90).mul hw).mul hw)).add ((PolyAt.const len 14).mul hw) |>.add
      (PolyAt.const len 6))))).add (((PolyAt.const len 2).mul hw).mul
        (((PolyAt.const len 216).mul hw |>.mul hw).add ((PolyAt.const len 300).mul hw) |>.add
          (PolyAt.const len 100)))).add hn
lemma tableOrderBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableOrderBound (n x) (f x) (c x)) := by
  have hw : PolyAt len (fun x=>tableOrderWidth (n x) (f x)) := by unfold tableOrderWidth;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  have hC : PolyAt len (fun x=>3*c x+220*n x+50+tableOrderWidth (n x) (f x)) := by repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  have hs : PolyAt len (fun x=>stripStepBound (tableOrderWidth (n x) (f x))
      (3*c x+220*n x+50+tableOrderWidth (n x) (f x))) := by unfold stripStepBound;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  unfold tableOrderBound
  exact ((hn.mul hf).mul ((((hC.add (((PolyAt.const len 90).mul hw).mul hw)).add
    ((PolyAt.const len 14).mul hw)).add (PolyAt.const len 6)).add hs) |>.add hw).add hn
lemma totientStepBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>totientStepBound (n x) (c x)) := by unfold totientStepBound;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
lemma tableTotientBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableTotientBound (n x) (f x) (c x)) :=
  (hc.add hn).add ((hn.mul hf).mul (totientStepBound_at hn
    (((PolyAt.const len 3).mul hc).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50))))
lemma oddPartBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>oddPartBound (n x) (c x)) := by
  have hp:=primeComponentBound_at hn (hc.add hn)
  unfold oddPartBound;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
lemma closedLevelBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>closedLevelBound (n x) (c x)) := by
  have ho:=oddPartBound_at hn hc
  unfold closedLevelBound;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
lemma componentLevelBound_at (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>componentLevelBound (n x) (c x)) := by
  have hp:=primeComponentBound_at hn hc
  have hphi : PolyAt len (fun x=>componentPhiBound (n x) (c x)) := by unfold componentPhiBound;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  have hclosed:=closedLevelBound_at hn hphi
  unfold componentLevelBound;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
lemma tableFavorableCountBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableFavorableCountBound (n x) (f x) (c x)) := by
  have hstep:=totientStepBound_at hn hc
  have hlev:=componentLevelBound_at hn hc
  have hinner : PolyAt len (fun x=>2*c x+96*n x+25) := by repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  have hmiddle : PolyAt len (fun x=>componentLevelBound (n x) (c x)+90*n x*n x+22*n x+7+f x*(2*c x+96*n x+25)) :=
    ((((hlev.add (((PolyAt.const len 90).mul hn).mul hn)).add ((PolyAt.const len 22).mul hn)).add
      (PolyAt.const len 7)).add (hf.mul hinner))
  have hbad : PolyAt len (fun x=>tableBadCountBound (n x) (f x) (c x)) :=
    ((hn.add (PolyAt.const len 1)).mul ((((hf.mul hmiddle).add hn).add
      ((PolyAt.const len 86).mul hn)).add (PolyAt.const len 6))).add hn
  unfold tableFavorableCountBound;repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
lemma tableCanonicalBound_at (hn : PolyAt len n) (hf : PolyAt len f) (hc : PolyAt len c) :
    PolyAt len (fun x=>tableCanonicalBound (n x) (f x) (c x)) := by
  have hp:=primeComponentBound_at hn hc
  have hi : PolyAt len (fun x=>4*c x+216*n x*n x+202*n x+42) := by repeat' (with_reducible_and_instances first | assumption | exact PolyAt.self _ | exact PolyAt.const _ _ | apply PolyAt.mul | apply PolyAt.add | apply PolyAt.pow | apply PolyAt.max | apply PolyAt.sub | apply PolyAt.div | apply PolyAt.mod | apply PolyAt.natSize)
  have hh : PolyAt len (fun x=>componentCongruenceBound (n x) (f x) (c x)) :=
    (((((hc.add ((PolyAt.const len 3).mul hp)).add (((PolyAt.const len 216).mul hn).mul hn)).add
      ((PolyAt.const len 500).mul hn)).add (PolyAt.const len 100)).add (hf.mul hi))
  have hi' : PolyAt len (fun x=>2*c x+216*n x*n x+154*n x+33+componentCongruenceBound (n x) (f x) (c x)) :=
    (((((PolyAt.const len 2).mul hc).add (((PolyAt.const len 216).mul hn).mul hn)).add
      ((PolyAt.const len 154).mul hn)).add (PolyAt.const len 33)).add hh
  exact (((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 48).mul hn)).add
    (PolyAt.const len 10)).add (hf.mul hi')).add (PolyAt.const len 2)
lemma resultBound_at (hn : PolyAt len n) : PolyAt len (fun x=>PhysicalNode.resultBound (n x)) :=
  (hn.mul hn).add ((hn.mul hn).mul (((PolyAt.const len 498).mul hn).add (PolyAt.const len 114)))
end RetainedPolynomial
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedNetworkAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a b : α→ℕ}
lemma all_map {δ : α→Type*} (ls : ∀x,List (δ x)) (f : ∀x,δ x→BooleanNetwork (a x) 1)
    (hl : PolyAt len (fun x=>(ls x).length))
    (hf : NetworkAt (fun xi : Σx,{i // i∈ls x}=>len xi.1) (fun xi=>f xi.1 xi.2.val)) :
    NetworkAt len (fun x=>BooleanNetwork.all ((ls x).map (f x))) := by
  obtain ⟨p,hp⟩:=hf
  apply all (by simpa only [List.length_map] using hl)
  refine ⟨p,?_⟩
  intro x g hg
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hg
  exact hp ⟨x,⟨i,hi⟩⟩
lemma any_ofFn {k : α→ℕ} {f : ∀x,Fin (k x)→BooleanNetwork (a x) 1} (hk : PolyAt len k)
    (hf : NetworkAt (fun xi : Σx,Fin (k x)=>len xi.1) (fun xi=>f xi.1 xi.2)) :
    NetworkAt len (fun x=>BooleanNetwork.any (List.ofFn (f x))) := by
  obtain ⟨p,hp⟩:=hf
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply of_le ((hk.mul (hc.add (PolyAt.const len 4))).add (PolyAt.const len 1))
  intro x
  have h:=any_count (List.ofFn (f x)) (c:=p.eval (len x)) (by
    intro g hg;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hg;exact hp ⟨x,i⟩)
  simpa only [List.length_ofFn] using h
lemma primeComponent {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hb : PolyAt len b) (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>BitArithmetic.primeComponent (f x) (g x)) :=
  of_le (RetainedPolynomial.primeComponentBound_at hb (PolyAt.add hf hg))
    (fun x=>primeComponent_count _ _ (by omega) (by omega))
lemma dividesOn {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hb : PolyAt len b) (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>BitArithmetic.dividesOn (f x) (g x)) := by
  have hh : PolyAt len (fun x=>(f x).net.count+(g x).net.count+216*b x*b x+154*b x+27) :=
    ((((PolyAt.add hf hg).add (((PolyAt.const len 216).mul hb).mul hb)).add
      ((PolyAt.const len 154).mul hb)).add (PolyAt.const len 27))
  exact of_le hh fun x=>dividesOn_count _ _
lemma sameTwoVal {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hb : PolyAt len b) (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>BitArithmetic.sameTwoVal (f x) (g x)) := by
  have hi : PolyAt len (fun x=>2*(f x).net.count+2*(g x).net.count+864*b x*b x+616*b x+118) :=
    (((((PolyAt.const len 2).mul hf).add ((PolyAt.const len 2).mul hg)).add
      (((PolyAt.const len 864).mul hb).mul hb)).add ((PolyAt.const len 616).mul hb)).add (PolyAt.const len 118)
  exact of_le ((hb.mul hi).add (PolyAt.const len 1)) fun x=>sameTwoVal_count _ _
end NetworkAt
namespace NodeMachine
variable {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
variable (hn : PolyAt len n) (ht : PolyAt len t)
  (hq : NetworkAt len (fun x=>(M x).query))
include hn ht hq
lemma retainedOrder_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedOrder (t x) (a x) (m x)) := by
  have hB:=((PolyAt.add ha hm).add hq).add (RetainedPolynomial.resultBound_at hn)
  apply NetworkAt.of_le (RetainedPolynomial.tableOrderBound_at hn (ht.mul hn) hB)
  intro x
  exact (M x).retainedOrder_count _ _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedTotient_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedTotient (t x) (m x)) := by
  have hB:=(PolyAt.add hm hq).add (RetainedPolynomial.resultBound_at hn)
  apply NetworkAt.of_le (RetainedPolynomial.tableTotientBound_at hn (ht.mul hn) hB)
  intro x
  exact (M x).retainedTotient_count _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedFavorableCount_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedFavorableCount (t x) (m x)) := by
  have hB:=(PolyAt.add hm hq).add (RetainedPolynomial.resultBound_at hn)
  have hC:=((PolyAt.const len 3).mul hB).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50)
  apply NetworkAt.of_le (RetainedPolynomial.tableFavorableCountBound_at hn (ht.mul hn) hC)
  intro x
  exact (M x).retainedFavorableCount_count _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedCanonical_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedCanonical (t x) (a x) (m x)) := by
  have hB:=((PolyAt.add ha hm).add hq).add (RetainedPolynomial.resultBound_at hn)
  have hC:=((PolyAt.const len 3).mul hB).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50)
  apply NetworkAt.of_le (RetainedPolynomial.tableCanonicalBound_at hn (ht.mul hn) hC)
  intro x
  exact (M x).retainedCanonical_count _ _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedComponentOrder_at {a m p : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hp : NetworkAt len p) :
    NetworkAt len (fun x=>(M x).retainedComponentOrder (t x) (a x) (m x) (p x)) :=
  retainedOrder_at hn ht hq ha (NetworkAt.primeComponent hn hm hp)
omit hq in
lemma tableNets_length_at : PolyAt len (fun x=>(tableNets ((M x).fieldRows (t x))).length) := by
  simpa only [fieldRows_table_length] using ht.mul hn
omit ht in
lemma tableNets_at : NetworkAt (fun xi : Σx,{p // p∈tableNets ((M x).fieldRows (t x))}=>len xi.1)
    (fun xi=>xi.2.val) := by
  let pull:=fun xi : Σx,{p // p∈tableNets ((M x).fieldRows (t x))}=>xi.1
  have hB:=PolyAt.add hq (RetainedPolynomial.resultBound_at hn)
  have hC:=((PolyAt.const len 3).mul hB).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50)
  apply NetworkAt.of_le (hC.pull pull)
  rintro ⟨x,p,hp⟩
  apply tableNets_counts _ (c:=(M x).query.net.count+PhysicalNode.resultBound (n x)) _ _ hp
  intro r hr
  have hh:=(M x).fieldRows_counts (t x) r hr
  exact ⟨hh.1.trans (by omega),fun p hp=>(hh.2 p hp).trans (by omega)⟩
end NodeMachine
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedFavorablePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len k n K : α→ℕ}
lemma usableOn {a m : ∀x,BooleanNetwork (k x) (n x)}
    (hn : PolyAt len n) (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>OrderSlots.usableOn (a x) (m x)) :=
  (ha.wordLt hm hn).band
    (((ha.pair hm).comp (NetworkAt.gcdNet hn)).equalOn (NetworkAt.wordConstant _ hn) hn)
lemma firstOnly {a : ∀x,BooleanNetwork (k x) (n x)}
    (hn : PolyAt len n) (hK : PolyAt len K) (ha : NetworkAt len a) :
    NetworkAt len (fun x=>TransitionWords.firstOnly (K:=K x) (a x)) := by
  apply of_le ((hn.mul (hK.add (PolyAt.const len 1))).mul
    ((PolyAt.add ha hn).add (PolyAt.const len 1)))
  intro x
  apply TransitionWords.encodeNet_count
  intro i
  by_cases hi:i.val=0
  · rw [ite_eq_left hi];omega
  · rw [ite_eq_right hi,wordConstant_count];omega
end NetworkAt
namespace NodeMachine
variable {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
variable (hn : PolyAt len n) (ht : PolyAt len t)
  (hq : NetworkAt len (fun x=>(M x).query))
include hn ht hq
lemma retainedFavorable_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedFavorable (t x) (a x) (m x)) := by
  let ps:=fun x=>tableNets ((M x).fieldRows (t x))
  let ix:=Σx,{p // p∈ps x}
  let fst:ix→α:=Sigma.fst
  let jx:=Σxi:ix,{q // q∈ps xi.1}
  let both:jx→α:=fun xi=>xi.1.1
  have hps : NetworkAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val):=tableNets_at hn hq
  have hl : PolyAt len (fun x=>(ps x).length):=tableNets_length_at hn ht
  apply (NetworkAt.usableOn hn ha hm).band
  apply NetworkAt.bnot
  apply NetworkAt.all_map ps _ hl
  apply NetworkAt.all_map (fun xi:ix=>ps xi.1) _ (hl.pull fst)
  have hp:=hps.pull (fun xi:jx=>xi.1)
  have hq':=hps.pull (fun xi:jx=>⟨xi.1.1,xi.2⟩)
  have hn':=hn.pull both
  have ht':=ht.pull both
  have hquery:=hq.pull both
  have ha':=ha.pull both
  have hm':=hm.pull both
  exact (NetworkAt.dividesOn hn' hp hm').bnot.bor
    ((NetworkAt.dividesOn hn' hq' hm').bnot.bor
      (NetworkAt.sameTwoVal hn'
        (retainedComponentOrder_at hn' ht' hquery ha' hm' hp)
        (retainedComponentOrder_at hn' ht' hquery ha' hm' hq')))
lemma retainedGoodList_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((M x).width (t x)) (n x*((n x)^5+1))}
    (hm : NetworkAt len m) (hy : NetworkAt len y) :
    NetworkAt len (fun x=>(M x).retainedGoodList (t x) (m x) (y x)) := by
  let param:=fun xi : Σx,Fin ((n x)^5)=>xi.1
  apply NetworkAt.any_ofFn (hn.pow 5)
  exact retainedFavorable_at (hn.pull param) (ht.pull param) (hq.pull param)
    ((hy.pull param).rewire _) (hm.pull param)
lemma retainedCanonicalList_at (hpos : ∀x,0<n x)
    {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    {y : ∀x,BooleanNetwork ((M x).width (t x)) (n x*((n x)^5+1))}
    (hm : NetworkAt len m) (hy : NetworkAt len y) :
    NetworkAt len (fun x=>(M x).retainedCanonicalList (hpos x) (t x) (m x) (y x)) := by
  have ha : NetworkAt len (fun x=>TransitionWords.readNet (y x) ⟨0,pow_pos (hpos x) 5⟩):=
    hy.rewire _
  exact (retainedCanonical_at hn ht hq ha hm).band
    (hy.equalOn (NetworkAt.firstOnly hn (hn.pow 5) ha) (hn.mul ((hn.pow 5).add (PolyAt.const len 1))))
end NodeMachine
end ExactQuantumFactoring

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedFilterPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
lemma ite {α : Type*} {len a b : α→ℕ} (p : α→Prop) [∀x,Decidable (p x)]
    {f g : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>if p x then f x else g x) := by
  apply of_le (PolyAt.add hf hg)
  intro x
  by_cases h : p x
  · rw [ite_eq_left h];omega
  · rw [ite_eq_right h];omega
end NetworkAt
namespace Completion.Expressions
lemma target_poly : RatExprPoly (fun n=>RatExpr.const (Completion.target n) : ℕ→RatExpr (Fin 3)) :=
  RatExprPoly.ofHeight ((RatHeightPoly.constant 1).sub
    ((RatHeightPoly.constant 1).div ((RatHeightPoly.constant 2).pow PolyBound.id)))
end Completion.Expressions
namespace Completion
lemma rareWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>rareWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
lemma ordinaryWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>ordinaryWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
lemma guessWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>guessWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
lemma retentionWires_at {α : Type*} (len q W t d : α→ℕ) :
    NetworkAt len (fun x=>retentionWires (q x) (W x) (t x) (d x)) := NetworkAt.select _
end Completion
namespace NodeMachine
variable {α : Type*} {len c t : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
variable (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query))
include ht hq
lemma listFilterVars_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (PhysicalListSlots.width (len x))}
    (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt (fun xi : α×Fin 3=>len xi.1) (fun xi=>(M xi.1).listFilterVars (t xi.1) (m xi.1) (raw xi.1) xi.2) := by
  unfold listFilterVars
  let fst : α×Fin 3→α:=Prod.fst
  have hn:=PolyAt.self len
  have hc:=PolyAt.ofPoly PreparationPolynomial.listCoin len
  have hw:=hn.add hc
  have hresize:=NetworkAt.resizeWord hn hw
  apply NetworkAt.ite (fun xi=>xi.2=0) ((hm.comp hresize).pull fst)
  apply NetworkAt.ite (fun xi=>xi.2=1)
    (((retainedFavorableCount_at hn ht hq hm).comp hresize).pull fst)
  exact ((hr.comp (Completion.retentionWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
      (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))).comp (NetworkAt.resizeWord hc hw)).pull fst
lemma orderFilterVars_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt (fun xi : α×Fin 3=>len xi.1) (fun xi=>(M xi.1).orderFilterVars (t xi.1) (a xi.1) (m xi.1) (raw xi.1) xi.2) := by
  unfold orderFilterVars
  let fst : α×Fin 3→α:=Prod.fst
  have hn:=PolyAt.self len
  have hc:=PolyAt.ofPoly PreparationPolynomial.orderCoin len
  have hw:=hn.add hc
  have ho:=retainedOrder_at hn ht hq ha hm
  have hphi:=retainedTotient_at hn ht hq ho
  have hresize:=NetworkAt.resizeWord hn hw
  apply NetworkAt.ite (fun xi=>xi.2=0) ((ho.comp hresize).pull fst)
  apply NetworkAt.ite (fun xi=>xi.2=1) ((hphi.comp hresize).pull fst)
  exact ((hr.comp (Completion.retentionWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
      (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))).comp (NetworkAt.resizeWord hc hw)).pull fst
lemma retainedListFilter_at (hpos : ∀x,0<len x)
    {m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (PhysicalListSlots.width (len x))}
    (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).retainedListFilter (hpos x) (t x) (m x) (raw x)) := by
  unfold retainedListFilter
  have hn:=PolyAt.self len
  obtain ⟨p,hp⟩:=listFilterVars_at ht hq hm hr
  have hord : NetworkAt len (fun x=>PhysicalListSlots.ordinaryNet (len x)) :=
    NetworkAt.of_le (PolyAt.ofPoly PreparationPolynomial.transitionWidth len)
      (fun x=>PhysicalListSlots.ordinaryNet_count (len x))
  have hgood := retainedGoodList_at hn ht hq hm ((hr.comp (Completion.ordinaryWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))).comp hord)
  have hcanonical := retainedCanonicalList_at hn ht hq hpos hm (hr.comp (Completion.guessWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5))))
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>listVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) (PolyBound.id.mul (PolyBound.id.pow 5))
      Completion.Expressions.listRateCoin_poly Completion.Expressions.target_poly (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.listCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5))))
      hgood hcanonical
lemma listDummyFilter_at
    {m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (PhysicalListSlots.width (len x))}
    (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).listDummyFilter (t x) (m x) (raw x)) := by
  unfold listDummyFilter
  have hn:=PolyAt.self len
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  obtain ⟨p,hp⟩:=listFilterVars_at ht hq hm hr
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>listVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) (PolyBound.id.mul (PolyBound.id.pow 5))
      (RatExprPoly.ofHeight (RatHeightPoly.constant 1)) Completion.Expressions.target_poly
      (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.listCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))) (NetworkAt.constant (fun _=>true))
      ((hr.comp (Completion.guessWires_at len (fun x=>PhysicalListSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>(len x*(len x)^5)))).zeroWord hw)
lemma orderActualFilter_at
    {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).orderActualFilter (t x) (a x) (m x) (raw x)) := by
  unfold orderActualFilter
  have hn:=PolyAt.self len
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  have ho:=retainedOrder_at hn ht hq ha hm
  obtain ⟨p,hp⟩:=orderFilterVars_at ht hq ha hm hr
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>orderVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) ((PolyBound.id.add (PolyBound.const 10)).mul (PolyBound.id.pow 5))
      Completion.Expressions.orderRateCoin_poly Completion.Expressions.target_poly
      (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.orderCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5))))
      ((OrderSlots.orderResultNet_poly ha hm (hr.comp (Completion.ordinaryWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5))))).equalOn ho hn)
      ((hr.comp (Completion.guessWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))).equalOn (ho.comp (NetworkAt.resizeWord hn hw)) hw)
lemma orderDummyFilter_at
    {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).orderDummyFilter (t x) (a x) (m x) (raw x)) := by
  unfold orderDummyFilter
  have hn:=PolyAt.self len
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  obtain ⟨p,hp⟩:=orderFilterVars_at ht hq ha hm hr
  with_reducible
    exact Completion.predicateFilter_at (len:=len) (a:=fun x=>(M x).width (t x))
      (v:=fun _=>Fin 3) (b:=fun x=>orderVarWidth (len x))
      PreparationPolynomial.transitionWidth
      ((PolyBound.const 2).mul PolyBound.id) ((PolyBound.id.add (PolyBound.const 10)).mul (PolyBound.id.pow 5))
      (RatExprPoly.ofHeight (RatHeightPoly.constant 1)) Completion.Expressions.target_poly
      (NatExprPoly.var (fun _=>2))
      (hn.add (PolyAt.ofPoly PreparationPolynomial.orderCoin len)) (⟨p,fun x i=>hp (x,i)⟩)
      (hr.comp (Completion.rareWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))) (NetworkAt.constant (fun _=>true))
      ((hr.comp (Completion.guessWires_at len (fun x=>OrderSlots.ordinaryWidth (len x))
        (fun x=>Completion.transitionWidth (len x)) (fun x=>2*len x) (fun x=>((len x+10)*(len x)^5)))).zeroWord hw)
lemma retainedOrderFilter_at
    {a m : ∀x,BooleanNetwork ((M x).width (t x)) (len x)}
    {raw : ∀x,BooleanNetwork ((M x).width (t x)) (OrderSlots.width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).retainedOrderFilter (t x) (a x) (m x) (raw x)) :=
  ((NetworkAt.usableOn (PolyAt.self len) ha hm).band (orderActualFilter_at ht hq ha hm hr)).bor
    ((NetworkAt.usableOn (PolyAt.self len) ha hm).bnot.band (orderDummyFilter_at ht hq ha hm hr))
end NodeMachine
end ExactQuantumFactoring

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedSplitPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
lemma primeWord {α : Type*} {len n : α→ℕ} (hn : PolyAt len n) :
    NetworkAt len (fun x=>BitArithmetic.primeWord (n x)) :=
  of_le (PolyAt.comp PreparationPolynomial.primeBound_poly hn) (fun x=>primeWord_count (n x))
lemma perfectPowerNet {α : Type*} {len n : α→ℕ} (hn : PolyAt len n) :
    NetworkAt len (fun x=>BitArithmetic.perfectPowerNet (n x)) :=
  of_le (((hn.add (PolyAt.const len 1)).mul
    ((PolyAt.comp PreparationPolynomial.perfectCheckBound_poly hn).add (PolyAt.const len 4))).add
    (PolyAt.const len 1)) (fun x=>perfectPowerNet_count (n x))
lemma hardOn {α : Type*} {len a n : α→ℕ} {m : ∀x,BooleanNetwork (a x) (n x)}
    (hn : PolyAt len n) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>UniversalSplit.hardOn (m x)) := by
  have hr:=PolyAt.comp PreparationPolynomial.rootWidth_poly hn
  exact (((NetworkAt.wordConstant _ hn).wordLe hm hn).band (hm.comp (primeWord hn)).bnot).band
    ((hm.evenOn hn).bnot.band ((hm.comp (NetworkAt.resizeWord hn hr)).comp (perfectPowerNet hn)).bnot)
end NetworkAt
namespace NodeMachine
variable {α : Type*} {len c t : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
variable (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query))
variable {raw : ∀x,BooleanNetwork ((M x).width (t x)) (FixedSplit.width (len x))}
variable (hr : NetworkAt len raw)
include hr
omit ht hq in
lemma splitModulus_at : NetworkAt len (fun x=>(M x).splitModulus (t x) (raw x)) :=
  hr.comp (FixedSplit.modulusNet_poly.pull len)
omit ht hq in
lemma splitList_at : NetworkAt len (fun x=>(M x).splitList (t x) (raw x)) :=
  (hr.comp (NetworkAt.select _)).comp (NetworkAt.select _)
omit ht hq in
lemma splitBase_at : NetworkAt (fun xi : Σx,Fin ((len x)^5)=>len xi.1)
    (fun xi=>(M xi.1).splitBase (t xi.1) (raw xi.1) xi.2) := by
  unfold splitBase
  with_reducible
    exact (hr.pull (fun xi : Σx,Fin ((len x)^5)=>xi.1)).comp
      (FixedSplit.actualBaseNet_poly.pull (fun xi : Σx,Fin ((len x)^5)=>⟨len xi.1,xi.2⟩))
omit ht hq in
lemma splitOrder_at : NetworkAt (fun xi : Σx,Fin ((len x)^5)=>len xi.1)
    (fun xi=>(M xi.1).splitOrder (t xi.1) (raw xi.1) xi.2) := by
  unfold splitOrder
  with_reducible
    exact (hr.pull (fun xi : Σx,Fin ((len x)^5)=>xi.1)).comp
      (FixedSplit.actualOrderRawNet_poly.pull (fun xi : Σx,Fin ((len x)^5)=>⟨len xi.1,xi.2⟩))
include ht hq in
lemma splitActualFilter_at (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>(M x).splitActualFilter (hpos x) (t x) (raw x)) := by
  let pull : (Σx,Fin ((len x)^5))→α:=Sigma.fst
  exact (retainedListFilter_at ht hq hpos (splitModulus_at hr) (splitList_at hr)).band
    (NetworkAt.all_ofFn ((PolyAt.self len).pow 5)
      (retainedOrderFilter_at (ht.pull pull) (hq.pull pull) (splitBase_at hr)
        ((splitModulus_at hr).pull pull) (splitOrder_at hr)))
include ht hq in
lemma splitDummyFilter_at :
    NetworkAt len (fun x=>(M x).splitDummyFilter (t x) (raw x)) := by
  let pull : (Σx,Fin ((len x)^5))→α:=Sigma.fst
  exact (listDummyFilter_at ht hq (splitModulus_at hr) (splitList_at hr)).band
    (NetworkAt.all_ofFn ((PolyAt.self len).pow 5)
      (orderDummyFilter_at (ht.pull pull) (hq.pull pull) (splitBase_at hr)
        ((splitModulus_at hr).pull pull) (splitOrder_at hr)))
include ht hq in
lemma retainedSplitFilter_at (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>(M x).retainedSplitFilter (hpos x) (t x) (raw x)) := by
  have hh:=NetworkAt.hardOn (PolyAt.self len) (splitModulus_at hr)
  exact (hh.band (splitActualFilter_at ht hq hr hpos)).bor
    (hh.bnot.band (splitDummyFilter_at ht hq hr))
end NodeMachine
end ExactQuantumFactoring

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedPrefixPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace SplitMachine
lemma previousNet_count {n c : ℕ} (M : SplitMachine n c) (s : ℕ) :
    (M.previousNet s).net.count=0 := by
  simp only [previousNet,count_comp,count_select,Nat.add_zero]
lemma lastSplitNet_count {n c : ℕ} (M : SplitMachine n c) (s : ℕ) :
    (M.lastSplitNet s).net.count=0 := by
  simp only [lastSplitNet,count_comp,count_select,Nat.add_zero]
end SplitMachine
namespace NodeMachine
lemma nodePrefixFilter_count {n c : ℕ} (M : NodeMachine n c) (hn : 0<n) (T B C : ℕ)
    (h : ∀v : BooleanNetwork (M.width T) (FixedSplit.width n),v.net.count≤B→
      (M.retainedSplitFilter hn T v).net.count≤C)
    (s : ℕ) (v : BooleanNetwork (M.width T) ((PhysicalNode.machine n (2*n)).width s))
    (hv : v.net.count≤B) : (M.nodePrefixFilter hn T s v).net.count≤ s*(C+1)+1 := by
  induction s with
  | zero=>simp only [nodePrefixFilter,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ s ih=>
    have hi:=ih (v.comp ((PhysicalNode.machine n (2*n)).previousNet s)) (by
      simpa only [count_comp,SplitMachine.previousNet_count,Nat.add_zero] using hv)
    have hh:=h (v.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s)) (by
      simpa only [count_comp,SplitMachine.lastSplitNet_count,Nat.add_zero] using hv)
    simp only [nodePrefixFilter,count_band]
    nlinarith
lemma nodePrefixFilter_at {α : Type*} {len c T s : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len T) (hs : PolyAt len s)
    (hq : NetworkAt len (fun x=>(M x).query))
    {raw : ∀x,BooleanNetwork ((M x).width (T x)) ((PhysicalNode.machine (len x) (2*len x)).width (s x))}
    (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).nodePrefixFilter (hpos x) (T x) (s x) (raw x)) := by
  let ix:=Σx,{v : BooleanNetwork ((M x).width (T x)) (FixedSplit.width (len x)) // v.net.count≤(raw x).net.count}
  let fst : ix→α:=Sigma.fst
  have hv : NetworkAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val):=
    NetworkAt.of_le (hr.pull fst) (fun xi=>xi.2.property)
  obtain ⟨p,hp⟩:=retainedSplitFilter_at (ht.pull fst) (hq.pull fst) hv (fun xi:ix=>hpos xi.1)
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply NetworkAt.of_le ((hs.mul (hc.add (PolyAt.const len 1))).add (PolyAt.const len 1))
  intro x
  exact nodePrefixFilter_count (M x) (hpos x) (T x) (raw x).net.count (p.eval (len x))
    (fun v hh=>hp ⟨x,v,hh⟩) (s x) (raw x) le_rfl
lemma retainedNodeFilter_at {α : Type*} {len c T : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len T)
    (hq : NetworkAt len (fun x=>(M x).query))
    {raw : ∀x,BooleanNetwork ((M x).width (T x)) (NodeKernel.width (len x))}
    (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).retainedNodeFilter (hpos x) (T x) (raw x)) :=
  nodePrefixFilter_at hpos ht ((PolyAt.const len 2).mul (PolyAt.self len)) hq hr
lemma treePrefixFilter_count {n c : ℕ} (M : NodeMachine n c) (hn : 0<n) (T B C : ℕ)
    (h : ∀v : BooleanNetwork (M.width T) (NodeKernel.width n),v.net.count≤B→
      (M.retainedNodeFilter hn T v).net.count≤C)
    (s : ℕ) (v : BooleanNetwork (M.width T) (M.width s))
    (hv : v.net.count≤B) : (M.treePrefixFilter hn T s v).net.count≤ s*(C+1)+1 := by
  induction s with
  | zero=>simp only [treePrefixFilter,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ s ih=>
    have hi:=ih (v.comp (M.previousNet s)) (by
      simpa only [count_comp,previousNet_count,Nat.add_zero] using hv)
    have hh:=h (v.comp (M.lastNodeNet s)) (by
      simpa only [count_comp,lastNodeNet_count,Nat.add_zero] using hv)
    simp only [treePrefixFilter,count_band]
    nlinarith
lemma treePrefixFilter_at {α : Type*} {len c T s : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len T) (hs : PolyAt len s)
    (hq : NetworkAt len (fun x=>(M x).query))
    {raw : ∀x,BooleanNetwork ((M x).width (T x)) ((M x).width (s x))}
    (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).treePrefixFilter (hpos x) (T x) (s x) (raw x)) := by
  let ix:=Σx,{v : BooleanNetwork ((M x).width (T x)) (NodeKernel.width (len x)) // v.net.count≤(raw x).net.count}
  let fst : ix→α:=Sigma.fst
  have hv : NetworkAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val):=
    NetworkAt.of_le (hr.pull fst) (fun xi=>xi.2.property)
  obtain ⟨p,hp⟩:=retainedNodeFilter_at (fun xi:ix=>hpos xi.1) (ht.pull fst) (hq.pull fst) hv
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply NetworkAt.of_le ((hs.mul (hc.add (PolyAt.const len 1))).add (PolyAt.const len 1))
  intro x
  exact treePrefixFilter_count (M x) (hpos x) (T x) (raw x).net.count (p.eval (len x))
    (fun v hh=>hp ⟨x,v,hh⟩) (s x) (raw x) le_rfl
end NodeMachine
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring
open BooleanNetwork

namespace NetworkPoly
variable {a b c : ℕ→ℕ}
lemma select (h : ∀ n,Fin (b n)→Fin (a n)) : NetworkPoly (fun n=>BooleanNetwork.select (h n)) := by
  simpa only [NetworkPoly,count_select] using PolyBound.const 0
lemma comp {f : ∀ n,BooleanNetwork (a n) (b n)} {g : ∀ n,BooleanNetwork (b n) (c n)}
    (hf : NetworkPoly f) (hg : NetworkPoly g) : NetworkPoly (fun n=>(f n).comp (g n)) := by
  simpa only [NetworkPoly,count_comp] using PolyBound.add hf hg
lemma pair {f : ∀ n,BooleanNetwork (a n) (b n)} {g : ∀ n,BooleanNetwork (a n) (c n)}
    (hf : NetworkPoly f) (hg : NetworkPoly g) : NetworkPoly (fun n=>(f n).pair (g n)) := by
  simpa only [NetworkPoly,count_pair] using PolyBound.add hf hg
end NetworkPoly

end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodePreparationPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PreparationPolynomial
lemma nodeConfig : PolyBound (fun n=>PhysicalNode.configWidth n (2*n)) := by
  unfold PhysicalNode.configWidth NodeStateCircuit.width
  repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma nodeQuery : NetworkPoly (fun n=>PhysicalNode.query n (2*n)) := by
  apply PolyBound.id.of_le
  intro n
  simpa only [PhysicalNode.query,count_comp,NodeStateCircuit.top_count,zero_add]
    using resizeWord_count (n+1) n
lemma nodeStep : NetworkPoly (fun n=>NodeStateCircuit.step (2*n) (n+1)) := by
  apply PolyBound.of_le (g:=fun n=>NodeStateCircuit.stepBound (2*n) (n+1))
  · exact nodeStepBound_poly ((PolyAt.const id 2).mul (PolyAt.self id))
      ((PolyAt.self id).add (PolyAt.const id 1))
  · intro n;exact NodeStateCircuit.step_count _ _
lemma nodeUpdate : NetworkPoly (fun n=>PhysicalNode.update n (2*n)) :=
  ((NetworkPoly.select _).pair ((NetworkPoly.select _).comp FixedSplit.divisorNet_poly)).comp nodeStep
lemma nodeInitWork : PolyBound (fun n=>(PhysicalNode.machine n (2*n)).initWork) :=
  nodeQuery.add splitInitial
lemma nodeUpdateWork : PolyBound (fun n=>(PhysicalNode.machine n (2*n)).updateWork) := nodeUpdate
lemma nodeWidth : PolyBound NodeKernel.width := by
  change PolyBound (fun n=>(PhysicalNode.machine n (2*n)).width (2*n))
  simp only [SplitMachine.width_eq]
  have :=nodeConfig;have:=splitWidth;have:=nodeInitWork;have:=nodeUpdateWork
  repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma machineNodeInitial : PolyBound (fun n=>((PhysicalNode.machine n (2*n)).initialNet (2*n)).net.count) := by
  simp only [SplitMachine.initialNet_count]
  have :=nodeConfig;have:=splitWidth;have:=nodeInitWork;have:=nodeUpdateWork
  repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma nodeStart : NetworkPoly PhysicalNode.startNet := by
  apply PolyBound.of_le (g:=fun n=>(2*n+1)*(n+1)*((n+1)+(2*n+1)*(n+1))+(2*n+1)*(n+1)+1)
  · repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · intro n
    have hh:=stackPush_count (resizeWord n (n+1)) (Completion.zeros n ((2*n+1)*(n+1)))
    simp only [Completion.zeros_count] at hh
    have hr:=resizeWord_count n (n+1)
    have hh' :=hh.trans (Nat.mul_le_mul_left ((2*n+1)*(n+1)) (Nat.add_le_add_right hr _))
    simp only [PhysicalNode.startNet,count_pair,Completion.zeros_count,count_constant]
    omega
lemma nodeInitial : NetworkPoly NodeKernel.initialNet := nodeStart.comp machineNodeInitial
lemma nodeSteps : PolyBound (fun n=>(NodeKernel.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>2*n*(4*(PhysicalNode.machine n (2*n)).initWork+
    2*FixedSplit.width n+(FixedSplit.program n).length+
    4*(PhysicalNode.machine n (2*n)).updateWork+2*PhysicalNode.configWidth n (2*n)))
  · have :=nodeInitWork;have:=splitWidth;have:=splitSteps;have:=nodeUpdateWork;have:=nodeConfig
    repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · intro n;exact SplitMachine.program_length _ _
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QuarterConstantResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
namespace RatHeightPoly
variable {a : ℕ→ℚ}
lemma floor (ha : RatHeightPoly a) : PolyBound (fun n=>(Int.floor (a n)).natAbs.size) := by
  apply ha.1.of_le
  intro n
  apply Nat.size_le_size
  rw [Rat.floor_def']
  exact Int.natAbs_ediv_le_natAbs _ _
end RatHeightPoly
namespace Exactness
lemma completionCoeff_height {E : ℕ→ℕ} {z A : ℕ→ℚ} (hE : PolyBound E)
    (hz : RatHeightPoly z) (hA : RatHeightPoly A) :
    RatHeightPoly (fun n=>completionCoeff (E n) (z n) (A n)) := by
  have hpow:=(RatHeightPoly.constant 2).pow hE
  exact (RatHeightPoly.intCast (hpow.mul (hz.div hA)).floor).div hpow
lemma quarterCoeff_height {J : ℕ→ℕ} {p : ℕ→ℚ} (hJ : PolyBound J) (hp : RatHeightPoly p) :
    RatHeightPoly (fun n=>quarterCoeff (J n) (p n)) :=
  completionCoeff_height (hJ.add (PolyBound.const 2)) (RatHeightPoly.constant (1/2)) hp
lemma quarterRemainder_height {J : ℕ→ℕ} {p : ℕ→ℚ} (hJ : PolyBound J) (hp : RatHeightPoly p) :
    RatHeightPoly (fun n=>quarterRemainder (J n) (p n)) :=
  (RatHeightPoly.constant (1/4)).sub ((hp.mul (quarterCoeff_height hJ hp)).div (RatHeightPoly.constant 2))
lemma knownProbability_height : RatHeightPoly knownProbability :=
  ((RatHeightPoly.constant 1).sub ((RatHeightPoly.constant 1).div
    ((RatHeightPoly.constant 2).pow PolyBound.id))).pow (PolyBound.id.pow 10)
end Exactness
namespace Quarter
lemma retention_height : RatHeightPoly retention :=
  Exactness.quarterCoeff_height (PolyBound.id.mul PolyBound.id) Exactness.knownProbability_height
lemma guessRetention_height : RatHeightPoly guessRetention :=
  ((RatHeightPoly.constant 2).pow ((PolyBound.id.mul PolyBound.id).add (PolyBound.const 1))).mul
    (Exactness.quarterRemainder_height (PolyBound.id.mul PolyBound.id) Exactness.knownProbability_height)
lemma D_poly : PolyBound D := by
  unfold D Completion.coinBits
  repeat' (first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
end Quarter
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreePreparationPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PreparationPolynomial
lemma treeConfig : PolyBound PhysicalTree.configWidth := by
  unfold PhysicalTree.configWidth PhysicalTree.capacity;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma treeQuery_count (n : ℕ) : (PhysicalTree.query n).net.count=0 := by
  simp only [PhysicalTree.query,blockNet,count_select]
lemma treeQuery : NetworkPoly PhysicalTree.query := by
  simp only [NetworkPoly,treeQuery_count];exact PolyBound.const 0
lemma treePushed : NetworkPoly PhysicalTree.pushed := by
  apply PolyBound.of_le (g:=fun n=>PhysicalTree.capacity n*n*n+n*ChildQueue.oneBound
    (PhysicalTree.capacity n) n (PhysicalNode.resultBound n) n)
  · have cap : PolyBound PhysicalTree.capacity :=by unfold PhysicalTree.capacity;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
    have res : PolyBound PhysicalNode.resultBound :=
      (PolyBound.id.mul PolyBound.id).add ((PolyBound.id.mul PolyBound.id).mul
        (((PolyBound.const 498).mul PolyBound.id).add (PolyBound.const 114)))
    have lin : PolyBound (fun n=>2*PhysicalNode.resultBound n+96*n+25) :=
      (((PolyBound.const 2).mul res).add ((PolyBound.const 96).mul PolyBound.id)).add (PolyBound.const 25)
    have lin' : PolyBound (fun n=>PhysicalNode.resultBound n+159*n+6) :=
      (res.add ((PolyBound.const 159).mul PolyBound.id)).add (PolyBound.const 6)
    have one : PolyBound (fun n=>ChildQueue.oneBound (PhysicalTree.capacity n) n (PhysicalNode.resultBound n) n) :=
      (((((res.add ((PolyBound.const 49).mul PolyBound.id)).add (PolyBound.const 11)).add
        (PolyBound.id.mul lin)).add ((cap.mul PolyBound.id).mul lin')).add
          ((PolyBound.const 7).mul (cap.mul PolyBound.id)))
    exact ((cap.mul PolyBound.id).mul PolyBound.id).add (PolyBound.id.mul one)
  · intro n
    have h:=ChildQueue.pushAll_count (PhysicalTree.capacity n) (PhysicalTree.fields n)
      (c:=PhysicalNode.resultBound n) (by
        intro b hb
        obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hb
        simpa only [count_comp,tensorSelect,count_select,add_zero]
          using PhysicalTree.nodeResult_count n)
    have hs:=stackPop_count (PhysicalTree.capacity n) n
    have hh:=Nat.add_le_add hs h
    simpa only [PhysicalTree.pushed,PhysicalTree.localNode,PhysicalTree.old,
      count_comp,count_pair,count_select,ChildQueue.queue,
      zero_add,add_zero,PhysicalTree.fields,List.length_ofFn] using hh
lemma treeUpdate : NetworkPoly PhysicalTree.update := by
  apply PolyBound.of_le (g:=fun n=>97*n+21+7*PhysicalTree.configWidth n+(PhysicalTree.pushed n).net.count)
  · exact ((((PolyBound.const 97).mul PolyBound.id).add (PolyBound.const 21)).add
      ((PolyBound.const 7).mul treeConfig)).add treePushed
  · intro n
    have h:=zeroWord_count ((PhysicalTree.old n).comp (PhysicalTree.query n))
    simp only [count_comp,PhysicalTree.old,count_select,treeQuery_count,zero_add] at h
    simp only [PhysicalTree.update,wordMux_count,PhysicalTree.old,count_select]
    omega
lemma treeInitWork : PolyBound (fun n=>(PhysicalTree.machine n).initWork) :=
  treeQuery.add nodeInitial
lemma treeUpdateWork : PolyBound (fun n=>(PhysicalTree.machine n).updateWork) :=treeUpdate
lemma treeWidth : PolyBound PhysicalTree.width := by
  change PolyBound (fun n=>(PhysicalTree.machine n).width (PhysicalTree.steps n))
  simp only [NodeMachine.width_eq]
  have :=treeConfig;have :=nodeWidth;have :=treeInitWork;have :=treeUpdateWork
  unfold PhysicalTree.steps;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma treeMachineInitial : PolyBound (fun n=>((PhysicalTree.machine n).initialNet
    (PhysicalTree.steps n)).net.count) := by
  simp only [NodeMachine.initialNet_count]
  have :=treeConfig;have :=nodeWidth;have :=treeInitWork;have :=treeUpdateWork
  unfold PhysicalTree.steps;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma treeStart : NetworkPoly PhysicalTree.startNet := by
  apply PolyBound.of_le (g:=fun n=>PhysicalTree.capacity n*n*(PhysicalTree.capacity n*n))
  · unfold PhysicalTree.capacity;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · intro n
    simpa only [PhysicalTree.startNet,count_select,Completion.zeros_count,zero_add]
      using stackPush_count (select (n:=n) id) (Completion.zeros n (PhysicalTree.configWidth n))
lemma treeLaunchWork : PolyBound PhysicalTree.launchWork :=treeStart.comp treeMachineInitial
lemma treeSteps : PolyBound (fun n=>((PhysicalTree.machine n).program (PhysicalTree.steps n)).length) := by
  apply PolyBound.of_le (g:=fun n=>PhysicalTree.steps n*(4*(PhysicalTree.machine n).initWork+
    2*NodeKernel.width n+(NodeKernel.program n).length+
    4*(PhysicalTree.machine n).updateWork+2*PhysicalTree.configWidth n))
  · have :=treeInitWork;have :=nodeWidth;have :=nodeSteps;have :=treeUpdateWork;have :=treeConfig
    unfold PhysicalTree.steps;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · intro n;exact NodeMachine.program_length _ _
lemma treeLaunchWidth : PolyBound PhysicalTree.launchWidth :=by
  unfold PhysicalTree.launchWidth
  have :=treeWidth;have :=treeLaunchWork;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma treePadding : PolyBound PhysicalTree.padding := by
  apply (PolyBound.id.pow 10).of_le
  intro n;exact Nat.sub_le _ _
lemma treePaddedWidth : PolyBound PhysicalTree.paddedWidth :=by
  unfold PhysicalTree.paddedWidth
  simp only [tensorWidth_eq]
  exact treeLaunchWidth.add (treePadding.mul PolyBound.id)
lemma treePaddedSteps : PolyBound (fun n=>(PhysicalTree.paddedProgram n).length) :=by
  apply PolyBound.of_le (g:=fun n=>4*PhysicalTree.launchWork n+2*PhysicalTree.width n+
    ((PhysicalTree.machine n).program (PhysicalTree.steps n)).length+PhysicalTree.padding n*n)
  · have :=treeLaunchWork;have :=treeWidth;have :=treeSteps;have :=treePadding;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
  · exact PhysicalTree.paddedProgram_length
lemma quarterWidth : PolyBound PhysicalTree.quarterWidth :=by
  unfold PhysicalTree.quarterWidth
  exact (PolyBound.const 1).add (treePaddedWidth.add ((PolyBound.id.mul PolyBound.id).add Quarter.D_poly))
lemma quarterSteps : PolyBound (fun n=>(PhysicalTree.quarterProgram n).length) :=by
  simp only [PhysicalTree.quarterProgram_length]
  exact ((treePaddedSteps.add (PolyBound.const 1)).add (PolyBound.id.mul PolyBound.id)).add Quarter.D_poly
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedQuarterPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PreparationPolynomial
lemma factorVerifierBound_at {α : Type*} {len n c : α→ℕ}
    (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>factorVerifierBound (n x) (c x)) := by
  have hr:=PolyAt.comp rootWidth_poly hn
  have hp:=PolyAt.comp primalityBound_poly hn
  have hprod:= (hn.mul ((((((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 105).mul hn)).add
    (PolyAt.const len 21)).add hr).add (((PolyAt.const len 90).mul hr).mul hr)).add
    ((PolyAt.const len 14).mul hr)).add (PolyAt.const len 6))).add hr
  have hfirst:= (hn.mul (((((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 146).mul hn)).add
    (PolyAt.const len 35)).add hr).add hp).add (PolyAt.const len 1))).add (PolyAt.const len 1)
  have hsecond:= ((hn.mul hn).mul ((((PolyAt.const len 4).mul hc).add
    ((PolyAt.const len 242).mul hn)).add (PolyAt.const len 58))).add (PolyAt.const len 1)
  exact ((((hfirst.add hsecond).add (PolyAt.const len 1)).add
    ((((hprod.add hc).add hr).add ((PolyAt.const len 96).mul hr)).add (PolyAt.const len 21))).add
      (PolyAt.const len 1))
lemma physicalResultBound : PolyBound PhysicalNode.resultBound := by
  exact (PolyBound.id.mul PolyBound.id).add ((PolyBound.id.mul PolyBound.id).mul
    (((PolyBound.const 498).mul PolyBound.id).add (PolyBound.const 114)))
end PreparationPolynomial
namespace NodeMachine
lemma rowBound_at {α : Type*} {len n c : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
    (hn : PolyAt len n) (hq : NetworkAt len (fun x=>(M x).query)) :
    PolyAt len (fun x=>(M x).rowBound) := by
  have hr:=PolyAt.comp PreparationPolynomial.physicalResultBound hn
  exact (((PolyAt.add hq ((PolyAt.const len 97).mul hn)).add (PolyAt.const len 25)).add
    (PreparationPolynomial.factorVerifierBound_at hn (PolyAt.add hq hr)))
lemma verifiedNet_at {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
    (hn : PolyAt len n) (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query)) :
    NetworkAt len (fun x=>(M x).verifiedNet (t x)) :=
  NetworkAt.of_le ((ht.mul ((rowBound_at hn hq).add (PolyAt.const len 1))).add (PolyAt.const len 1))
    (fun x=>(M x).verifiedNet_count (t x))
lemma acceptedNet_at {α : Type*} {len c t : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query)) :
    NetworkAt len (fun x=>(M x).acceptedNet (hpos x) (t x)) :=
  (verifiedNet_at (PolyAt.self len) ht hq).band
    (treePrefixFilter_at hpos ht ht hq (NetworkAt.select (fun _=>id)))
end NodeMachine
namespace PhysicalTree
lemma padFlag_poly : NetworkPoly padFlag := by
  unfold padFlag
  exact NetworkAt.all_ofFn PreparationPolynomial.treePadding
    (((NetworkAt.select _).zeroWord (PolyAt.self (fun xi:Σn,Fin (padding n)=>xi.1))).bnot)
lemma paddedFlag_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>paddedFlag (len x) (hpos x)) := by
  have ht : PolyAt len (fun x=>2*(len x)^2):=(PolyAt.const len 2).mul ((PolyAt.self len).pow 2)
  have hq : NetworkAt len (fun x=>(machine (len x)).query):=NetworkAt.ofPoly PreparationPolynomial.treeQuery len
  have ha:=NodeMachine.acceptedNet_at hpos ht hq
  exact (((NetworkAt.select _).comp (NetworkAt.select _)).comp ha).band
    ((NetworkAt.select _).comp (NetworkAt.ofPoly padFlag_poly len))
lemma guessVerifier_poly : NetworkPoly guessVerifier := by
  apply NetworkAt.of_le (PreparationPolynomial.factorVerifierBound_at (PolyAt.self id) (PolyAt.const id 0))
  intro n
  exact factorVerifierOn_count _ _ (by simp only [count_select,le_refl]) (by intro i;simp only [count_select,le_refl])
lemma quarterGuessFlag_poly : NetworkPoly quarterGuessFlag :=
  ((((NetworkAt.select _).comp ((NetworkAt.select _).comp (NetworkAt.select _))).pair
    (NetworkAt.select _)).comp guessVerifier_poly)
lemma quarterRare_poly : NetworkPoly quarterRare :=
  ((NetworkAt.select _).zeroWord (PolyAt.const id 1))
lemma quarterKeep_poly {p : ℕ→ℚ} (hp : RatHeightPoly p) :
    NetworkPoly (fun n=>quarterKeep n (p n)) := by
  unfold quarterKeep
  exact retentionNet_at Quarter.D_poly (RatExprPoly.ofHeight hp) (NatExprPoly.var (fun _=>()))
    Quarter.D_poly ⟨0,fun n i=>by simp only [quarterCoin,Completion.retentionWires,count_select,Polynomial.eval_zero,le_refl]⟩
lemma quarterFlag_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>quarterFlag (len x) (hpos x)) := by
  have hr:=NetworkAt.ofPoly quarterRare_poly len
  have hp:=paddedFlag_at len hpos
  have hk:=NetworkAt.ofPoly (quarterKeep_poly Quarter.retention_height) len
  have hg:=NetworkAt.ofPoly (quarterKeep_poly Quarter.guessRetention_height) len
  have hv:=NetworkAt.ofPoly quarterGuessFlag_poly len
  exact (hr.bnot.band (((NetworkAt.select _).comp hp).band hk)).bor (hr.band (hv.band hg))
end PhysicalTree
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeFinalResources
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
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma amplifiedProgram_length (n : ℕ) (hn : 0<n) :
    (amplifiedProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+8*(zeroNet n).net.count+12 :=
  amplificationProgram_length _ _ _ _ _

lemma amplifiedOutput_count (n : ℕ) (hn : 0<n) :
    (amplifiedOutput n hn).net.count=(quarterOutputNet n).net.count := by
  simp only [amplifiedOutput,count_comp,count_select,Nat.zero_add]

lemma paddedHistory_count (n : ℕ) : (paddedHistory n).net.count=0 := by
  simp only [paddedHistory,launchHistory,count_comp,count_select,Nat.zero_add]

lemma paddedOutputNet_count (n : ℕ) :
    (paddedOutputNet n).net.count=(rootFlat n (2*n^2)).net.count := by
  simp only [paddedOutputNet,count_comp,paddedHistory_count,Nat.zero_add]

lemma quarterOutputNet_count (n : ℕ) :
    (quarterOutputNet n).net.count≤(rootFlat n (2*n^2)).net.count+7*(n*n)+118 := by
  have h:=Completion.outputNet_count (paddedOutputNet n) 1 (n^11)
  rw [paddedOutputNet_count] at h
  change (Completion.outputNet (paddedOutputNet n) 1 (n^11)).net.count≤_
  omega

lemma factoringProgram_length (n : ℕ) (hn : 0<n) :
    (factoringProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+8*(zeroNet n).net.count+
      4*(quarterOutputNet n).net.count+2*(n*n)+12 := by
  have h₁:=readoutProgram_length (amplifiedProgram n hn) (amplifiedOutput n hn) le_rfl
  have h₂:=amplifiedProgram_length n hn
  have hc:=amplifiedOutput_count n hn
  change (readoutProgram (amplifiedProgram n hn) (amplifiedOutput n hn) le_rfl).length≤_
  omega

lemma readoutWidth_bound (n : ℕ) (hn : 0<n) :
    readoutWidth n hn≤quarterWidth n+1+(quarterFlag n hn).net.count+
      (zeroNet n).net.count+n*n+(quarterOutputNet n).net.count := by
  have hc:=amplifiedOutput_count n hn
  change quarterWidth n+1+max (quarterFlag n hn).net.count (zeroNet n).net.count+
    n*n+(amplifiedOutput n hn).net.count≤_
  omega

/-- Concrete reduction of the remaining whole-program resource obligation to
its literal preparation, accepted-event network, and root readout. These are
counts of actual gates/wires, not an assumed big-O charge for arithmetic. -/
theorem factoringProgram_resources (n : ℕ) (hn : 0<n) :
    (factoringProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+16*quarterWidth n+
      4*(rootFlat n (2*n^2)).net.count+30*(n*n)+492 ∧
    readoutWidth n hn≤3*quarterWidth n+(quarterFlag n hn).net.count+
      (rootFlat n (2*n^2)).net.count+8*(n*n)+120 := by
  have h₁:=factoringProgram_length n hn
  have h₂:=readoutWidth_bound n hn
  have h₃:=zeroNet_count n
  have h₄:=quarterOutputNet_count n
  constructor <;> omega

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeReadoutResources
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
namespace PhysicalTree

lemma flattenWords_count (n : ℕ) : (flattenWords n).net.count=0 := by
  have h:=wordBlocks_count (fun i : Fin n=>tensorSelect n n i)
    (c:=0) (fun _=>by simp only [tensorSelect,count_select,le_refl])
  change (flattenWords n).net.count≤n*n*0 at h
  omega

lemma rootFlat_count (n t : ℕ) :
    (rootFlat n t).net.count≤n*n+PhysicalNode.resultBound n := by
  cases t with
  | zero=>simp only [rootFlat,Completion.zeros_count];omega
  | succ t=>
    have h:=nodeResult_count n
    simp only [rootFlat,rootResult,count_comp,NodeMachine.firstNodeNet_count,
      flattenWords_count,Nat.zero_add,Nat.add_zero]
    omega

/-- All readout overhead is now bounded by an explicit polynomial expression;
the two remaining size estimates are preparation and same-history flagging. -/
theorem factoringProgram_resources_reduced (n : ℕ) (hn : 0<n) :
    (factoringProgram n hn).length≤3*(quarterProgram n).length+
      8*(quarterFlag n hn).net.count+16*quarterWidth n+
      4*PhysicalNode.resultBound n+34*(n*n)+492 ∧
    readoutWidth n hn≤3*quarterWidth n+(quarterFlag n hn).net.count+
      PhysicalNode.resultBound n+9*(n*n)+120 := by
  have h₁:=factoringProgram_resources n hn
  have h₂:=rootFlat_count n (2*n^2)
  constructor <;> omega

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FinalPolynomialResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
namespace PhysicalTree
lemma factoringProgram_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    PolyAt len (fun x=>(factoringProgram (len x) (hpos x)).length) := by
  have hprep:=PolyAt.ofPoly PreparationPolynomial.quarterSteps len
  have hflag : PolyAt len (fun x=>(quarterFlag (len x) (hpos x)).net.count):=quarterFlag_at len hpos
  have hwidth:=PolyAt.ofPoly PreparationPolynomial.quarterWidth len
  have hresult:=PolyAt.ofPoly PreparationPolynomial.physicalResultBound len
  exact (((((((PolyAt.const len 3).mul hprep).add ((PolyAt.const len 8).mul hflag)).add
    ((PolyAt.const len 16).mul hwidth)).add ((PolyAt.const len 4).mul hresult)).add
      ((PolyAt.const len 34).mul ((PolyAt.self len).mul (PolyAt.self len)))).add
        (PolyAt.const len 492)).of_le (fun x=>(factoringProgram_resources_reduced (len x) (hpos x)).1)
lemma readoutWidth_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    PolyAt len (fun x=>readoutWidth (len x) (hpos x)) := by
  have hflag : PolyAt len (fun x=>(quarterFlag (len x) (hpos x)).net.count):=quarterFlag_at len hpos
  have hwidth:=PolyAt.ofPoly PreparationPolynomial.quarterWidth len
  have hresult:=PolyAt.ofPoly PreparationPolynomial.physicalResultBound len
  exact ((((((PolyAt.const len 3).mul hwidth).add hflag).add hresult).add
    ((PolyAt.const len 9).mul ((PolyAt.self len).mul (PolyAt.self len)))).add
      (PolyAt.const len 120)).of_le (fun x=>(factoringProgram_resources_reduced (len x) (hpos x)).2)
lemma paddedLength_poly : PolyBound paddedLength :=
  (PolyBound.const 128).max PolyBound.id
lemma finalCircuit_qubits_poly : PolyBound (fun ℓ=>(finalCircuit ℓ).qubits) := by
  obtain ⟨p,hp⟩:=readoutWidth_at paddedLength paddedLength_pos
  exact (PolyBound.comp (⟨p,fun _=>le_rfl⟩ : PolyBound (fun n=>p.eval n)) paddedLength_poly).of_le hp
lemma finalCircuit_gates_poly : PolyBound (fun ℓ=>(finalCircuit ℓ).instructions.length) := by
  obtain ⟨p,hp⟩:=factoringProgram_at paddedLength paddedLength_pos
  apply (PolyBound.comp (⟨p,fun _=>le_rfl⟩ : PolyBound (fun n=>p.eval n)) paddedLength_poly).of_le
  intro ℓ
  rw [finalCircuit_length]
  exact hp ℓ
theorem finalCircuit_resources_oai : PolynomialResources finalCircuit := by
  obtain ⟨p,hp⟩:=finalCircuit_qubits_poly
  obtain ⟨q,hq⟩:=finalCircuit_gates_poly
  refine ⟨p+q,fun ℓ=>?_⟩
  rw [Polynomial.eval_add]
  exact ⟨(hp ℓ).trans (Nat.le_add_right _ _),(hq ℓ).trans (Nat.le_add_left _ _)⟩
end PhysicalTree
end ExactQuantumFactoring

end


end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_resources_oai := @OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_resources_oai
