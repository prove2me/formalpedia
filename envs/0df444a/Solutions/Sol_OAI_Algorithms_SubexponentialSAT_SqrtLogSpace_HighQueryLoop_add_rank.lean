-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:33:44.251693+00:00
-- url     : https://prove2.me/submissions/504e39e7-82df-47fc-bad0-4b574699e9b2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Definitions.Def_OAIQ081S169

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem digits_two_eq_map_toNat (a : ℕ) :
    Nat.digits 2 a = a.bits.map Bool.toNat := by
  rw [Nat.digits_two_eq_bits]
  induction a.bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all

@[simp] theorem countWord_decode (a : ℕ) :
    Nat.ofDigits 2 ((countWord a).map Bool.toNat) = a := by
  by_cases h : a = 0
  · subst a
    rfl
  · rw [countWord, ite_eq_right h, ← digits_two_eq_map_toNat]
    exact Nat.ofDigits_digits 2 a

@[simp] theorem countWord_toNat (a : ℕ) : BinaryArithmetic.toNat (countWord a) = a := by
  have h (word : List Bool) :
      BinaryArithmetic.toNat word = Nat.ofDigits 2 (word.map Bool.toNat) := by
    induction word with
    | nil => rfl
    | cons b word ih =>
        cases b <;> simp [BinaryArithmetic.toNat, BinaryArithmetic.bitVal, ih,
          Nat.ofDigits]
  rw [h, countWord_decode]

theorem countWord_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (countWord a).length ≤ n + 1 := by
  by_cases h : a = 0
  · simp [countWord, h]
  · simpa only [countWord, ite_eq_right h, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer high-incidence cutoff and disjoint branching on original coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem sum_assignments_split {M : Type*} [AddCommMonoid M]
    (H : Finset V) (f : (V → Bool) → M) :
    ∑ x, f x = ∑ a : H → Bool, ∑ b : {v : V // v ∉ H} → Bool, f (glue H a b) := by
  calc
    _ = ∑ ab : (H → Bool) × ({v : V // v ∉ H} → Bool), f (glue H ab.1 ab.2) :=
      (Fintype.sum_equiv (assignmentEquiv H) _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighIncidenceStream
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact disjoint conditioning and bounded-width accumulation on original variables.
The finite sums below specify the stream; they are not materialized by its program.
The source is the sparse-query proof in counting-k-sat.tex, lines 1636–1698. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceStream

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A binary carry does not enlarge a bounded word unless the numerical result overflows.
This also permits leading zeroes, so the existing actual adder needs no normalization. -/
theorem length_carryAdd_of_lt (width : ℕ) (c : Bool) (xs : List Bool)
    (hx : xs.length ≤ width) (hv : toNat xs + bitVal c < 2 ^ width) :
    (carryAdd c xs).length ≤ width := by
  induction width generalizing c xs with
  | zero =>
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst xs
      cases c <;> simp_all [carryAdd, bitVal]
  | succ width ih =>
      cases xs with
      | nil => cases c <;> simp [carryAdd]
      | cons b xs =>
          have hx' : xs.length ≤ width := by simpa using hx
          have hf := fullAdder_correct false b c
          simp only [bitVal_false, zero_add] at hf
          have hv' : toNat xs + bitVal (carryBit false b c) < 2 ^ width := by
            simp only [toNat_cons, pow_succ] at hv
            omega
          simpa only [carryAdd, List.length_cons, Nat.succ_le_succ_iff] using ih
            (carryBit false b c) xs hx' hv'

theorem length_addCarry_of_lt (width : ℕ) (c : Bool) (xs ys : List Bool)
    (hx : xs.length ≤ width) (hy : ys.length ≤ width)
    (hv : toNat xs + toNat ys + bitVal c < 2 ^ width) :
    (addCarry c xs ys).length ≤ width := by
  induction width generalizing c xs ys with
  | zero =>
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hys : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst xs; subst ys
      cases c <;> simp_all [addCarry, carryAdd, bitVal]
  | succ width ih =>
      cases xs with
      | nil => exact length_carryAdd_of_lt (width + 1) c ys hy (by simpa using hv)
      | cons a xs =>
          have hx' : xs.length ≤ width := by simpa using hx
          cases ys with
          | nil =>
              have hf := fullAdder_correct a false c
              simp only [bitVal_false, add_zero] at hf
              have hv' : toNat xs + toNat [] + bitVal (carryBit a false c) < 2 ^ width := by
                simp only [toNat_cons, toNat_nil, add_zero, pow_succ] at hv ⊢
                omega
              simpa only [addCarry, List.length_cons, Nat.succ_le_succ_iff] using
                ih (carryBit a false c) xs [] hx' (by simp) hv'
          | cons b ys =>
              have hy' : ys.length ≤ width := by simpa using hy
              have hf := fullAdder_correct a b c
              have hv' : toNat xs + toNat ys + bitVal (carryBit a b c) < 2 ^ width := by
                simp only [toNat_cons, pow_succ] at hv
                omega
              simpa only [addCarry, List.length_cons, Nat.succ_le_succ_iff] using
                ih (carryBit a b c) xs ys hx' hy' hv'

theorem length_add_of_lt (width : ℕ) (xs ys : List Bool)
    (hx : xs.length ≤ width) (hy : ys.length ≤ width)
    (hv : toNat xs + toNat ys < 2 ^ width) :
    (add xs ys).length ≤ width :=
  length_addCarry_of_lt width false xs ys hx hy (by simpa using hv)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceStream
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rank semantics for the native all-visits Boolean odometer. These maps are
proof-level reindexings; the machine changes its physical tuple in place. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank
open scoped BigOperators

theorem sum_by_rank {H M : Type*} [Fintype H] [DecidableEq H] [AddCommMonoid M] {h : ℕ}
    (order : Fin h ≃ H) (f : (H → Bool) → M) :
    ∑ a, f a = ∑ r : Fin (2 ^ h), f (highEquiv order r) := by
  exact (Fintype.sum_equiv (highEquiv order) _ _ (fun _ => rfl)).symm

/-- Every original assignment occurs once in the outer rank sum and inner
free-coordinate sum. This is the exact count bridge, including unused vars. -/
theorem sum_original_by_rank {V M : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid M] (H : Finset V) (order : Fin H.card ≃ H)
    (f : (V → Bool) → M) :
    ∑ x, f x = ∑ r : Fin (2 ^ H.card),
      ∑ b : {v : V // v ∉ H} → Bool, f (HighIncidence.glue H (highEquiv order r) b) := by
  rw [HighIncidence.sum_assignments_split H f]
  exact sum_by_rank order _

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive integer accumulator used after each marked-clause count.
Both operands have runtime lengths. The fixed instruction table adds them
exactly and restores little-endian orientation; no arithmetic instruction or
precomputed mass is admitted into the machine model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Mass

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- This adds two binary words with an actual execution of the fixed adder. -/
theorem command_eval (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 1, ∃ regs',
      Eval command n (data regs acc next) (data regs' (BinaryArithmetic.add acc next) []) := by
  let reset := Function.update regs 0 false
  obtain ⟨regs', n, hn, ht⟩ := BinaryPrograms.Add.littleEndian_run reset acc next
  have hs : (StructuredProgram.Atom.set 0 false).eval (data regs acc next) =
      data reset acc next := by
    rfl
  refine ⟨1 + n, by omega, regs', ?_⟩
  apply Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 0 false) _))
  rw [hs]
  apply Eval.call
  have hentry : BinaryPrograms.Add.littleEndianProgram.entry = 0 := rfl
  simpa [data, reset, BinaryArithmetic.add, StructuredProgram.State.withPC, hentry] using ht

theorem program_trace (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 2, ∃ regs',
      Trace program n ((data regs acc next).withPC (some program.entry))
        ((data regs' (BinaryArithmetic.add acc next) []).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := command_eval regs acc next
  exact ⟨n + 1, by omega, regs', compiled_halt_trace ht 1 0⟩

variable {r s : ℕ}

theorem invoke_eval (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 3, ∃ regs',
      Eval (invoke p) n (state p frame regs acc next)
        (state p frame regs' (BinaryArithmetic.add acc next) []) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace regs acc next
  exact ⟨n, by omega, regs', eval_call_lifted program p.register p.stack frame
    p.register_injective p.stack_injective ht⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafBranchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The branch callback is a real residual-count program followed by the native
binary adder. Semantic branch counts occur only in its verification contract. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.ExecCNFTupleEnumeration

variable {R S : ℕ}

theorem mass_self (p : Ports R S) (a : State R S)
    (hs : a.stacks (p.mass.stack 2) = []) :
    LeafProgram.Mass.state p.mass a (fun i => a.regs (p.mass.register i))
      (read p a) (a.stacks (p.mass.stack 1)) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, p.mass.register j = i
    · obtain ⟨j, rfl⟩ := h
      exact embedState_register p.mass.register p.mass.stack a
        (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))) p.mass.register_injective j
    · exact embedState_register_frame p.mass.register p.mass.stack a
        (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))) i h
  · funext i
    by_cases h : ∃ j, p.mass.stack j = i
    · obtain ⟨j, rfl⟩ := h
      calc
        _ = (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))).stacks j :=
            embedState_stack p.mass.register p.mass.stack a _ p.mass.stack_injective j
        _ = _ := by
          fin_cases j <;> simp [LeafProgram.Mass.data, BinaryPrograms.Add.stackState, read, hs]
    · exact embedState_stack_frame p.mass.register p.mass.stack a
        (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))) i h

theorem mass_stack (p : Ports R S) (a : State R S) regs acc next (i : Fin 3) :
    (LeafProgram.Mass.state p.mass a regs acc next).stacks (p.mass.stack i) =
      (LeafProgram.Mass.data regs acc next).stacks i :=
  embedState_stack _ _ _ _ p.mass.stack_injective i

theorem mass_frame (p : Ports R S) (a : State R S) regs acc next (j : Fin S)
    (hj : ∀ i, p.mass.stack i ≠ j) :
    (LeafProgram.Mass.state p.mass a regs acc next).stacks j = a.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  exact hj i hi

end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafBranchProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Disjointness of the high-coordinate partition turns the native rank sum
into a full count over the original assignment space. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open scoped BigOperators

 theorem rankSum_eq_sum (value : ℕ → ℕ) (n : ℕ) :
    rankSum value 0 n = ∑ r : Fin n, value r.val := by
  rw [Fin.sum_univ_eq_sum_range, rankSum, ← List.range_eq_range']
  induction n with
  | zero => simp
  | succ n ih => simp [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem rankSum_original {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset V) (order : Fin H.card ≃ H) (P : (V → Bool) → Prop) [DecidablePred P]
    (value : ℕ → ℕ)
    (hvalue : ∀ r : Fin (2^H.card), value r.val =
      ∑ b : {v : V // v ∉ H} → Bool,
        if P (HighIncidence.glue H (HighIncidenceProgram.Rank.highEquiv order r) b) then 1 else 0) :
    rankSum value 0 (2^H.card) = ∑ x : V → Bool, if P x then 1 else 0 := by
  rw [rankSum_eq_sum, HighIncidenceProgram.Rank.sum_original_by_rank H order]
  apply Finset.sum_congr rfl
  intro r _
  exact hvalue r

end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-coordinate interpretation of the physical high tuple.
The order is descending original ID, and every rank including the unique
empty tuple participates in the count. No coordinate compaction is used. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount
open HighIncidenceProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem rankValue_at (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (r : Fin (2^H.card)) :
    rankValue H hashes marked clause r.val=NodeSemantics.ternaryFixedHighCount H
      (Rank.highEquiv (Order.highOrder H) r) hashes marked clause := by
  simp only [rankValue,dite_eq_left r.isLt]

theorem rankSum_fullCount (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) :
    LeafBranchProgram.rankSum (rankValue H hashes marked clause) 0 (2^H.card)=
      fullCount hashes marked clause := by
  apply LeafBranchProgram.rankSum_original H (Order.highOrder H)
    (NodeSemantics.ternaryAccepted hashes marked clause)
  intro r
  exact rankValue_at H hashes marked clause r

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete high-loop interfaces: the original ternary source count, exact
physical rank order, the fixed stream's durable frame, and its actual native
accumulator. The full loop still requires the actual stream semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount ProgramTapeReplay
open scoped BigOperators

/-- Each fixed-high query counts free assignments without pruning original
clause violations; its optional marked violation is part of the source test. -/
theorem residual_count_le {n : ℕ} (H : Finset (Fin n)) (high : H → Bool)
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) :
    NodeSemantics.ternaryFixedHighCount H high hashes marked clause ≤ 2 ^ n := by
  classical
  calc
    _ ≤ ∑ _x : ResidualEmbedding.Free H → Bool, 1 :=
      Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = 2 ^ (n-H.card) := by simp [ResidualEmbedding.Free]
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

/-- The rank function is the original source function in descending high-ID
order. Out-of-range proof indices contribute zero. -/
theorem rank_value_le {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) :
    rankValue H hashes marked clause rank ≤ 2 ^ n := by
  unfold rankValue
  split_ifs
  · exact residual_count_le H _ hashes marked clause
  · exact Nat.zero_le _

theorem full_count_le {n : ℕ} (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) :
    fullCount hashes marked clause ≤ 2 ^ n := by
  classical
  calc
    _ ≤ ∑ _x : Fin n → Bool, 1 := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = _ := by simp

/-- This is a mathematical prefix sum only. The machine retains a binary
accumulator and odometer, never this exponential range as a list. -/
theorem rank_prefix_le {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank ≤ 2 ^ H.card) :
    rankSum (rankValue H hashes marked clause) 0 rank ≤ 2 ^ n := by
  have hs : List.Sublist (List.range' 0 rank) (List.range' 0 (2 ^ H.card)) :=
    List.range'_sublist_right.mpr hr
  have hb := (hs.map (rankValue H hashes marked clause)).sum_le_sum
    (fun _ _ => Nat.zero_le _)
  change rankSum (rankValue H hashes marked clause) 0 rank ≤
    rankSum (rankValue H hashes marked clause) 0 (2 ^ H.card) at hb
  rw [rankSum_fullCount] at hb
  exact hb.trans (full_count_le hashes marked clause)

/-- Appending the current residual count advances exactly one rank. -/
theorem rank_prefix_succ (value : ℕ → ℕ) (rank : ℕ) :
    rankSum value 0 rank + value rank = rankSum value 0 (rank+1) := by
  unfold rankSum
  rw [←List.range'_append_1 (s:=0) (m:=rank) (n:=1)]
  simp

/-- The genuine binary adder consumes a canonical residual answer, retaining
at most ambient n+1 bits even after exponentially many preceding branches. -/
theorem add_rank_oai {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank < 2 ^ H.card)
    (a : Data) (hacc : BinaryArithmetic.toNat (a.stacks 788) =
      rankSum (rankValue H hashes marked clause) 0 rank)
    (hlen : (a.stacks 788).length ≤ n+1)
    (hnext : a.stacks 323 = countWord (rankValue H hashes marked clause rank))
    (hscratch : a.stacks 791 = []) :
    ∃ steps rf, steps ≤ 16*(n+2)+3 ∧
      let b := Mass.state highPorts.mass a rf
        (BinaryArithmetic.add (a.stacks 788) (a.stacks 323)) []
      Eval (Mass.invoke highPorts.mass) steps a b ∧
      b.stacks 323 = [] ∧ b.stacks 791 = [] ∧
      (b.stacks 788).length ≤ n+1 ∧
      BinaryArithmetic.toNat (b.stacks 788) =
        rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
      (∀ i, i ≠ 788 → i ≠ 323 → i ≠ 791 → b.stacks i = a.stacks i) := by
  have hv : BinaryArithmetic.toNat (a.stacks 788) + BinaryArithmetic.toNat (a.stacks 323) =
      rankSum (rankValue H hashes marked clause) 0 (rank+1) := by
    rw [hacc,hnext,countWord_toNat,rank_prefix_succ]
  have hn : (a.stacks 323).length ≤ n+1 := by
    rw [hnext]
    exact countWord_length_le (rank_value_le H hashes marked clause rank)
  have hp : BinaryArithmetic.toNat (a.stacks 788) + BinaryArithmetic.toNat (a.stacks 323) <
      2 ^ (n+1) := by
    rw [hv]
    exact (rank_prefix_le H hashes marked clause (rank+1) (by omega)).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by omega))
  obtain ⟨steps,ht,rf,he⟩ := Mass.invoke_eval highPorts.mass a
    (fun i => a.regs (highPorts.mass.register i)) (a.stacks 788) (a.stacks 323)
  have hself : Mass.state highPorts.mass a (fun i => a.regs (highPorts.mass.register i))
      (a.stacks 788) (a.stacks 323) = a := mass_self highPorts a hscratch
  rw [hself] at he
  have hout : (Mass.state highPorts.mass a rf
      (BinaryArithmetic.add (a.stacks 788) (a.stacks 323)) []).stacks 788 =
        BinaryArithmetic.add (a.stacks 788) (a.stacks 323) := mass_stack highPorts a rf _ [] 0
  refine ⟨steps,rf,?_,he,mass_stack highPorts a rf _ [] 1,
    mass_stack highPorts a rf _ [] 2,?_,?_,?_⟩
  · have hm : max (a.stacks 788).length (a.stacks 323).length ≤ n+1 := max_le hlen hn
    omega
  · rw [hout]
    exact HighIncidenceStream.length_add_of_lt (n+1) _ _ hlen hn hp
  · rw [hout,BinaryArithmetic.toNat_add,hv]
  · intro i hi hj hk
    apply mass_frame highPorts a rf _ [] i
    intro j
    fin_cases j <;> simp [highPorts,Ne.symm hi,Ne.symm hj,Ne.symm hk]

open HashGreedyProgram.NativeRound


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank_oai
