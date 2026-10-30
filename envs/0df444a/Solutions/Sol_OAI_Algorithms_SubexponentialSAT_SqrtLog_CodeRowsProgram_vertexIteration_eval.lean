-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexIteration_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:38:51.196636+00:00
-- url     : https://prove2.me/submissions/b0fd6cb5-9946-477c-ac94-7fafc0681a8a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_vertexStep_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Width preservation below a binary overflow boundary

The input word may contain high zero bits. This lemma applies to actual ripple
increment results and does not assume a canonical binary representation.
-/

namespace SubexponentialSAT.CounterPrograms

/-- Increment stays within an n-bit word when its new value is below 2^n. -/
theorem increment_length_le_of_lt (bs : List Bool) (n : ℕ)
    (hlen : bs.length ≤ n) (hvalue : value bs + 1 < 2 ^ n) :
    (ripple true bs).length ≤ n := by
  induction n generalizing bs with
  | zero =>
      have he : bs = [] := List.length_eq_zero_iff.mp (by omega)
      subst bs
      simp at hvalue
  | succ n ih =>
      cases bs with
      | nil => simp [ripple]
      | cons bit bs =>
          cases bit with
          | false => simpa [ripple] using hlen
          | true =>
              have hl : bs.length ≤ n := by simpa using hlen
              have hv : value bs + 1 < 2 ^ n := by
                simp only [value, Bool.toNat_true, pow_succ] at hvalue
                omega
              simpa [ripple] using Nat.succ_le_succ (ih bs hl hv)

end SubexponentialSAT.CounterPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCounter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem ripple_length_ge (xs : List Bool) : xs.length ≤ (CounterPrograms.ripple true xs).length := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp [CounterPrograms.ripple] at * ; omega

theorem increment_vertex_width (xs : List Bool) (r : ℕ) (hl : xs.length=r)
    (hv : CounterPrograms.value xs+1 < 2^r) : (CounterPrograms.ripple true xs).length=r := by
  exact Nat.le_antisymm (CounterPrograms.increment_length_le_of_lt xs r hl.le hv)
    (hl ▸ ripple_length_ge xs)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistenceEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable binary indexing for Cayley vertices. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

theorem cubeEquiv_encode (r : ℕ) (x : Cube r) :
    ((cubeEquiv r).symm x).val = ∑ j, (x j).val * 2 ^ j.val := by
  rfl

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStream
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

theorem collectedRows_append {m : ℕ} (b : ℕ)
    (rs ss : List (List (Fin m × SparseCode.F3))) (tail : List Bool) :
    collectedRows b (rs++ss) tail=collectedRows b ss (collectedRows b rs tail) := by
  simp [collectedRows,rowRecords,List.reverse_append,List.flatMap_append,List.append_assoc]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SubexponentialSAT.BinaryArithmetic

theorem toNat_ofFn {r : ℕ} (f : Fin r → Bool) :
    BinaryArithmetic.toNat (List.ofFn f)=∑ i : Fin r,bitVal (f i)*2^i.val := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ,toNat_cons,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem vertexBits_value {r : ℕ} (v : Cayley.Cube r) :
    BinaryArithmetic.toNat (vertexBits v)=((WalshExistence.cubeEquiv r).symm v).val := by
  rw [vertexBits,toNat_ofFn,WalshExistence.cubeEquiv_encode]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hb (x : ZMod 2) : bitVal (decide (x=1))=x.val := by fin_cases x <;> decide
  exact hb (v i)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertexLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

private theorem word_eq (xs ys : List Bool) (hlen : xs.length=ys.length)
    (hv : BinaryArithmetic.toNat xs=BinaryArithmetic.toNat ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hxy : x=y := by
        cases x <;> cases y <;> simp_all [toNat_cons,bitVal] <;> omega
      subst y
      congr 1
      apply ih ys (by simpa using hlen)
      cases x <;> simp_all [toNat_cons,bitVal]

theorem vertexPrefix_succ {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (i : ℕ) (hi : i < 2^r) :
    vertexPrefix m shifts Q (i+1)=vertexPrefix m shifts Q i++
      vertexRows m shifts Q (WalshExistence.cubeEquiv r ⟨i,hi⟩) := by
  unfold vertexPrefix
  rw [List.take_succ_eq_append_getElem (by simpa using hi),List.flatMap_append]
  simp

theorem vertexIteration_eval_oai {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (b : ℕ)
    (ready : LocalReady base D m b (base.regs 12) (0 : Cayley.Cube r))
    (hq : base.stacks 10=CodeSearchProgram.matrixFrames Q)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D) (ht : (base.stacks 7).length=t)
    (h0 : base.stacks 0=[]) (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) (h16 : base.stacks 16=[])
    (i : ℕ) (hi : i < 2^r) (d : Data) (inv : VertexInvariant (m:=m) base shifts Q b i d) :
    ∃ n e, n ≤ vertexCost base D t b ∧ Eval vertexStep n d e ∧
      e.stacks vertexLoop.counter=d.stacks vertexLoop.counter ∧
      VertexInvariant (m:=m) base shifts Q b (i+1) e := by
  let v := WalshExistence.cubeEquiv r ⟨i,hi⟩
  have hv : d.stacks 2=vertexBits v := by
    apply word_eq
    · simpa using inv.width hi
    · simpa [v,vertexBits_value] using inv.value
  have preserved (j : Fin 64) (h2 : j≠2) (h8 : j≠8) (h12 : j≠12) :
      d.stacks j=base.stacks j := inv.other j h2 h8 h12
  have rd : LocalReady d D m b (d.regs 12) v := by
    constructor
    · rfl
    · exact hv
    · rw [preserved 3 (by decide) (by decide) (by decide)]; exact ready.degree
    · rw [preserved 4 (by decide) (by decide) (by decide)]; exact ready.modulus
    · rw [preserved 5 (by decide) (by decide) (by decide)]; exact ready.width
    · exact ready.capacity
    · intro j hj hk
      have h2 : j≠2 := by intro hne; have hv := congrArg Fin.val hne; change j.val=2 at hv; omega
      have h8 : j≠8 := by intro hne; have hv := congrArg Fin.val hne; change j.val=8 at hv; omega
      have h12 : j≠12 := by intro hne; have hv := congrArg Fin.val hne; change j.val=12 at hv; omega
      rw [preserved j h2 h8 h12]; exact ready.work j hj hk
  obtain ⟨n,rf,he,hn,hr⟩ := vertexStep_eval d shifts Q v b rd
    (by rw [preserved 10 (by decide) (by decide) (by decide)]; exact hq)
    (by rw [preserved 9 (by decide) (by decide) (by decide)]; exact hs)
    (by rw [preserved 6 (by decide) (by decide) (by decide)]; exact hD)
    (by rw [preserved 7 (by decide) (by decide) (by decide)]; exact ht)
    (by rw [preserved 0 (by decide) (by decide) (by decide)]; exact h0)
    (by rw [preserved 1 (by decide) (by decide) (by decide)]; exact h1)
    (by rw [preserved 13 (by decide) (by decide) (by decide)]; exact h13)
    (by rw [preserved 14 (by decide) (by decide) (by decide)]; exact h14)
    (by rw [preserved 15 (by decide) (by decide) (by decide)]; exact h15)
    (by rw [preserved 16 (by decide) (by decide) (by decide)]; exact h16)
  let e : Data := ⟨rf,Function.update (Function.update d.stacks 12
    (collectedRows b (vertexRows m shifts Q v) (d.stacks 12))) 2
      (CounterPrograms.ripple true (d.stacks 2))⟩
  have costeq : vertexCost d D t b=vertexCost base D t b := by
    unfold vertexCost sideCost rowCost portWidth
    rw [preserved 10 (by decide) (by decide) (by decide),
      preserved 7 (by decide) (by decide) (by decide),
      preserved 6 (by decide) (by decide) (by decide),
      preserved 9 (by decide) (by decide) (by decide),
      preserved 3 (by decide) (by decide) (by decide),
      preserved 4 (by decide) (by decide) (by decide),
      preserved 5 (by decide) (by decide) (by decide),
      preserved 14 (by decide) (by decide) (by decide),hv,ready.vertex]
    simp
  refine ⟨n,e,by simpa [costeq] using hn,he,?_,?_⟩
  · simp [e,vertexLoop]
  · constructor
    · omega
    · simpa [e,CounterPrograms.value_eq_toNat,inv.value] using
        CounterPrograms.value_increment (d.stacks 2)
    · intro hj
      simpa [e] using increment_vertex_width (d.stacks 2) r (inv.width hi)
        (by simpa [CounterPrograms.value_eq_toNat,inv.value] using hj)
    · have hlen := CounterPrograms.ripple_length_le true (d.stacks 2)
      have old := inv.width hi
      simp only [e,Function.update_same]
      omega
    · simp [e,vertexPrefix_succ m shifts Q i hi,v,inv.output,collectedRows_append]
    · intro j h2 h8 h12
      simpa [e,h2,h12] using inv.other j h2 h8 h12

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexIteration_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexIteration_eval_oai
