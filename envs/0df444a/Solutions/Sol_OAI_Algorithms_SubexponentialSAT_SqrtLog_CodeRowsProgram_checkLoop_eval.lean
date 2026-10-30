-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.checkLoop_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:32:41.608464+00:00
-- url     : https://prove2.me/submissions/30f61da1-ca21-497a-8f3a-fd8703402687

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_rowStep_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramFor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A bounded variant of the existing unary controller rule. Its invariant
may retain registers that the actual pop instruction does not touch. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.UnaryForPrograms

variable {R S : ℕ}

theorem bounded_visits (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop) (N C : ℕ)
    (stable : ∀ i d, I i d → I i (popped p d))
    (step : ∀ i < N, ∀ d, I i d → ∃ n e, n ≤ C ∧ Eval body n d e ∧
      e.stacks p.counter=d.stacks p.counter ∧ I (i+1) e)
    (word : List Bool) :
    ∀ i d, d.stacks p.counter=word → I i d → i+word.length ≤ N →
      ∃ costs n e, Visits p body costs n d e ∧ I (i+word.length) e ∧
        n ≤ word.length*(C+2)+2 := by
  induction word with
  | nil =>
    intro i d hd hi hN
    exact ⟨[],2,popped p d,Visits.done d hd,by simpa using stable i d hi,by simp⟩
  | cons bit word ih =>
    intro i d hd hi hN
    have hiN : i < N := by simp only [List.length_cons] at hN; omega
    obtain ⟨nb,e,hnb,hbody,hcounter,hie⟩ := step i hiN (popped p d) (stable i d hi)
    have he : e.stacks p.counter=word := by rw [hcounter,popped_counter,hd]; rfl
    have htail : i+1+word.length ≤ N := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hN
    obtain ⟨costs,nt,f,ht,hif,hnt⟩ := ih (i+1) e he hie htail
    refine ⟨nb::costs,nb+nt+2,f,Visits.step (by simp [hd]) hbody hcounter ht,?_,?_⟩
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hif
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem bounded_for_eval (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop) (N C : ℕ)
    (stable : ∀ i d, I i d → I i (popped p d))
    (step : ∀ i < N, ∀ d, I i d → ∃ n e, n ≤ C ∧ Eval body n d e ∧
      e.stacks p.counter=d.stacks p.counter ∧ I (i+1) e)
    (d : State R S) (hd : (d.stacks p.counter).length=N) (hi : I 0 d) :
    ∃ n e, Eval (forCmd p body) n d e ∧ I N e ∧ e.stacks p.counter=[] ∧ n ≤ N*(C+2)+2 := by
  obtain ⟨costs,n,e,hvis,hei,hn⟩ := bounded_visits p body I N C stable step
    (d.stacks p.counter) 0 d rfl hi (by omega)
  refine ⟨n,e,hvis.eval,?_,hvis.bounds.2.1,?_⟩
  · simpa [hd] using hei
  · simpa [hd] using hn

end SubexponentialSAT.SqrtLog.CodeRowsProgram

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

theorem collectedRows_snoc {m : ℕ} (b : ℕ) (rs : List (List (Fin m × SparseCode.F3)))
    (row : List (Fin m × SparseCode.F3)) (tail : List Bool) :
    collectedRows b (rs++[row]) tail=
      true::(Encoding.frame (rowPayload b m row)++collectedRows b rs tail) := by
  simp [collectedRows,rowRecords,List.reverse_append,List.append_assoc]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCheckLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem CheckInvariant.popped {r D t m : ℕ} {base : Data} {shifts : Fin D → Cayley.Cube r}
    {Q : Fin t → Fin D → SparseCode.F3} {side : Bool} {v : Cayley.Cube r}
    {b i : ℕ} {d : Data} (h : CheckInvariant (m:=m) base shifts Q side v b i d) :
    CheckInvariant (m:=m) base shifts Q side v b i (UnaryForPrograms.popped rowLoop d) := by
  constructor
  · intro j hj
    have h10 : j≠10 := by intro hne; have hv := congrArg Fin.val hne; change j.val=10 at hv; omega
    have h11 : j≠11 := by intro hne; have hv := congrArg Fin.val hne; change j.val=11 at hv; omega
    simpa [UnaryForPrograms.popped,rowLoop,readRegs,h10,h11] using h.registers j hj
  · simpa [UnaryForPrograms.popped,rowLoop] using h.source
  · simpa [UnaryForPrograms.popped,rowLoop] using h.output
  · intro j h0 h12 h16
    simpa [UnaryForPrograms.popped,rowLoop,h16] using h.other j h0 h12 h16

theorem checkStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (b : ℕ) (ready : LocalReady base D m b side v)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts)) (hD : (base.stacks 6).length=D)
    (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[])
    (i : ℕ) (hi : i < t) (d : Data) (inv : CheckInvariant (m:=m) base shifts Q side v b i d) :
    ∃ n e, n ≤ rowCost base D b ∧ Eval rowStep n d e ∧
      e.stacks rowLoop.counter=d.stacks rowLoop.counter ∧
      CheckInvariant (m:=m) base shifts Q side v b (i+1) e := by
  let a : Fin t := ⟨i,hi⟩
  have preserved (j : Fin 64) (h0 : j≠0) (h12 : j≠12) (h16 : j≠16) :
      d.stacks j=base.stacks j := inv.other j h0 h12 h16
  have rd : LocalReady d D m b side v := by
    constructor
    · exact (inv.registers 12 (by decide)).trans ready.mode
    · rw [preserved 2 (by decide) (by decide) (by decide)]; exact ready.vertex
    · rw [preserved 3 (by decide) (by decide) (by decide)]; exact ready.degree
    · rw [preserved 4 (by decide) (by decide) (by decide)]; exact ready.modulus
    · rw [preserved 5 (by decide) (by decide) (by decide)]; exact ready.width
    · exact ready.capacity
    · intro j hj hk
      have h0 : j≠0 := by intro hne; have hv := congrArg Fin.val hne; change j.val=0 at hv; omega
      have h12 : j≠12 := by intro hne; have hv := congrArg Fin.val hne; change j.val=12 at hv; omega
      have h16 : j≠16 := by intro hne; have hv := congrArg Fin.val hne; change j.val=16 at hv; omega
      rw [preserved j h0 h12 h16]; exact ready.work j hj hk
  have source : d.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++matrixSuffix Q (i+1) := by
    rw [inv.source]
    unfold matrixSuffix
    rw [List.drop_eq_getElem_cons (by simpa using hi)]
    simp [a]
  obtain ⟨n,rf,he,hn,hr⟩ := rowStep_eval d shifts Q side v a b (matrixSuffix Q (i+1)) rd source
    (by rw [preserved 9 (by decide) (by decide) (by decide)]; exact hs)
    (by rw [preserved 6 (by decide) (by decide) (by decide)]; exact hD)
    (by rw [preserved 1 (by decide) (by decide) (by decide)]; exact h1)
    (by rw [preserved 13 (by decide) (by decide) (by decide)]; exact h13)
    (by rw [preserved 14 (by decide) (by decide) (by decide)]; exact h14)
    (by rw [preserved 15 (by decide) (by decide) (by decide)]; exact h15)
  let e : Data := ⟨rf,rowStacks d (matrixSuffix Q (i+1)) (rowPayload b m (slots m shifts Q side v a))⟩
  have costeq : rowCost d D b=rowCost base D b := by
    unfold rowCost portWidth
    rw [preserved 6 (by decide) (by decide) (by decide),
      preserved 9 (by decide) (by decide) (by decide),
      preserved 2 (by decide) (by decide) (by decide),
      preserved 3 (by decide) (by decide) (by decide),
      preserved 4 (by decide) (by decide) (by decide),
      preserved 5 (by decide) (by decide) (by decide),
      preserved 14 (by decide) (by decide) (by decide)]
  refine ⟨n,e,by simpa [costeq] using hn,he,?_,?_⟩
  · simp [e,rowStacks,rowLoop]
  · constructor
    · intro j hj; exact (hr j hj).trans (inv.registers j hj)
    · simp [e,rowStacks]
    · have ht : (checkRows m shifts Q side v).take (i+1)=
          (checkRows m shifts Q side v).take i++[slots m shifts Q side v a] := by
        rw [List.take_succ_eq_append_getElem (by simpa [checkRows] using hi)]
        simp [checkRows,a]
      simp [e,rowStacks,ht,collectedRows_snoc,inv.output]
    · intro j h0 h12 h16
      simpa [e,rowStacks,h0,h12] using inv.other j h0 h12 h16

theorem checkLoop_eval_oai {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (b : ℕ) (ready : LocalReady base D m b side v)
    (hq : base.stacks 0=matrixSuffix Q 0)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts)) (hD : (base.stacks 6).length=D)
    (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[])
    (ht : (base.stacks 16).length=t) :
    ∃ n e, Eval (UnaryForPrograms.forCmd rowLoop rowStep) n base e ∧
      CheckInvariant (m:=m) base shifts Q side v b t e ∧ e.stacks 16=[] ∧
      n ≤ t*(rowCost base D b+2)+2 := by
  apply bounded_for_eval rowLoop rowStep
    (CheckInvariant (m:=m) base shifts Q side v b) t (rowCost base D b)
  · intro i d inv; exact inv.popped
  · exact checkStep_eval base shifts Q side v b ready hs hD h1 h13 h14 h15
  · exact ht
  · constructor
    · intros; rfl
    · exact hq
    · simp
    · intros; rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.checkLoop_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.checkLoop_eval_oai
