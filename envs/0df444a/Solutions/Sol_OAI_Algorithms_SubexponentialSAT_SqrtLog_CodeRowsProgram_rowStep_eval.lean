-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:37:27.236582+00:00
-- url     : https://prove2.me/submissions/0df6a0b7-bd57-417c-8021-c65a9a601de3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_localStep_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_writeRow_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_eval (src dst : Fin 64) (d : Data)
    (hsd : src≠dst) (hst : src≠24) (htd : (24 : Fin 64)≠dst)
    (htmp : d.stacks 24=[]) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copied src dst d) :=
  Subexp.TupleProgram.copy_eval src dst 24 0 1 hsd hst htd (by decide) d htmp

theorem clear_eval (src : Fin 64) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared src d) :=
  Subexp.TupleProgram.clear_eval src 0 1 d

theorem copied_register (src dst : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (copied src dst d).regs i=d.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  simp [copied,readRegs,h0,h1]

theorem cleared_register (src : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (cleared src d).regs i=d.regs i := by
  exact copied_register src src d i hi

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlots
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse local-slot specifications. A row lists at most D original clause
indices, including any zero coefficients; shortening only removes slots whose
actual shifted edge index lies outside the original m coordinates. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

theorem slots_length (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    (slots m shifts Q side v a).length ≤ D := by
  exact (List.length_filterMap_le _ _).trans_eq List.length_finRange

theorem rowPayload_length (b m : ℕ) (ss : List (Fin m × SparseCode.F3)) :
    (rowPayload b m ss).length=ss.length*b := by
  induction ss with
  | nil => simp [rowPayload]
  | cons s ss ih =>
    change ((SubexpLiftRing.fixedBits b (s.1.val+m*s.2.val)) ++ rowPayload b m ss).length = _
    simp only [List.length_append,SubexpLiftRing.fixedBits_length,ih,List.length_cons]
    simp [Nat.add_mul,Nat.add_comm]

theorem sparse_rowPayload_length (b : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    (rowPayload b m (slots m shifts Q side v a)).length ≤ D*b := by
  rw [rowPayload_length]
  exact Nat.mul_le_mul_right b (slots_length shifts Q side v a)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramInvariant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem LocalInvariant.popped {r D t m : ℕ} {base : Data} {shifts : Fin D → Cayley.Cube r}
    {Q : Fin t → Fin D → SparseCode.F3} {side : Bool} {v : Cayley.Cube r}
    {a : Fin t} {b : ℕ} {qt st : List Bool} {i : ℕ} {d : Data}
    (h : LocalInvariant (m:=m) base shifts Q side v a b qt st i d) :
    LocalInvariant (m:=m) base shifts Q side v a b qt st i (UnaryForPrograms.popped portLoop d) := by
  constructor
  · exact h.position
  · intro j hj
    have h10 : j≠10 := by intro hne; have hv := congrArg Fin.val hne; change j.val=10 at hv; omega
    have h11 : j≠11 := by intro hne; have hv := congrArg Fin.val hne; change j.val=11 at hv; omega
    simpa [UnaryForPrograms.popped,portLoop,readRegs,h10,h11] using h.registers j hj
  · simpa [UnaryForPrograms.popped,portLoop] using h.source
  · simpa [UnaryForPrograms.popped,portLoop] using h.shiftSource
  · simpa [UnaryForPrograms.popped,portLoop] using h.accum
  · simpa [UnaryForPrograms.popped,portLoop] using h.index
  · simpa [UnaryForPrograms.popped,portLoop] using h.indexLength
  · intro j h0 h1 h13 h14 h15
    simpa [UnaryForPrograms.popped,portLoop,h15] using h.other j h0 h1 h13 h14 h15

theorem localInvariant_initial {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt st : List Bool)
    (hq : base.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++qt)
    (hs : base.stacks 1=shiftRows (List.ofFn shifts)++st) (hp : base.stacks 14=[]) :
    LocalInvariant (m:=m) base shifts Q side v a b qt st 0 base := by
  constructor
  · omega
  · intro j hj; rfl
  · simpa using hq
  · simpa using hs
  · simp [rowPayload]
  · simp [hp]
  · simp [hp]
  · intros; rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramLocal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem localLoop_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt st : List Bool) (ready : LocalReady base D m b side v)
    (hq : base.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++qt)
    (hs : base.stacks 1=shiftRows (List.ofFn shifts)++st)
    (hp : base.stacks 14=[]) (hcount : (base.stacks 15).length=D) :
    ∃ n e, Eval (UnaryForPrograms.forCmd portLoop portStep) n base e ∧
      LocalInvariant (m:=m) base shifts Q side v a b qt st D e ∧ e.stacks 15=[] ∧
      n ≤ D*(2000*(portWidth base+D+1)^2+2)+2 := by
  apply bounded_for_eval portLoop portStep
    (LocalInvariant (m:=m) base shifts Q side v a b qt st) D (2000*(portWidth base+D+1)^2)
  · intro i d inv; exact inv.popped
  · exact localStep_eval base shifts Q side v a b qt st ready
  · exact hcount
  · exact localInvariant_initial base shifts Q side v a b qt st hq hs hp

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.StackRoutines

theorem rowStep_eval_oai {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt : List Bool) (ready : LocalReady base D m b side v)
    (hq : base.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++qt)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D)
    (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) :
    ∃ n rf, Eval rowStep n base
      ⟨rf,rowStacks base qt (rowPayload b m (slots m shifts Q side v a))⟩ ∧
      n ≤ rowCost base D b ∧ (∀ j : Fin 16, 12 ≤ j.val → rf j=base.regs j) := by
  let d1 := copied 6 15 base
  let d2 := copied 9 1 d1
  have c1 := copy_eval 6 15 base (by decide) (by decide) (by decide)
    (ready.work 24 (by decide) (by decide))
  have c2 := copy_eval 9 1 d1 (by decide) (by decide) (by decide)
    (by simpa [d1,copied,copyStacks] using ready.work 24 (by decide) (by decide))
  have rd : LocalReady d2 D m b side v := by
    constructor
    · simpa [d2,d1,copied,readRegs] using ready.mode
    · simpa [d2,d1,copied,copyStacks] using ready.vertex
    · simpa [d2,d1,copied,copyStacks] using ready.degree
    · simpa [d2,d1,copied,copyStacks] using ready.modulus
    · simpa [d2,d1,copied,copyStacks] using ready.width
    · exact ready.capacity
    · intro j hj hk
      have hj1 : j≠1 := by intro hne; have hv := congrArg Fin.val hne; change j.val=1 at hv; omega
      have hj15 : j≠15 := by intro hne; have hv := congrArg Fin.val hne; change j.val=15 at hv; omega
      simpa [d2,d1,copied,copyStacks,hj1,hj15] using ready.work j hj hk
  obtain ⟨nl,e,hl,inv,he15,hnl⟩ := localLoop_eval d2 shifts Q side v a b qt [] rd
    (by simpa [d2,d1,copied,copyStacks] using hq)
    (by simp [d2,d1,copied,copyStacks,h1,hs])
    (by simpa [d2,d1,copied,copyStacks] using h14)
    (by simpa [d2,d1,copied,copyStacks,h15] using hD)
  let d3 := cleared 14 e
  have cl := clear_eval 14 e
  obtain ⟨rf,hw,hr⟩ := writeRow_eval d3
  have hqdrop : (List.ofFn (Q a)).drop D = [] := by
    apply List.drop_eq_nil_of_le
    simp
  have hsdrop : (List.ofFn shifts).drop D = [] := by
    apply List.drop_eq_nil_of_le
    simp
  have e0 : e.stacks 0=qt := by
    simpa [hqdrop, CodeSearchProgram.scalarFrames, Subexp.MatrixProgramSupport.words]
      using inv.source
  have e1 : e.stacks 1=[] := by simpa [hsdrop,shiftRows] using inv.shiftSource
  have e13 : e.stacks 13=(rowPayload b m (slots m shifts Q side v a)).reverse := by
    simpa [d2,d1,copied,copyStacks,h13] using inv.accum
  have eother (j : Fin 64) (hj0 : j≠0) (hj1 : j≠1) (hj13 : j≠13)
      (hj14 : j≠14) (hj15 : j≠15) : e.stacks j=base.stacks j := by
    simpa [d2,d1,copied,copyStacks,hj1,hj15] using inv.other j hj0 hj1 hj13 hj14 hj15
  have e12 : e.stacks 12=base.stacks 12 := eother 12 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hout : Function.update (Function.update d3.stacks 13 []) 12
      (true::(Encoding.frame (d3.stacks 13).reverse++d3.stacks 12))=
      rowStacks base qt (rowPayload b m (slots m shifts Q side v a)) := by
    funext j
    by_cases hj0 : j=0
    · subst j; simp [d3,cleared,rowStacks,e0]
    by_cases hj1 : j=1
    · subst j; simp [d3,cleared,rowStacks,e1,h1]
    by_cases hj12 : j=12
    · subst j; simp [d3,cleared,rowStacks,e13,e12]
    by_cases hj13 : j=13
    · subst j; simp [d3,cleared,rowStacks,h13]
    by_cases hj14 : j=14
    · subst j; simp [d3,cleared,rowStacks,h14]
    by_cases hj15 : j=15
    · subst j; simp [d3,cleared,rowStacks,he15,h15]
    simp [d3,cleared,rowStacks,hj0,hj12,hj13,hj14,
      eother j hj0 hj1 hj13 hj14 hj15]
  have width : portWidth d2=portWidth base := by simp [portWidth,d2,d1,copied,copyStacks]
  have payloadBound : (rowPayload b m (slots m shifts Q side v a)).length ≤ D*b :=
    sparse_rowPayload_length b shifts Q side v a
  refine ⟨(7*(base.stacks 6).length+5) + ((7*(d1.stacks 9).length+5) +
    (nl + ((2*(e.stacks 14).length+3) + (4*(d3.stacks 13).length+8)))),rf,?_,?_,?_⟩
  · simpa only [rowStep,hout] using c1.seq (c2.seq (hl.seq (cl.seq hw)))
  · have ei := inv.indexLength
    dsimp [d3,cleared] at hw ⊢
    simp only [Function.update_noteq (by decide : (13 : Fin 64)≠14),e13,
      List.length_reverse] at ⊢
    simp only [d1,copied,copyStacks,Function.update_noteq (by decide : (9 : Fin 64)≠15)]
    rw [width] at hnl
    unfold rowCost
    omega
  · intro j hj
    have hr' : rf j=e.regs j := by
      rw [hr j (by omega)]
      exact cleared_register 14 e j (by omega)
    rw [hr',inv.registers j hj,copied_register 9 1 d1 j (by omega),
      copied_register 6 15 base j (by omega)]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval_oai
