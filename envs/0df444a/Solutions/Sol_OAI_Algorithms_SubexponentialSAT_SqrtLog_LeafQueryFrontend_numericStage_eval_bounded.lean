-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:01:03.856075+00:00
-- url     : https://prove2.me/submissions/9361958e-e21a-4d55-bc2b-48feec3e45ac

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S168
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_convertStatistics_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticExpressionSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem bits_value (n : ℕ) : BinaryArithmetic.toNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp []
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      cases b <;> simp [BinaryArithmetic.toNat, ih, Nat.bit, Nat.add_comm]

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
theorem registers_injective (n : ℕ) (hn : n ≤ 40) : Function.Injective (registers n hn) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun z : Fin 40 => z.val) h

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies and fixed constants used between frontend stages. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem copy_eval (a : Data) (src dst : Fin 768) (h : CopyReady a src dst) :
    Eval (copy src dst) (7*(a.stacks src).length+5) a (copied a src dst) :=
  SubexpScanPrimitives.copy_eval a src dst 679 0 1 h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem copies_eval (xs : List (Fin 768 × Fin 768)) (a : Data) (h : CopiesReady xs a) :
    Eval (copies xs) (copiesCost xs a) a (copiesState xs a) := by
  induction xs generalizing a with
  | nil => exact .base (.skip a)
  | cons x xs ih =>
      rcases x with ⟨s,d⟩
      exact (copy_eval a s d h.1).seq (ih _ h.2)

theorem copies_frame (xs : List (Fin 768 × Fin 768)) (a : Data) (i : Fin 768)
    (hi : ∀ x ∈ xs, x.2 ≠ i) : (copiesState xs a).stacks i = a.stacks i := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨s,d⟩
      rw [copiesState,ih _ (fun x hx => hi x (List.mem_cons_of_mem _ hx))]
      simp [copied_stack,Ne.symm (hi (s,d) List.mem_cons_self)]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordinary finite-window facts for the concrete frontend port maps. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem copies_ready_of_clean (xs : List (Fin 768 × Fin 768)) (a : Data)
    (h : ∀ x ∈ xs, x.1≠x.2 ∧ x.1≠679 ∧ x.2≠679) (ht : a.stacks 679=[]) :
    CopiesReady xs a := by
  induction xs generalizing a with
  | nil => trivial
  | cons x xs ih =>
      rcases x with ⟨s,d⟩
      have hx := h (s,d) List.mem_cons_self
      exact ⟨⟨hx.1,hx.2.1,Ne.symm hx.2.2,ht⟩,
        ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))
          (by simpa [copied_stack,Ne.symm hx.2.2] using ht)⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem loadBits_eval (a : Data) (dst : Fin 768) (bits : List Bool) :
    ∃ rf, Eval (loadBits dst bits) (2*bits.length+1) a
      ⟨rf,Function.update a.stacks dst (bits++a.stacks dst)⟩ := by
  obtain ⟨rf,he⟩ := ArithmeticExpressionSupport.pushWord_eval dst bits (projectState r8 id a)
  have h := eval_liftCommand_from_state (ArithmeticExpressionSupport.pushWord dst bits) dst dst
    r8 id a (registers_injective ..) Function.injective_id he
  let b := embedState r8 id a ⟨rf,Function.update (projectState r8 id a).stacks dst
    (bits++(projectState r8 id a).stacks dst)⟩
  have hb : b = ⟨b.regs,Function.update a.stacks dst (bits++a.stacks dst)⟩ := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i
    exact embedState_stack r8 id a _ Function.injective_id i
  exact ⟨b.regs,by change Eval (loadBits dst bits) _ a b at h; rw [hb] at h; exact h⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendGrowth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem eval_length_le {c : Code} {n : ℕ} {a b : Data} (he : Eval c n a b)
    (i : Fin 768) : (b.stacks i).length ≤ (a.stacks i).length+n := by
  exact Subexp.SequentialProgram.trace_stack_length_le (compiled_trace he i i) i

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendNumericRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram


theorem numericStage_eval (a : Data) (ambient clauses : List Bool)
    (k free occ arity factors mass : ℕ)
    (ha : a.stacks 709=ambient) (hm : a.stacks 707=clauses)
    (hz : emptyRange a 340 417) (ht : a.stacks 679=[]) (ht' : a.stacks 647=[])
    (hfree : a.stacks 626=List.replicate free true)
    (hocc : a.stacks 627=List.replicate occ true)
    (harity : a.stacks 642=List.replicate arity true)
    (hfactors : a.stacks 613=List.replicate factors true)
    (hmass : a.stacks 628=List.replicate mass true) :
    ∃ n b l w, Eval (numericStage k) n a b ∧
      projectState r9 bank b=Execute.state (b.regs ∘ r9) w ∧
      Circuit.Shape (Layout.initialModel (numericInput ambient clauses k free occ arity factors mass) l) w ∧
      n ≤ 7*ambient.length+5+7*clauses.length+5+2*k.bits.length+1+
        conversionCost free+conversionCost occ+conversionCost arity+conversionCost factors+conversionCost mass ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 417 ≤ i.val) →
        i≠626 → i≠627 → i≠642 → i≠613 → i≠628 → i≠647 → b.stacks i=a.stacks i) := by
  let cs : List (Fin 768 × Fin 768) := [(709,340),(707,342)]
  let c := copiesState cs a
  have hc := copies_eval cs a (copies_ready_of_clean cs a (by simp [cs]) ht)
  have hcf (i : Fin 768) (h0 : i≠340) (h2 : i≠342) : c.stacks i=a.stacks i := by
    apply copies_frame
    simp [cs,Ne.symm h0,Ne.symm h2]
  have hc340 : c.stacks 340=ambient := by
    simp [c,cs,copiesState,copied_stack,ha,hz 340 (by decide) (by decide)]
  have hc342 : c.stacks 342=clauses := by
    simp [c,cs,copiesState,copied_stack,hm,hz 342 (by decide) (by decide)]
  have hc346 : c.stacks 346=[] := (hcf 346 (by decide) (by decide)).trans (hz 346 (by decide) (by decide))
  obtain ⟨rl,hl⟩ := loadBits_eval c 346 k.bits
  rw [hc346,List.append_nil] at hl
  let d : Data := ⟨rl,Function.update c.stacks 346 k.bits⟩
  have hdf (i : Fin 768) (h0 : i≠340) (h2 : i≠342) (h6 : i≠346) : d.stacks i=a.stacks i := by
    simpa [d,h6] using hcf i h0 h2
  have hd647 : d.stacks 647=[] := (hdf 647 (by decide) (by decide) (by decide)).trans ht'
  have hd626 : d.stacks 626=List.replicate free true := (hdf 626 (by decide) (by decide) (by decide)).trans hfree
  have hd627 : d.stacks 627=List.replicate occ true := (hdf 627 (by decide) (by decide) (by decide)).trans hocc
  have hd642 : d.stacks 642=List.replicate arity true := (hdf 642 (by decide) (by decide) (by decide)).trans harity
  have hd613 : d.stacks 613=List.replicate factors true := (hdf 613 (by decide) (by decide) (by decide)).trans hfactors
  have hd628 : d.stacks 628=List.replicate mass true := (hdf 628 (by decide) (by decide) (by decide)).trans hmass
  have hdz (i : Fin 768) (hi : 340 ≤ i.val ∧ i.val < 417) (h0 : i≠340) (h2 : i≠342) (h6 : i≠346) : d.stacks i=[] :=
    (hdf i h0 h2 h6).trans (hz i hi.1 hi.2)
  obtain ⟨nb,b,hb,hnb,hv1,hl1,hv3,hl3,hv4,hl4,hv5,hl5,hv7,hl7,hb647,hbf⟩ :=
    convertStatistics_eval d free occ arity factors mass hd647
      hd626 (hdz 341 (by decide) (by decide) (by decide) (by decide))
      hd627 (hdz 343 (by decide) (by decide) (by decide) (by decide))
      hd642 (hdz 344 (by decide) (by decide) (by decide) (by decide))
      hd613 (hdz 345 (by decide) (by decide) (by decide) (by decide))
      hd628 (hdz 347 (by decide) (by decide) (by decide) (by decide))
  let w : Bank.Words := fun i => b.stacks (bank (Bank.port i))
  let l : Fin 8 → ℕ := fun i => (w (i.castAdd 56)).length
  have hb0 : b.stacks 340=ambient := by
    rw [hbf 340 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [d] using hc340
  have hb2 : b.stacks 342=clauses := by
    rw [hbf 342 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [d] using hc342
  have hb6 : b.stacks 346=k.bits := by
    rw [hbf 346 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [d]
  have hbz (i : Fin 768) (hi : 348 ≤ i.val ∧ i.val < 417) : b.stacks i=[] := by
    have hi0 : i≠340 := by intro h; subst i; omega
    have hi2 : i≠342 := by intro h; subst i; omega
    have hi6 : i≠346 := by intro h; subst i; omega
    rw [hbf i (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega)]
    exact hdz i (by omega) hi0 hi2 hi6
  have hp : projectState r9 bank b=Execute.state (b.regs ∘ r9) w := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i.val < 64
      · simp [Bank.state,hi,w,Bank.port]
      · have hzi := hbz (bank i) (by dsimp [bank,block]; omega)
        simpa [projectState,Execute.state,Bank.state,hi] using hzi
  have hshape : Circuit.Shape (Layout.initialModel (numericInput ambient clauses k free occ arity factors mass) l) w := by
    constructor
    · intro i
      by_cases hi : i.val < 8
      · obtain ⟨j,rfl⟩ : ∃ j : Fin 8, i=j.castAdd 56 := ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
        fin_cases j <;>
          simp_all [w,bank,block,Bank.port,Layout.initialModel,Layout.initialValues,numericInput,
            ArithmeticExpressionSupport.bits_value]
      · have hzi := hbz (bank (Bank.port i)) (by dsimp [bank,block,Bank.port]; omega)
        simp [w,hzi,Layout.initialModel,Layout.initialValues,numericInput
]
        split <;> omega
    · intro i
      by_cases hi : i.val < 8
      · simp [Layout.initialModel,hi,l]
      · have hzi := hbz (bank (Bank.port i)) (by dsimp [bank,block,Bank.port]; omega)
        simp [Layout.initialModel,hi,w,hzi]
  refine ⟨copiesCost cs a+(2*k.bits.length+1+nb),b,l,w,hc.seq (hl.seq hb),hp,hshape,?_,?_⟩
  · have hcost : copiesCost cs a=7*ambient.length+5+7*clauses.length+5 := by
      simp [copiesCost,cs,copied_stack,ha,hm]
      omega
    rw [hcost]
    omega
  · intro i hi h626 h627 h642 h613 h628 h647
    rw [hbf i h626 (by intro h; subst i; omega) h627 (by intro h; subst i; omega)
      h642 (by intro h; subst i; omega) h613 (by intro h; subst i; omega)
      h628 (by intro h; subst i; omega) h647]
    exact hdf i (by intro h; subst i; omega) (by intro h; subst i; omega) (by intro h; subst i; omega)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendNumericBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The concrete input bank admits an input-only uniform word-length model. -/
theorem numericStage_eval_bounded_oai (a : Data) (ambient clauses : List Bool)
    (k free occ arity factors mass : ℕ)
    (ha : a.stacks 709=ambient) (hm : a.stacks 707=clauses)
    (hz : emptyRange a 340 417) (ht : a.stacks 679=[]) (ht' : a.stacks 647=[])
    (hfree : a.stacks 626=List.replicate free true)
    (hocc : a.stacks 627=List.replicate occ true)
    (harity : a.stacks 642=List.replicate arity true)
    (hfactors : a.stacks 613=List.replicate factors true)
    (hmass : a.stacks 628=List.replicate mass true) :
    ∃ n b l w, Eval (numericStage k) n a b ∧
      projectState r9 bank b=Execute.state (b.regs ∘ r9) w ∧
      Circuit.Shape (Layout.initialModel (numericInput ambient clauses k free occ arity factors mass) l) w ∧
      n ≤ numericCost ambient clauses k free occ arity factors mass ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 417 ≤ i.val) →
        i≠626 → i≠627 → i≠642 → i≠613 → i≠628 → i≠647 → b.stacks i=a.stacks i) ∧
      l=(fun _ => numericCost ambient clauses k free occ arity factors mass) := by
  obtain ⟨n,b,l,w,he,hp,hs,hn,hf⟩ := numericStage_eval a ambient clauses k free occ arity factors mass
    ha hm hz ht ht' hfree hocc harity hfactors hmass
  refine ⟨n,b,fun _ => numericCost ambient clauses k free occ arity factors mass,w,he,hp,⟨hs.1,?_⟩,hn,hf,rfl⟩
  intro i
  by_cases hi : i.val < 8
  · have hv : b.stacks (bank (Bank.port i))=w i := by
      have h := congrFun (congrArg StructuredProgram.State.stacks hp) (Bank.port i)
      simpa [projectState,Execute.state,Bank.state,Bank.port] using h
    have hg := eval_length_le he (bank (Bank.port i))
    have hz' := hz (bank (Bank.port i)) (by dsimp [bank,block,Bank.port]; omega)
      (by dsimp [bank,block,Bank.port]; omega)
    rw [hz',List.length_nil,zero_add,hv] at hg
    simpa [numericCost, Layout.initialModel, hi, Nat.add_assoc] using hg.trans hn
  · simpa [Layout.initialModel,hi] using hs.2 i

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded_oai
