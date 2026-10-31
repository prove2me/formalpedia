-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:06:24.196562+00:00
-- url     : https://prove2.me/submissions/50a38897-d84f-4eb9-a054-15dbc53c9750

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S183
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_convertStatistics_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_highCommand_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_measureCommand_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_parameterCall_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_rawCommand_eval

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
theorem block_injective (base n : ℕ) (hn : base+n ≤ 768) : Function.Injective (block base n hn) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [block] at this; omega

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

theorem block_not_mem {base n : ℕ} (h : base+n ≤ 768) (i : Fin 768)
    (hi : i.val < base ∨ base+n ≤ i.val) : i ∉ Set.range (block base n h) := by
  rintro ⟨j,hj⟩
  have hjv := congrArg Fin.val hj
  dsimp [block] at hjv
  have := j.isLt
  omega

theorem embedded_stack_frame {r base n : ℕ} (hr : r ≤ 40) (hs : base+n ≤ 768)
    (a : Data) (b : State r n) (i : Fin 768) (hi : i.val < base ∨ base+n ≤ i.val) :
    (embedState (registers r hr) (block base n hs) a b).stacks i = a.stacks i :=
  embedState_stack_frame _ _ _ _ _ (block_not_mem hs i hi)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Joined per-query core. Mathematical values below describe physical input
words and computed outputs; they are not extra machine inputs. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem coreCommand_eval_oai (q : Query) (k : ℕ) (a : Data) (hv : q.Valid) (hready : q.Ready a) :
    ∃ n b tau l w, Eval (coreCommand k) n a b ∧
      n ≤ coreBudget q k a tau l ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧
      projectState r9 bank b=LeafParametersProgram.Execute.state (b.regs ∘ r9) w ∧
      LeafParametersProgram.Circuit.Shape (LeafParametersProgram.Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ LeafParametersProgram.Guard (q.input k)) ∧
      (LeafParametersProgram.Guard (q.input k) → LeafParametersProgram.Layout.EncodesParameters
        (LeafParametersProgram.produce (q.input k)) w) ∧
      emptyRange b 648 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) → i≠338 → i≠718 → i≠719 → b.stacks i=a.stacks i) := by
  rcases hv with ⟨hb,hn,hc,hbound,hindex,hm,hids⟩
  rcases hready with ⟨h700,h701,h705,h706,h707,h708,h709,hz,h338,h718,h719⟩
  have ht := hz 679 (by decide) (by decide)
  obtain ⟨nr,r,er,hr718,br,fr⟩ := rawCommand_eval a
    (fun i hi hj => hz i (by omega) (by omega)) ht h718 q.width.length hb q.clauses q.codes hc
    q.rows hbound q.mark q.index q.width q.modulus hindex rfl hm h700 h701 h705 h706 h707 h708
  have r709 : r.stacks 709=q.ambient := (fr 709 (Or.inr (by decide)) (by decide)).trans h709
  have r679 : r.stacks 679=[] := (fr 679 (Or.inr (by decide)) (by decide)).trans ht
  obtain ⟨nh,h,tau,eh,htau,hh338,hh719,bh,fh⟩ := highCommand_eval r q.scopeRows q.ambient r709 hn hr718
    (fun i hi hj => (fr i (Or.inl (by omega)) (by intro he; subst i; omega)).trans (hz i (by omega) (by omega)))
    (fun i hi hj => (fr i (Or.inr (by omega)) (by intro he; subst i; omega)).trans (hz i (by omega) (by omega)))
    r679 ((fr 338 (Or.inl (by decide)) (by decide)).trans h338)
    ((fr 719 (Or.inr (by decide)) (by decide)).trans h719)
    ((fr 645 (Or.inr (by decide)) (by decide)).trans (hz 645 (by decide) (by decide)))
    ((fr 646 (Or.inr (by decide)) (by decide)).trans (hz 646 (by decide) (by decide)))
  have h718 : h.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows :=
    (fh 718 (Or.inr (by decide)) (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide)).trans hr718
  have h679 : h.stacks 679=[] :=
    (fh 679 (Or.inr (by decide)) (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide)).trans r679
  have hlen : q.forward.length=BinaryArithmetic.toNat q.ambient := by simp [Query.forward,highMask]
  obtain ⟨nm,m,em,hmv,bm,fm⟩ := measureCommand_eval h q.scopeRows q.forward h718 hh719 h679
    (fun i hi hj => (fh i (Or.inr (by omega)) (Or.inr (by omega))
      (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega)).trans
        ((fr i (Or.inr (by omega)) (by intro he; subst i; omega)).trans (hz i (by omega) (by omega))))
    (by simpa only [hlen] using hids)
  have mhframe (i : Fin 768) (hi : i.val < 340 ∨ 680 ≤ i.val) (h338 : i≠338) (h719 : i≠719) : m.stacks i=r.stacks i := by
    exact (fm i (by omega)).trans (fh i (by omega) (by omega) h338 h719
      (by intro he; subst i; omega) (by intro he; subst i; omega))
  have m709 : m.stacks 709=q.ambient := (mhframe 709 (Or.inr (by decide)) (by decide) (by decide)).trans r709
  have m707 : m.stacks 707=q.modulus := (mhframe 707 (Or.inr (by decide)) (by decide) (by decide)).trans
    ((fr 707 (Or.inr (by decide)) (by decide)).trans h707)
  have m679 : m.stacks 679=[] := (fm 679 (Or.inr (by decide))).trans h679
  have m647 : m.stacks 647=[] := (fm 647 (Or.inr (by decide))).trans
    ((fh 647 (Or.inr (by decide)) (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide)).trans
      ((fr 647 (Or.inr (by decide)) (by decide)).trans (hz 647 (by decide) (by decide))))
  rcases hmv with ⟨mf,mo,mi,mq,ma⟩
  obtain ⟨nn,u,l,w,en,hup,hushape,bn,fn⟩ := numericStage_eval m q.ambient q.modulus k
    (totals q.scopeRows q.forward).free (totals q.scopeRows q.forward).occurrence
    (completedArity q.scopeRows q.forward) (q.scopeRows.length+(totals q.scopeRows q.forward).uncovered)
    (totals q.scopeRows q.forward).incidences m709 m707
    (fun i hi hj => (fm i (Or.inl (by omega))).trans
      ((fh i (Or.inl (by omega)) (Or.inl (by omega)) (by intro he; subst i; omega)
        (by intro he; subst i; omega) (by intro he; subst i; omega) (by intro he; subst i; omega)).trans
        ((fr i (Or.inl (by omega)) (by intro he; subst i; omega)).trans (hz i hi (by omega)))))
    m679 m647 mf mo ma mq mi
  obtain ⟨np,bp,rp,wp,ep,hguard,hshape,hparameters⟩ := parameterCall_eval u (q.input k) l w hushape hup
  let b := embedState r9 bank u (LeafParametersProgram.Execute.state rp wp)
  have fb (i : Fin 768) (hi : i.val < 340 ∨ 417 ≤ i.val) : b.stacks i=u.stacks i :=
    embedded_stack_frame (by decide) (by decide) u _ i hi
  have fnu (i : Fin 768) (hi : i.val < 340 ∨ 680 ≤ i.val) : u.stacks i=m.stacks i :=
    fn i (by omega) (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega)
  have b718 : b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows :=
    (fb 718 (Or.inr (by decide))).trans ((fnu 718 (Or.inr (by decide))).trans
      ((fm 718 (Or.inr (by decide))).trans h718))
  have b338 : b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) :=
    (fb 338 (Or.inl (by decide))).trans ((fnu 338 (Or.inl (by decide))).trans
      ((fm 338 (Or.inl (by decide))).trans hh338))
  have b719 : b.stacks 719=q.forward := (fb 719 (Or.inr (by decide))).trans
    ((fnu 719 (Or.inr (by decide))).trans ((fm 719 (Or.inr (by decide))).trans hh719))
  have pb : projectState r9 bank b=LeafParametersProgram.Execute.state rp wp :=
    projectState_embed _ _ _ _ (registers_injective ..) (block_injective ..)
  have rb : b.regs ∘ r9=rp := congrArg StructuredProgram.State.regs pb
  refine ⟨nr+(nh+(nm+(nn+np))),b,tau,l,wp,er.seq (eh.seq (em.seq (en.seq ep))),?_,htau,
    b718,b338,b719,?_,hshape,?_,hparameters,?_,?_⟩
  · change h.stacks 719=q.forward at hh719
    have hcopy : copiesCost statsCopies h=7*(LeafStatisticsProgram.scopeBits q.scopeRows).length+5+7*q.forward.length+5 := by
      simp [copiesCost,statsCopies,copied_stack,h718,hh719]
      omega
    rw [measureBudget,hcopy] at bm
    unfold coreBudget
    dsimp only
    dsimp only [Query.scopeRows,Query.forward] at br bh bm bn ⊢
    simp only [List.length_reverse] at br bh bm bn ⊢
    omega
  · rw [rb]; exact pb
  · have hr8 : b.regs 8=rp 8 := congrFun rb 8
    simpa only [hr8] using hguard
  · intro i hi hj
    have hb_u := fb i (Or.inr (by omega))
    have hu_m := fn i (Or.inr (by omega))
      (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega)
    have hm_h := fm i (Or.inr (by omega))
    have hh_r := fh i (Or.inr (by omega)) (Or.inr (by omega))
      (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega)
    have hr_a := fr i (Or.inr (by omega)) (by intro he; subst i; omega)
    exact hb_u.trans (hu_m.trans (hm_h.trans (hh_r.trans (hr_a.trans (hz i (by omega) hj)))))
  · intro i hi h338 h718 h719
    exact (fb i (by omega)).trans ((fnu i hi).trans ((mhframe i hi h338 h719).trans
      (fr i (by omega) h718)))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_oai
