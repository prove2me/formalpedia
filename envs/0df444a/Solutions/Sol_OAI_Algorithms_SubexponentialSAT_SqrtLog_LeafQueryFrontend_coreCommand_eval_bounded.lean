-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:06:25.248441+00:00
-- url     : https://prove2.me/submissions/93efcd3e-59fc-40e4-8b67-6ef5b552b39a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S183
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_highCommand_eval_bounded
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_measureCommand_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_numericStage_eval_bounded
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_parameterCall_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_rawCommand_eval

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

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCoreBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem coreCommand_eval_bounded_oai (q : Query) (k : ℕ) (a : Data) (hv : q.Valid) (hready : q.Ready a) :
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
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) → i≠338 → i≠718 → i≠719 → b.stacks i=a.stacks i) ∧
      tau.length ≤ Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1 ∧
      l=q.inputLengths k := by
  rcases hv with ⟨hb,hn,hc,hbound,hindex,hm,hids⟩
  rcases hready with ⟨h700,h701,h705,h706,h707,h708,h709,hz,h338,h718,h719⟩
  have ht := hz 679 (by decide) (by decide)
  obtain ⟨nr,r,er,hr718,br,fr⟩ := rawCommand_eval a
    (fun i hi hj => hz i (by omega) (by omega)) ht h718 q.width.length hb q.clauses q.codes hc
    q.rows hbound q.mark q.index q.width q.modulus hindex rfl hm h700 h701 h705 h706 h707 h708
  have r709 : r.stacks 709=q.ambient := (fr 709 (Or.inr (by decide)) (by decide)).trans h709
  have r679 : r.stacks 679=[] := (fr 679 (Or.inr (by decide)) (by decide)).trans ht
  obtain ⟨nh,h,tau,eh,htau,hh338,hh719,bh,fh,htlen⟩ := highCommand_eval_bounded r q.scopeRows q.ambient r709 hn hr718
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
  obtain ⟨nn,u,l,w,en,hup,hushape,bn,fn,hll⟩ := numericStage_eval_bounded m q.ambient q.modulus k
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
    b718,b338,b719,?_,hshape,?_,hparameters,?_,?_,htlen,hll⟩
  · change h.stacks 719=q.forward at hh719
    have hcopy : copiesCost statsCopies h=7*(LeafStatisticsProgram.scopeBits q.scopeRows).length+5+7*q.forward.length+5 := by
      simp [copiesCost,statsCopies,copied_stack,h718,hh719]
      omega
    rw [measureBudget,hcopy] at bm
    dsimp only [numericCost] at bn
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

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded_oai
