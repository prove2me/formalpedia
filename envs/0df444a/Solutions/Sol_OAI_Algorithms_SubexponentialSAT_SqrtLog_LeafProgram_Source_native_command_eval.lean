-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:54:48.130301+00:00
-- url     : https://prove2.me/submissions/37c90e95-df8e-4653-8438-562493bf1439

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Source_finished_stacks

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramLengthFixed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Proof-only refinement of the actual output rows to fixed-length arrays.
The byte stream is unchanged, so this adds no executable conversion. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

private theorem fixed_encodeList {B d D : ℕ}
    (rows : List (DensePolynomialProgram.Fixed.Array B d D)) :
    Encoding.encodeList DensePolynomialProgram.Fixed.encode rows=
      Encoding.encodeList DensePolynomialProgram.encode (rows.map Subtype.val) := by
  induction rows with
  | nil => rfl
  | cons w ws ih => simp [Encoding.encodeList,DensePolynomialProgram.Fixed.encode,ih]

theorem RowProperty.toFixed {B d : ℕ} (hB : 0 < B) (hd : 0 < d)
    (R : ℕ → List (DensePolynomialProgram.Coeff B d) → Prop)
    (D j : ℕ) (rows : List (List (DensePolynomialProgram.Coeff B d)))
    (h : RowProperty DensePolynomialProgram.encode R (D*(d*B)) j rows) :
    ∃ fixed : List (DensePolynomialProgram.Fixed.Array B d D),
      fixed.map Subtype.val=rows ∧ fixed.length=rows.length ∧
      Encoding.encodeList DensePolynomialProgram.Fixed.encode fixed=
        Encoding.encodeList DensePolynomialProgram.encode rows ∧
      RowProperty DensePolynomialProgram.Fixed.encode (fun k a=>R k a.val) (D*(d*B)) j fixed := by
  have hp : ∃ fixed : List (DensePolynomialProgram.Fixed.Array B d D),
      fixed.map Subtype.val=rows ∧
      RowProperty DensePolynomialProgram.Fixed.encode (fun k a=>R k a.val) (D*(d*B)) j fixed := by
    induction rows generalizing j with
    | nil => exact ⟨[],rfl,True.intro⟩
    | cons w ws ih =>
      obtain ⟨hr,hlen,htail⟩ := h
      have hw : w.length=D := by
        rw [DensePolynomialProgram.encode_length] at hlen
        exact (Nat.mul_right_cancel_iff (Nat.mul_pos hd hB)).mp hlen
      obtain ⟨tail,he,hprop⟩ := ih (j+1) htail
      refine ⟨⟨w,hw⟩::tail,?_,hr,?_,hprop⟩
      · simp [he]
      · exact DensePolynomialProgram.Fixed.encode_length ⟨w,hw⟩
  obtain ⟨fixed,he,hprop⟩ := hp
  refine ⟨fixed,he,?_,?_,hprop⟩
  · simpa using congrArg List.length he
  · rw [fixed_encodeList,he]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Protect the target-jet caches while the source-polynomial initializer
uses the same private local ports. Source length and target jet order are
independent runtime values. These are actual copy and clear programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem save_valid : ∀p∈savePairs,p.1≠p.2 ∧ p.1≠684 ∧ (684 : Fin 768)≠p.2 := by
  intro p hp
  simp only [savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl <;> decide
private theorem restore_valid : ∀p∈restorePairs,p.1≠p.2 ∧ p.1≠684 ∧ (684 : Fin 768)≠p.2 := by
  intro p hp
  simp only [restorePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl <;> decide

theorem before_eval (a : Data) (htmp : a.stacks 684=[]) :
    Eval before (beforeCost a) a (saved a) :=
  (copyMany_eval 684 savePairs a save_valid htmp).seq
    (clearMany_eval cachePorts (copyManyState savePairs a))

theorem after_eval (a : Data) (htmp : a.stacks 684=[]) :
    Eval after (afterCost a) a (finished a) := by
  have htmp' : (clearManyState cachePorts a).stacks 684=[] := by
    simpa [clearMany_stacks,cachePorts] using htmp
  have h := (clearMany_eval cachePorts a).seq
    ((copyMany_eval 684 restorePairs (clearManyState cachePorts a) restore_valid htmp').seq
      ((clearMany_eval backupPorts (copyManyState restorePairs (clearManyState cachePorts a))).seq
        (clearMany_eval lowClearPorts (restored a))))
  change Eval after
    (clearManyCost cachePorts a + (copyManyCost restorePairs (clearManyState cachePorts a) +
      (clearManyCost backupPorts (copyManyState restorePairs (clearManyState cachePorts a)) +
        clearManyCost lowClearPorts (restored a)))) a (finished a) at h
  rw [show afterCost a = clearManyCost cachePorts a +
    (copyManyCost restorePairs (clearManyState cachePorts a) +
      (clearManyCost backupPorts (copyManyState restorePairs (clearManyState cachePorts a)) +
        clearManyCost lowClearPorts (restored a))) by unfold afterCost; omega]
  exact h

end SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem pairs_valid : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ p.1 ≠ 684 ∧ (684 : Fin 768) ≠ p.2 := by
  intro p hp
  simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

theorem setDelta_eval (a : Data) : Eval setDelta 2 a (deltaState a) :=
  (Eval.base (StructuredProgram.Eval.atom (.set 0 true) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push 365 0)
      ((StructuredProgram.Atom.set (0 : Fin 16) true).eval a)))

theorem prepare_eval (a : Data) (htmp : a.stacks 684 = []) :
    Eval prepare (prepareCost a) a (prepared a) :=
  (copyMany_eval 684 pairs a pairs_valid htmp).seq (setDelta_eval _)

theorem delta_stacks (a : Data) :
    (deltaState a).stacks = Function.update a.stacks 365 (true :: a.stacks 365) := by
  rfl

theorem cleanup_eval (a : Data) :
    Eval cleanup (clearManyCost extraPorts a) a (cleaned a) := clearMany_eval extraPorts a

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source callback used by the actual incidence-table loop. The fixed
command stages source controls, protects all four target caches, invokes the
concrete source-row instruction table, restores the target caches, and clears
source-only controls. The local source correctness theorem is joined below
through its actual execution, never through a supplied polynomial oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
theorem workerPort_injective : Function.Injective workerPort := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 340+i.val=340+j.val at hv
  omega

private theorem saved_tmp (a : Data) :
    (SourceStaging.saved a).stacks 684 = a.stacks 684 := by
  rw [SourceStaging.saved,clearMany_stacks,ite_eq_right (by decide)]
  apply copyMany_frame
  intro p hp
  simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h <;> subst p <;> decide

private theorem prepared_tmp (a : Data) : (prepared a).stacks 684 = a.stacks 684 := by
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks]
  simp only [Function.update_of_ne (by decide : (684 : Fin 768) ≠ 365)]
  calc
    (copyManyState SourceControls.pairs (SourceStaging.saved a)).stacks 684 =
        (SourceStaging.saved a).stacks 684 := by
      apply copyMany_frame
      intro p hp
      exact (SourceControls.pairs_valid p hp).2.2
    _ = a.stacks 684 := saved_tmp a

private theorem coreOutput_tmp (a : Data) (b : State 16 340) :
    (coreOutput a b).stacks 684 = a.stacks 684 := by
  have h := embedState_stack_frame id workerPort (prepared a) b (684 : Fin 768) (by
    rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    change 340+i.val=684 at hv
    omega)
  exact h.trans (prepared_tmp a)

/-- This composition lemma charges the concrete source command's execution
plus every staging/cleanup call. The source execution premise is precisely
what its native correctness theorem supplies. -/
theorem command_eval (a : Data) (b : State 16 340) (n : ℕ)
    (htmp : a.stacks 684 = [])
    (hsource : Eval LayoutSourceRowsProgram.sourceRows n
      (projectState id workerPort (prepared a)) b) :
    Eval command (cost a b n) a (finished a b) := by
  have h0 := SourceStaging.before_eval a htmp
  have h1 := SourceControls.prepare_eval (SourceStaging.saved a)
    ((saved_tmp a).trans htmp)
  have h2 := eval_call_from_state LayoutSourceRowsProgram.sourceRowsProgram
    id workerPort (prepared a) Function.injective_id workerPort_injective
    (compiled_halt_trace hsource 337 205)
  have h3 := SourceStaging.after_eval (coreOutput a b)
    ((coreOutput_tmp a b).trans htmp)
  have h4 := SourceControls.cleanup_eval (SourceStaging.finished (coreOutput a b))
  exact h0.seq (h1.seq (h2.seq (h3.seq h4)))

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact store restoration for the executed source callback. The source
kernel may change its four initialized caches and source output; the wrapper
restores all four caches and removes every staged source control. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem control_classified (p : Fin 768 × Fin 768) (hp : p ∈ SourceControls.pairs) :
    p.2 ∈ SourceStaging.lowClearPorts ∨ p.2 ∈ SourceControls.extraPorts := by
  simp only [SourceControls.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

/-- Native source-row correctness gives the local frame below; relocation
transports it without imposing any condition on unrelated global masters. -/
theorem coreFrame_of_local (a : Data) (b : State 16 340)
    (h : ∀ j : Fin 340, j ∉ ([205,192,193,242,243] : List (Fin 340)) →
      b.stacks j = (prepared a).stacks (workerPort j)) : CoreFrame a b := by
  intro i hi
  by_cases hin : ∃ j, workerPort j = i
  · obtain ⟨j,rfl⟩ := hin
    rw [show (coreOutput a b).stacks (workerPort j) = b.stacks j from
      embedState_stack id workerPort (prepared a) b workerPort_injective j]
    apply h
    intro hj
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj
    rcases hj with hj|hj|hj|hj|hj <;> subst j <;> exact hi (by decide)
  · exact embedState_stack_frame id workerPort (prepared a) b i hin

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed source generation in the incidence worker. The result arrays are
witnesses of the actual run; no equality of separately generated byte arrays
is inferred from equality of their polynomial meanings. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

private theorem nativeResult_frame {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (a : Source.Data) (rows : List (List (DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)))
    (regs : Fin 16 → Bool) : CoreFrame a (nativeResult p (nativeStore a) rows regs) := by
  apply coreFrame_of_local
  intro j hj
  have h205 : j ≠ 205 := by intro h; subst j; exact hj (by simp)
  have h192 : j ≠ 192 := by intro h; subst j; exact hj (by simp)
  have h193 : j ≠ 193 := by intro h; subst j; exact hj (by simp)
  have h242 : j ≠ 242 := by intro h; subst j; exact hj (by simp)
  have h243 : j ≠ 243 := by intro h; subst j; exact hj (by simp)
  simp only [nativeResult,initializeFinish,Function.update_of_ne h205,
    Function.update_of_ne h192,Function.update_of_ne h193,
    Function.update_of_ne h242,Function.update_of_ne h243]
  rfl

/-- The fixed source wrapper returns the exact arrays generated on this
invocation, with their full untruncated source meaning and exact outer frame.
The source-time bound excludes all target-J truncation parameters. -/
theorem native_command_eval_oai {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : Source.Data) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (h : NativeInput p ps P a v N f S width frame) :
    ∃ (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
      (raw : List (List (DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)))
      (n : ℕ) (rf rr : Fin 16 → Bool),
      rows.map Subtype.val = raw ∧ rows.length = N ∧
      RowProperty DensePolynomialProgram.Fixed.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out.val =
          sourceRowFamily ps N f v (totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧
      n ≤ nativeRowsBudget p (nativeStore a) v N f S ps ∧
      Eval Source.command (Source.cost a (nativeResult p (nativeStore a) raw rf) n) a
        (⟨rr,Function.update a.stacks 545
          (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : Source.Data) := by
  obtain ⟨raw,n,rf,hraw,hlen,hn,he⟩ := sourceRows_run p ps P (nativeStore a) v N f S width frame
    h.init h.literal h.ambient h.factor h.plans h.lookup h.rowsClean h.workClean h.owner
    h.arithmetic h.empty h.source h.sourceClean h.metadata h.size h.metadataSize
    h.incidenceBound h.nodesBound h.radiusBound h.ringWidthBound h.rowWidthBound (prepared a).regs
  have hB : 0 < baseWidth 3 p.t := by
    unfold baseWidth
    exact Nat.mul_pos p.ht (by omega)
  obtain ⟨rows,hmap,hlen',hbytes,hrows⟩ := RowProperty.toFixed hB p.hd _ (p.R+1) 0 raw hraw
  let b := nativeResult p (nativeStore a) raw rf
  have hc := Source.command_eval a b n h.tmp he
  have hout := finished_stacks a b (nativeResult_frame p a raw rf) h.low h.extra h.backups
  have hb : b.stacks 205 = Encoding.encodeList DensePolynomialProgram.Fixed.encode rows := by
    simp only [b,nativeResult,Function.update_same]
    exact hbytes.symm
  rw [hb] at hout
  have hout' : finished a b =
      (⟨(finished a b).regs,Function.update a.stacks 545
        (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : Source.Data) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact hout
  rw [hout'] at hc
  exact ⟨rows,raw,n,rf,(finished a b).regs,hmap,hlen'.trans hlen,hrows,hn,hc⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval_oai
