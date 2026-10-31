-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.initialize_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:31:41.137859+00:00
-- url     : https://prove2.me/submissions/b1047746-ca2d-4d00-96bd-8bf68801efa9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafNodeCacheProgram_local_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- Different finite execution derivations of the same structured command
must have the same final data. The existing source port supplies a concrete
compiled machine, and determinism is inherited from its actual transition. -/
theorem Eval.final_unique {r s : ℕ} (port : Fin s) {c : Cmd r s}
    {n m : ℕ} {a b d : State r s} (h : Eval c n a b) (g : Eval c m a d) : b = d := by
  have hb := compiled_halt_trace h port port
  have hd := compiled_halt_trace g port port
  have heq := Computation.RunsIn.terminal_unique
    (show RunsIn (compiled c port port) (n + 1)
      (a.withPC (some (compiled c port port).entry)) (b.withPC none) from
      ⟨n + 1, le_rfl, hb⟩)
    (show RunsIn (compiled c port port) (m + 1)
      (a.withPC (some (compiled c port port).entry)) (d.withPC none) from
      ⟨m + 1, le_rfl, hd⟩)
    (by simp [step, StructuredProgram.State.withPC])
    (by simp [step, StructuredProgram.State.withPC])
  exact congrArg StructuredProgram.State.ofCfg heq

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct a cached sparse constant from a shape word and a forward flat
coefficient. Zero support bits, key delimiters, reversal, record framing and
cleanup all execute on the native bit machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem key_eq_origin (n : ℕ) : key n = Squarefree.encodeIndex (Squarefree.Index.origin : Squarefree.Index (Fin n)) := by
  unfold key
  rw [Nat.add_comm n 2,List.replicate_add]
  simp [Squarefree.encodeIndex,Squarefree.Index.origin,Encoding.encodeNat,Squarefree.encodeMask,
    List.ofFn_const]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeCacheProgramFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem copies_append (ps qs : List (Fin 768 × Fin 768)) (a : LocalData) :
    copyManyState (ps++qs) a = copyManyState qs (copyManyState ps a) := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨src,dst⟩
      exact ih _

private theorem direct_frame (a : LocalData) (i : Fin 768)
    (hi : i ∉ cachePorts) : (copyManyState directCopies a).stacks i = a.stacks i := by
  apply copyMany_frame
  intro p hp he
  have hmem : p.2∈cachePorts := (show ∀ p∈directCopies, p.2∈cachePorts by simp [directCopies,cachePorts]) p hp
  exact hi (he.symm ▸ hmem)

theorem cache_frame (a : LocalData) (i : Fin 768) (hi : i ∉ cachePorts) :
    cacheTapes a i = a.stacks i := by
  have h69 : i≠69 := fun he => hi (by simp [cachePorts,he])
  have h167 : i≠167 := fun he => hi (by simp [cachePorts,he])
  simpa only [cacheTapes,Function.update_of_ne h69,Function.update_of_ne h167] using direct_frame a i hi

theorem cache_direct (a : LocalData) (h : Ready a.stacks)
    (p : Fin 768 × Fin 768) (hp : p∈directCopies) : cacheTapes a p.2 = a.stacks p.1 := by
  have hp69 : p.2≠69 := (show ∀ p∈directCopies,p.2≠69 by simp [directCopies]) p hp
  have hp167 : p.2≠167 := (show ∀ p∈directCopies,p.2≠167 by simp [directCopies]) p hp
  simp only [cacheTapes,Function.update_of_ne hp69,Function.update_of_ne hp167]
  apply copyMany_value directCopies a (by decide) _ (by simp [directCopies]) p hp
  intro q hq
  exact h q.2 ((show ∀ q∈directCopies,q.2∈cachePorts++pocket by simp [directCopies,cachePorts,pocket]) q hq)

theorem cache_one (a : LocalData) : cacheTapes a 69=rawOne a.stacks ∧
    cacheTapes a 167=rawOne a.stacks := by simp [cacheTapes]

/-- The asserted update store includes every cache byte and all external tapes. -/
theorem final_stacks (a : LocalData) (h : Ready a.stacks) (rr : Fin 8 → Bool) :
    (finalState (prepared a) rr (rawOne a.stacks)).stacks = cacheTapes a := by
  funext i
  have h69 := h 69 (by decide)
  have h167 := h 167 (by decide)
  have hf69 : (copyManyState directCopies a).stacks 69=[] := (copyMany_frame directCopies a 69 (by simp [directCopies])).trans h69
  have hf167 : (copyManyState directCopies a).stacks 167=[] := (copyMany_frame directCopies a 167 (by simp [directCopies])).trans h167
  by_cases hi69 : i=69
  · subst i
    simp [finalState,prepared,copies,copies_append,copyManyState,copyState,clearState,
      StackRoutines.copyStacks,constantResult,constantTapes,cacheTapes,hf69]
  by_cases hi167 : i=167
  · subst i
    simp [finalState,prepared,copies,copies_append,copyManyState,copyState,clearState,
      StackRoutines.copyStacks,constantResult,constantTapes,cacheTapes,hf167]
  by_cases hr : 340 ≤ i.val ∧ i.val ≤ 345
  · have hi : i=340 ∨ i=341 ∨ i=342 ∨ i=343 ∨ i=344 ∨ i=345 := by
      have : i.val=340 ∨ i.val=341 ∨ i.val=342 ∨ i.val=343 ∨ i.val=344 ∨ i.val=345 := by omega
      simpa [Fin.ext_iff] using this
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 340 (by decide),h 340 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 341 (by decide),h 341 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 342 (by decide),h 342 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 343 (by decide),h 343 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 344 (by decide),h 344 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 345 (by decide),h 345 (by decide)]
  · have h340 : i≠340 := by intro he; subst i; simp at hr
    have h343 : i≠343 := by intro he; subst i; simp at hr
    have h345 : i≠345 := by intro he; subst i; simp at hr
    have hr' : ¬(340 ≤ i.val ∧ i.val < 345) := by omega
    simp [finalState,prepared,copies,copies_append,copyManyState,copyState,clearState,
      StackRoutines.copyStacks,constantResult,constantTapes,cacheTapes,hi69,hi167,h340,h343,h345,hr']

theorem local_eval_exact (a : LocalData) (h : Ready a.stacks) :
    ∃ b, Eval localCommand (localBudget a) a b ∧ b.stacks=cacheTapes a := by
  obtain ⟨rr,he⟩ := local_eval a h
  exact ⟨_,he,final_stacks a h rr⟩

theorem rawOne_length (a : LocalData) :
    (rawOne a.stacks).length = 2*(a.stacks 128).length+2*(a.stacks 207).length+6 := by
  simp [rawOne,HashCircuitProgram.Constant.key,Encoding.length_frame]
  omega

/-- Linear in a bound on actual source words, including the generated raw one. -/
theorem localBudget_le (a : LocalData) (B : ℕ) (ha : WordBound B a) :
    localBudget a  ≤  1000*(B+1) := by
  have hc := copyManyCost_le copies a B (by simp [copies,directCopies]) (fun p _ => ha p.1)
  have hn := ha 128
  have ho := ha 207
  rw [show copies.length=14 from rfl] at hc
  unfold localBudget
  rw [rawOne_length]
  omega

end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical reconstruction of the exact node caches, including the sparse
ring identity and ambient shape, before accepted assignment evaluation. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

theorem cacheStart_ready (a : State 16 768) :
    LeafNodeCacheProgram.Ready (cacheStart a).stacks := by
  intro i hi
  change i ∈ cachePorts at hi
  rw [cacheStart, clearMany_stacks, ite_eq_left hi]

theorem setupLocal_eval (a : State 16 768) :
    ∃ b, Eval setupLocal (setupLocalCost a) a b ∧
      b.stacks = LeafNodeCacheProgram.cacheTapes (cacheStart a) := by
  obtain ⟨b, he, hb⟩ := LeafNodeCacheProgram.local_eval_exact (cacheStart a) (cacheStart_ready a)
  exact ⟨b, (clearMany_eval cachePorts a).seq he, hb⟩

theorem setup_eval (a : Data) :
    ∃ b, Eval setup (setupCost a) a b ∧
      (∀ i, b.stacks (lowStack i) =
        LeafNodeCacheProgram.cacheTapes (cacheStart (projectState localRegister lowStack a)) i) ∧
      (∀ i : Fin 896, 768 ≤ i.val → b.stacks i = a.stacks i) := by
  obtain ⟨b, he, hb⟩ := setupLocal_eval (projectState localRegister lowStack a)
  refine ⟨embedState localRegister lowStack a b,
    eval_liftCommand_from_state setupLocal 128 69 localRegister lowStack a
      (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) he, ?_, ?_⟩
  · intro i
    rw [embedState_stack localRegister lowStack a b (Fin.castAdd_injective _ _) i, hb]
  · intro i hi
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

theorem setupLocalCost_le (a : State 16 768) (B : ℕ) (ha : WordBound B a) :
    setupLocalCost a ≤ 1100 * (B + 1) := by
  have hclear := clearManyCost_le cachePorts a B ha
  have hcache := LeafNodeCacheProgram.localBudget_le (cacheStart a) B
    (clearMany_wordBound cachePorts a B ha)
  change clearManyCost cachePorts a ≤ 21 * (2 * B + 3) at hclear
  unfold setupLocalCost
  omega

theorem setupCost_le (a : Data) (B : ℕ) (ha : WordBound B a) :
    setupCost a ≤ 1100 * (B + 1) + 1 := by
  exact Nat.add_le_add_right (setupLocalCost_le _ B (fun i => ha (lowStack i))) 1

theorem setup_local_frame (a : State 16 768) (i : Fin 768) (hi : i ∉ cachePorts) :
    LeafNodeCacheProgram.cacheTapes (cacheStart a) i = a.stacks i := by
  have hcache : i ∉ LeafNodeCacheProgram.cachePorts := by
    intro hm
    exact hi (List.mem_append_left _ hm)
  rw [LeafNodeCacheProgram.cache_frame _ i hcache, cacheStart, clearMany_stacks,
    ite_eq_right hi]

theorem setup_direct_word (a : State 16 768) (pair : Fin 768 × Fin 768)
    (hp : pair ∈ LeafNodeCacheProgram.directCopies) :
    LeafNodeCacheProgram.cacheTapes (cacheStart a) pair.2 = a.stacks pair.1 := by
  rw [LeafNodeCacheProgram.cache_direct _ (cacheStart_ready a) pair hp,
    cacheStart, clearMany_stacks]
  have hsep : pair.1 ∉ cachePorts := by
    have hall : ∀ q ∈ LeafNodeCacheProgram.directCopies, q.1 ∉ cachePorts := by
      simp [LeafNodeCacheProgram.directCopies, cachePorts,
        LeafNodeCacheProgram.cachePorts, LeafNodeCacheProgram.pocket]
    exact hall pair hp
  rw [ite_eq_right hsep]

/-- All 56 arithmetic ports are restored to the original Product.idle ABI.
The other copied cache words lie outside that bank. -/
theorem setup_low (a : State 16 768)
    (hempty : ∀ i : Fin 56, a.stacks (i.castAdd 712) = []) :
    ∀ i : Fin 56,
      LeafNodeCacheProgram.cacheTapes (cacheStart a) (i.castAdd 712) =
        MomentsProgram.Product.tapes (MomentsProgram.Product.idle
          (a.stacks 194) (a.stacks 202) (a.stacks 203) (a.stacks 201)
          (a.stacks 204) (a.stacks 212) (a.stacks 243)) i := by
  intro i
  by_cases h5 : i = 5
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (194, 5) (by decide)
  by_cases h12 : i = 12
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (202, 12) (by decide)
  by_cases h17 : i = 17
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (203, 17) (by decide)
  by_cases h22 : i = 22
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (201, 22) (by decide)
  by_cases h39 : i = 39
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (204, 39) (by decide)
  by_cases h45 : i = 45
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (212, 45) (by decide)
  by_cases h46 : i = 46
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (243, 46) (by decide)
  have hi : i.castAdd 712 ∉ cachePorts := by
    intro hm
    simp only [Fin.ext_iff] at h5 h12 h17 h22 h39 h45 h46
    simp [cachePorts, LeafNodeCacheProgram.cachePorts, LeafNodeCacheProgram.pocket,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hm
    omega
  rw [setup_local_frame a _ hi, hempty i]
  simp [MomentsProgram.Product.tapes, MomentsProgram.Product.idle,
    h5, h12, h17, h22, h39, h45, h46]

/-- The word69 is constructed by the actual constant encoder, including the
ambient coordinate count. No semantically supplied ring-one dictionary is used. -/
theorem setup_one_word (a : State 16 768) :
    LeafNodeCacheProgram.cacheTapes (cacheStart a) 69 = LeafNodeCacheProgram.rawOne a.stacks := by
  rw [(LeafNodeCacheProgram.cache_one (cacheStart a)).1]
  have h128 : (cacheStart a).stacks 128 = a.stacks 128 := by
    simp [cacheStart, clearMany_stacks, cachePorts,
      LeafNodeCacheProgram.cachePorts, LeafNodeCacheProgram.pocket]
  have h207 : (cacheStart a).stacks 207 = a.stacks 207 := by
    simp [cacheStart, clearMany_stacks, cachePorts,
      LeafNodeCacheProgram.cachePorts, LeafNodeCacheProgram.pocket]
  simp only [LeafNodeCacheProgram.rawOne, h128, h207]

theorem oneEntries_eq_constant {n B d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word B) d) (u J : ℕ)
    (hu : 0 < u) (hJ : 0 < J) :
    oneEntries (n:=n) one = Squarefree.Sparse.constant u J one := by
  simp [Squarefree.Sparse.constant, hu, hJ, oneEntries]

theorem oneEntries_good {n B d : ℕ} (one : RingProgram.Code (SubexpQuarticRing.Word B) d)
    (u J : ℕ) (hu : 0 < u) (hJ : 0 < J) :
    NativeSemantics.Good (∅ : Finset (Fin n)) u J (oneEntries one) := by
  constructor
  · intro e he
    simp only [oneEntries, List.mem_singleton] at he
    subst e
    simp [MomentsProgram.Product.ValidKey, Squarefree.Index.origin,
      Squarefree.Index.Kept, Squarefree.Index.Valid, hu, hJ]
  · simp [oneEntries, Squarefree.Sparse.keys]

theorem setup_one_bytes (a : State 16 768) {n B d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word B) d)
    (hn : (a.stacks 128).length = n) (ho : a.stacks 207 = RingProgram.flat one) :
    LeafNodeCacheProgram.cacheTapes (cacheStart a) 69 =
      MomentsProgram.Product.bytes (oneEntries (n:=n) one) := by
  rw [setup_one_word]
  simp [LeafNodeCacheProgram.rawOne, hn, ho, HashCircuitProgram.Constant.key_eq_origin,
    oneEntries, MomentsProgram.Product.bytes, MomentsProgram.Normalize.bytes,
    Squarefree.Program.rawEntries, Squarefree.Program.encodeDictionary]

/-- The retained cache envelope uses physical master sizes separately from the
caller frame. Repeating setup therefore preserves any common bound containing
both the frame and the fixed generated cache words. -/
theorem setup_cache_wordBound_max (a : State 16 768) (A M : ℕ)
    (ha : WordBound A a)
    (hcopy : ∀ p ∈ LeafNodeCacheProgram.directCopies, (a.stacks p.1).length ≤ M)
    (hn : (a.stacks 128).length ≤ M) (ho : (a.stacks 207).length ≤ M) :
    ∀ i, (LeafNodeCacheProgram.cacheTapes (cacheStart a) i).length ≤ max A (4 * M + 6) := by
  have hone : (LeafNodeCacheProgram.rawOne a.stacks).length ≤ 4 * M + 6 := by
    rw [LeafNodeCacheProgram.rawOne_length]
    omega
  intro i
  by_cases hi69 : i = 69
  · subst i
    rw [setup_one_word]
    exact hone.trans (Nat.le_max_right _ _)
  by_cases hi167 : i = 167
  · subst i
    rw [(LeafNodeCacheProgram.cache_one (cacheStart a)).2]
    have he := setup_one_word a
    rw [(LeafNodeCacheProgram.cache_one (cacheStart a)).1] at he
    rw [he]
    exact hone.trans (Nat.le_max_right _ _)
  by_cases hi : ∃ p ∈ LeafNodeCacheProgram.directCopies, p.2 = i
  · obtain ⟨p, hp, rfl⟩ := hi
    rw [setup_direct_word a p hp]
    exact (hcopy p hp).trans (le_trans (by omega : M ≤ 4 * M + 6) (Nat.le_max_right _ _))
  · have hnot : i ∉ LeafNodeCacheProgram.cachePorts := by
      simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil,
        or_false, Prod.exists, Prod.mk.injEq] at hi
      simp only [LeafNodeCacheProgram.cachePorts, List.mem_cons, List.not_mem_nil, or_false]
      aesop
    rw [LeafNodeCacheProgram.cache_frame _ i hnot, cacheStart, clearMany_stacks]
    split_ifs
    · simp
    · exact (ha i).trans (Nat.le_max_left _ _)

theorem setup_eval_wordBound_max (a : Data) (A M : ℕ)
    (ha : WordBound A a)
    (hcopy : ∀ p ∈ LeafNodeCacheProgram.directCopies, (a.stacks (lowStack p.1)).length ≤ M)
    (hn : (a.stacks 128).length ≤ M) (ho : (a.stacks 207).length ≤ M) :
    ∃ b, Eval setup (setupCost a) a b ∧ WordBound (max A (4 * M + 6)) b ∧
      (∀ i : Fin 896, 768 ≤ i.val → b.stacks i = a.stacks i) := by
  obtain ⟨b, he, hl, hh⟩ := setup_eval a
  refine ⟨b, he, ?_, hh⟩
  intro i
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val, hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj, hl j]
    exact setup_cache_wordBound_max (projectState localRegister lowStack a) A M
      (fun q => ha (lowStack q)) hcopy hn ho j
  · rw [hh i (by omega)]
    exact (ha i).trans (Nat.le_max_left _ _)

/-- Concrete setup produces the same identity dictionary used by subsequent
factor semantics, with an exact frame for all non-cache caller storage. -/
theorem setup_context (a : Data) {n B d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word B) d) (u J : ℕ)
    (hu : 0 < u) (hJ : 0 < J)
    (hempty : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
    (hn : (a.stacks 128).length = n) (ho : a.stacks 207 = RingProgram.flat one) :
    ∃ b, Eval setup (setupCost a) a b ∧
      (∀ i : Fin 56, b.stacks (i.castAdd 840) =
        MomentsProgram.Product.tapes (MomentsProgram.Product.idle
          (a.stacks 194) (a.stacks 202) (a.stacks 203) (a.stacks 201)
          (a.stacks 204) (a.stacks 212) (a.stacks 243)) i) ∧
      b.stacks 69 = MomentsProgram.Product.bytes (oneEntries (n:=n) one) ∧
      NativeSemantics.Good (∅ : Finset (Fin n)) u J (oneEntries one) ∧
      ∀ i : Fin 896, i ∉ cachePorts.map lowStack → b.stacks i = a.stacks i := by
  obtain ⟨b, he, hl, hh⟩ := setup_eval a
  let initial := projectState localRegister lowStack a
  refine ⟨b, he, ?_, ?_, oneEntries_good one u J hu hJ, ?_⟩
  · intro i
    have hi := hl (i.castAdd 712)
    exact hi.trans (setup_low initial hempty i)
  · exact (hl 69).trans (setup_one_bytes initial one hn ho)
  · intro i hi
    by_cases hlt : i.val < 768
    · let j : Fin 768 := ⟨i.val, hlt⟩
      have hj : lowStack j = i := Fin.ext rfl
      have hmem : j ∉ cachePorts := by
        intro hjmem
        exact hi (List.mem_map.mpr ⟨j, hjmem, hj⟩)
      rw [← hj, hl j, setup_local_frame initial j hmem]
      rfl
    · exact hh i (by omega)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/

variable {V R : Type*} [DecidableEq V] [CommRing R]

noncomputable section

/-- An actual decoded unit represents the neutral factor, including zero cutoffs. -/
theorem rawValue_constant_one {R : Type*} [CommRing R] {n B d : ℕ}
    (u J : ℕ) (f : RingProgram.Code (Word B) d → R)
    (c : RingProgram.Code (Word B) d) (hc : f c = 1) :
    rawValue (n := n) u J f (Squarefree.Sparse.constant u J c) = 1 := by
  have hmap : Dictionary.denoteTable f (Squarefree.Sparse.constant (V := Fin n) u J c) =
      Squarefree.Sparse.constant u J (f c) := by
    by_cases h : 0 < u ∧ 0 < J <;>
      simp [Squarefree.Sparse.constant, h, Dictionary.denoteTable]
  change jetProjection u J (Squarefree.Sparse.denote _) = 1
  rw [hmap, hc, Squarefree.Sparse.denote_constant, Squarefree.Sparse.atom_origin_one,
    jetProjection_canonical, map_one]

end

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

private theorem clear_eval (dst : Fin 896) (a : Data) :
    Eval (.call (StackRoutines.clearProgram dst 0 1)) (2 * (a.stacks dst).length + 3)
      a ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks dst a.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run dst (0 : Fin 40) 1 a.regs a.stacks)

theorem overwrite_eval (src dst : Fin 896) (hsd : src ≠ dst)
    (hst : src ≠ 841) (htd : (841 : Fin 896) ≠ dst)
    (a : Data) (htmp : a.stacks 841 = []) :
    Eval (overwrite src dst) (2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8)
      a (overwriteState src dst a) := by
  have hc := clear_eval dst a
  have ht : (StackRoutines.clearStacks dst a.stacks) 841 = [] := by
    simp [StackRoutines.clearStacks, htd, htmp]
  have hp := copyWord_eval src dst 841 hsd hst htd
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks dst a.stacks⟩ ht
  have hs : (StackRoutines.clearStacks dst a.stacks) src = a.stacks src := by
    simp [StackRoutines.clearStacks,hsd]
  simpa only [overwrite, overwriteState, hs, show 2 * (a.stacks dst).length + 3 +
    (7 * (a.stacks src).length + 5) =
    2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8 by omega] using hc.seq hp

theorem overwriteState_stacks (src dst : Fin 896) (hsd : src ≠ dst) (a : Data) :
    (overwriteState src dst a).stacks = Function.update a.stacks dst (a.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hsd]
  · simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hi]

/-- Repeated passes retain the same word bound: overwrite replaces one word,
rather than appending to a growing visit history. -/
theorem overwriteState_bound (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((overwriteState src dst a).stacks i).length ≤ B := by
  intro i
  rw [overwriteState_stacks src dst hsd]
  by_cases hi : i = dst
  · subst i
    rw [Function.update_self]
    exact hb src
  · rw [Function.update_of_ne hi]
    exact hb i

theorem overwriteState_frame (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (i : Fin 896) (hi : i ≠ dst) :
    (overwriteState src dst a).stacks i = a.stacks i := by
  rw [overwriteState_stacks src dst hsd,Function.update_of_ne hi]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of one attained-signature tuple product. The
multiplicative identity is built by the native cache routine, and every stale
output and borrowed word is cleared by an actual command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

theorem mem_lowPorts (i : Fin 896) : i ∈ lowPorts ↔ i.val < 56 := by
  constructor
  · intro hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact j.isLt
  · intro hi
    exact List.mem_ofFn.mpr ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem clear_eval (ports : List (Fin 896)) (a : Data) :
    Eval (clearBank ports) (clearCost ports a) a (cleared ports a) :=
  eval_liftCommand_from_state (clearMany ports) 841 841
    FactorAssignmentProgram.localRegister id a (Fin.castAdd_injective _ _)
    Function.injective_id (clearMany_eval ports _)

theorem cleared_stacks (ports : List (Fin 896)) (a : Data) (i : Fin 896) :
    (cleared ports a).stacks i = if i ∈ ports then [] else a.stacks i := by
  exact (embedState_stack FactorAssignmentProgram.localRegister id a
    (clearManyState ports (projectState FactorAssignmentProgram.localRegister id a))
    Function.injective_id i).trans (clearMany_stacks ports _ i)

theorem cleared_bound (ports : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : WordBound B a) : WordBound B (cleared ports a) := by
  intro i
  rw [cleared_stacks]
  split_ifs
  · simp
  · exact ha i

theorem clearCost_le (ports : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : WordBound B a) : clearCost ports a ≤ ports.length * (2 * B + 3) + 1 :=
  Nat.add_le_add_right (clearManyCost_le ports _ B ha) 1

theorem finish_eval (a : Data) (htmp : a.stacks 841 = []) :
    Eval finish (finishCost a) a (finished a) := by
  have h1 := QueryTupleVisitor.overwrite_eval 69 852 (by decide) (by decide) (by decide) a htmp
  have ht : (QueryTupleVisitor.overwriteState 69 852 a).stacks 841 = [] :=
    (QueryTupleVisitor.overwriteState_frame _ _ (by decide) _ _ (by decide)).trans htmp
  have h2 := QueryTupleVisitor.overwrite_eval 703 869 (by decide) (by decide) (by decide)
    (QueryTupleVisitor.overwriteState 69 852 a) ht
  have h869 := QueryTupleVisitor.overwriteState_frame 69 852 (by decide) a 869 (by decide)
  have h703 := QueryTupleVisitor.overwriteState_frame 69 852 (by decide) a 703 (by decide)
  have he := h1.seq (h2.seq (clear_eval lowPorts (copied a)))
  simpa only [finish, finishCost, finished, copied, h869, h703] using he

theorem finished_stacks (a : Data) (i : Fin 896) :
    (finished a).stacks i = if i ∈ lowPorts then [] else
      if i = 869 then a.stacks 703 else if i = 852 then a.stacks 69 else a.stacks i := by
  rw [finished, cleared_stacks, copied,
    QueryTupleVisitor.overwriteState_stacks 703 869 (by decide),
    QueryTupleVisitor.overwriteState_stacks 69 852 (by decide)]
  simp only [Function.update_of_ne (by decide : (703 : Fin 896) ≠ 852)]
  simp only [Function.update_apply]

theorem copied_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound B (copied a) :=
  QueryTupleVisitor.overwriteState_bound 703 869 (by decide) _ B
    (QueryTupleVisitor.overwriteState_bound 69 852 (by decide) a B ha)

theorem finished_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound B (finished a) := cleared_bound lowPorts _ B (copied_bound a B ha)

theorem finishCost_le (a : Data) (B : ℕ) (ha : WordBound B a) :
    finishCost a ≤ 130 * B + 185 := by
  have hc := clearCost_le lowPorts (copied a) B (copied_bound a B ha)
  have h1 := ha 852
  have h2 := ha 69
  have h3 := ha 869
  have h4 := ha 703
  rw [show lowPorts.length = 56 by simp [lowPorts]] at hc
  unfold finishCost
  omega

/-- One actual initialization constructs its unit and restores the semantic
caller envelope. Physical masters are bounded independently, so the same
bound can be reused for every attained tuple. -/
theorem command_run (a : Data) {n width d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word width) d) (u J P B : ℕ)
    (hu : 0 < u) (hJ : 0 < J)
    (hn : (a.stacks 128).length = n) (ho : a.stacks 207 = RingProgram.flat one)
    (ha : WordBound B a)
    (hcopy : ∀ p ∈ LeafNodeCacheProgram.directCopies,
      (a.stacks (FactorAssignmentProgram.lowStack p.1)).length ≤ P)
    (hnP : (a.stacks 128).length ≤ P) (hoP : (a.stacks 207).length ≤ P)
    (hPB : 4 * P + 6 ≤ B) :
    ∃ steps b, Eval command steps a b ∧ Initialized a b (n:=n) one u J ∧
      WordBound B b ∧ steps ≤ 1500 * (B + 1) := by
  let start := cleared entryPorts a
  have hstart : WordBound B start := cleared_bound entryPorts a B ha
  have hframe (i : Fin 896) (hi : i ∉ entryPorts) : start.stacks i = a.stacks i := by
    exact (cleared_stacks entryPorts a i).trans (ite_eq_right hi)
  have hlow : ∀ i : Fin 56, start.stacks (i.castAdd 840) = [] := by
    intro i
    rw [cleared_stacks, ite_eq_left]
    exact List.mem_append_left _ ((mem_lowPorts _).mpr i.isLt)
  have h128 := hframe 128 (by decide)
  have h207 := hframe 207 (by decide)
  obtain ⟨b, he, _, hunit, hgood, hcache⟩ := FactorAssignmentProgram.setup_context start one u J
    hu hJ hlow (by simpa only [h128] using hn) (h207.trans ho)
  have hmaster : ∀ p ∈ LeafNodeCacheProgram.directCopies,
      FactorAssignmentProgram.lowStack p.1 ∉ entryPorts := by
    intro p hp
    simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have hcopy' : ∀ p ∈ LeafNodeCacheProgram.directCopies,
      (start.stacks (FactorAssignmentProgram.lowStack p.1)).length ≤ P := by
    intro p hp
    rw [hframe _ (hmaster p hp)]
    exact hcopy p hp
  obtain ⟨c, hc, hbound, _⟩ := FactorAssignmentProgram.setup_eval_wordBound_max start B P hstart
    hcopy' (by simpa only [h128] using hnP) (by simpa only [h207] using hoP)
  have hbc := Eval.final_unique (128 : Fin 896) he hc
  have hb : WordBound B b := by
    rw [hbc]
    simpa only [max_eq_left hPB] using hbound
  have htmp : b.stacks 841 = [] := by
    rw [hcache 841 (by decide)]
    exact (cleared_stacks entryPorts a 841).trans (ite_eq_left (by decide))
  have hwhole := (clear_eval entryPorts a).seq (he.seq (finish_eval b htmp))
  refine ⟨_, finished b, hwhole, ?_, finished_bound b B hb, ?_⟩
  · constructor
    · rw [finished_stacks, ite_eq_right (by decide : (852 : Fin 896) ∉ lowPorts),
        ite_eq_right (by decide : (852 : Fin 896) ≠ 869), ite_eq_left rfl]
      exact hunit
    · exact hgood
    · rw [finished_stacks, ite_eq_right (by decide : (869 : Fin 896) ∉ lowPorts),
        ite_eq_left rfl,
        hcache 703 (by decide), hframe 703 (by decide)]
    · intro i
      rw [finished_stacks, ite_eq_left ((mem_lowPorts _).mpr i.isLt)]
    · rw [finished_stacks, ite_eq_right (by decide : (841 : Fin 896) ∉ lowPorts),
        ite_eq_right (by decide : (841 : Fin 896) ≠ 869),
        ite_eq_right (by decide : (841 : Fin 896) ≠ 852)]
      exact htmp
    · intro i hi
      have hin : i ∉ entryPorts := fun h => hi (List.mem_append_left _ (List.mem_append_left _ h))
      have hcn : i ∉ FactorAssignmentProgram.cachePorts.map FactorAssignmentProgram.lowStack :=
        fun h => hi (List.mem_append_left _ (List.mem_append_right _ h))
      have h852 : i ≠ 852 := by
        intro h; subst i; exact hi (List.mem_append_right _ (by simp))
      have h869 : i ≠ 869 := by
        intro h; subst i; exact hi (List.mem_append_right _ (by simp))
      have hlo : i ∉ lowPorts := fun h => hin (List.mem_append_left _ h)
      rw [finished_stacks, ite_eq_right hlo, ite_eq_right h869, ite_eq_right h852,
        hcache i hcn, hframe i hin]
  · have hentry := clearCost_le entryPorts a B ha
    have hsetup := FactorAssignmentProgram.setupCost_le start B hstart
    have hfinish := finishCost_le b B hb
    rw [show entryPorts.length = 57 by simp [entryPorts, lowPorts]] at hentry
    omega


open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

namespace QueryReady

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a b : Data}
    (h : QueryReady q node H high E U P a) (hf : QueryMasterFrame a b) :
    QueryReady q node H high E U P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf.word 128 (by decide)).trans h.ambient
    theta := (hf.word 78 (by decide)).trans h.theta
    modulus := (hf.word 194 (by decide)).trans h.modulus
    table := (hf.word 201 (by decide)).trans h.table
    width := (hf.word 202 (by decide)).trans h.width
    scalarZero := (hf.word 203 (by decide)).trans h.scalarZero
    degree := (hf.word 204 (by decide)).trans h.degree
    one := (hf.word 207 (by decide)).trans h.one
    minus := (hf.word 211 (by decide)).trans h.minus
    precision := (hf.word 212 (by decide)).trans h.precision
    order := (hf.word 243 (by decide)).trans h.order
    zero := (hf.word 280 (by decide)).trans h.zero
    code := (hf.word 281 (by decide)).trans h.code
    clauses := (hf.word 700 (by decide)).trans h.clauses
    rows := (hf.word 701 (by decide)).trans h.rows
    rowCount := (hf.word 704 (by decide)).trans h.rowCount
    markedIndex := (hf.word 705 (by decide)).trans h.markedIndex
    markedFlag := (hf.word 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf.word 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf.word 708 (by decide))).trans h.indexWidth
    highMask := (hf.word 702 (by decide)).trans h.highMask
    highBits := (hf.word 703 (by decide)).trans h.highBits
    outer := (hf.word 858 (by decide)).trans h.outer
    inner := (hf.word 857 (by decide)).trans h.inner
    outerFree := h.outerFree
    innerSubset := h.innerSubset
    colors := (hf.word 130 (by decide)).trans h.colors
    nodes := (hf.word 131 (by decide)).trans h.nodes
    typeWidth := (hf.word 132 (by decide)).trans h.typeWidth
    positive := (hf.word 710 (by decide)).trans h.positive
    negative := (hf.word 711 (by decide)).trans h.negative
    sourceWidth := (hf.word 140 (by decide)).trans h.sourceWidth
    power := (hf.word 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf.word 138 (by decide)).trans h.radius
    offset := (hf.word 139 (by decide)).trans h.offset
    metadata := (hf.word 135 (by decide)).trans h.metadata
    plans := (hf.word 136 (by decide)).trans h.plans
    inverses := (hf.word 713 (by decide)).trans h.inverses
    negatives := (hf.word 714 (by decide)).trans h.negatives
    differences := (hf.word 715 (by decide)).trans h.differences
    ringWidth := (hf.word 717 (by decide)).trans h.ringWidth
    rowWidth := (hf.word 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf.word 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈masterPorts := by
      simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
        List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf.word _ hm]
    exact h.cacheCaps p hp
  · rw [hf.word 128 (by decide)]
    exact h.ambientCap
  · rw [hf.word 207 (by decide)]
    exact h.oneCap

end QueryReady

namespace PairAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : PairAccumulatorMeaning q value a) (hf : b.stacks 851=a.stacks 851) :
    PairAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end PairAccumulatorMeaning

/-- Actual cache initialization changes no retained query input. -/
theorem initialized_masterFrame {a b : Data} {n width d u J : ℕ}
    {one : RingProgram.Code (Word width) d}
    (h : QueryTupleInit.Initialized a b (n:=n) one u J) : QueryMasterFrame a b := by
  constructor
  intro i hi
  apply h.frame i
  simp only [masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- The neutral tuple product is decoded from the coefficient word produced
by the ring initializer. It is not a supplied unit dictionary. -/
theorem initialized_unit {r Q n d : ℕ} (q : Factor.Spec r Q n d) {a b : Data}
    (h : QueryTupleInit.Initialized a b (n:=n) q.p.ops.oneRun.1 q.p.t q.J) :
    ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
      b.stacks 852=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
      rawValue q.p.t q.J q.p.ops.decode entries=1 := by
  refine ⟨FactorAssignmentProgram.oneEntries q.p.ops.oneRun.1,h.unit,
    ⟨h.unit_good.valid,h.unit_good.nodup⟩,?_⟩
  rw [FactorAssignmentProgram.oneEntries_eq_constant _ q.p.t q.J q.p.ht q.hJ]
  exact rawValue_constant_one q.p.t q.J q.p.ops.decode q.p.ops.oneRun.1 q.p.ops.one_correct

/-- The actual tuple initializer restores the fixed retained cap, carries
the current pair sum, and creates the correctly decoded neutral product. -/
theorem initialize_run_oai {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P B : ℕ} {a : Data} {value : Truncated (q.p.model.O q.p.t) q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q value a)
    (ha : WordBound B a) (hPB : 4*P+6≤B) :
    ∃ steps b, Eval QueryTupleInit.command steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q value b ∧
      QueryTupleInit.Initialized a b (n:=n) q.p.ops.oneRun.1 q.p.t q.J ∧
      WordBound B b ∧ steps≤1500*(B+1) ∧
      ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
        b.stacks 852=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
          rawValue q.p.t q.J q.p.ops.decode entries=1 := by
  have hn : (a.stacks 128).length=n := by rw [hr.ambient,List.length_replicate]
  obtain ⟨steps,b,he,hi,hb,hcost⟩ := QueryTupleInit.command_run a q.p.ops.oneRun.1
    q.p.t q.J P B q.p.ht q.hJ hn hr.one ha hr.cacheCaps hr.ambientCap hr.oneCap hPB
  exact ⟨steps,b,he,hr.frame (initialized_masterFrame hi),
    hm.frame (hi.frame 851 (by decide)),hi,hb,hcost,initialized_unit q hi⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.initialize_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.initialize_run_oai
