-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.Entry.prepare
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:33:55.398033+00:00
-- url     : https://prove2.me/submissions/980f0c53-900f-44e0-a344-cfa8f933675e

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem mem_workerPorts (i : Fin 768) : i ∈ workerPorts ↔ 340 ≤ i.val ∧ i.val < 680 := by
  simp only [workerPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=i.val at hv
    omega
  · intro hi
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

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

end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/


/-! Denotation of the concrete raw row recurrence used by the native program. -/


/-! Instantiation at the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

theorem model_table_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (i j : Fin d) :
    RingBasis.basis (a.F t) i * RingBasis.basis (a.F t) j =
      ∑ k, SubexponentialSAT.LiftRing.of (a.F t) (wordValue 3 t (modelTable t a M cache i j k)) *
        RingBasis.basis (a.F t) k := by
  let _ : Fact (1 < 3^t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)⟩
  rw [RingBasis.basis_mul (a.F t) (a.F_monic t ht) (a.F_degree t ht) i j]
  apply Finset.sum_congr rfl
  intro k _
  have hc : wordValue 3 t (modelTable t a M cache i j k) =
      RingBasis.structureConstant (a.F t) i j k := by
    change (RingProgram.scalarRing 3 t M cache).decode
      ((RingProgram.structureTableRun (RingProgram.scalarRing 3 t M cache).program
        (RingProgram.liftCoefficientsRun t a.coefficients).1).1 i j k) = _
    rw [RingProgram.structureTableRun_remainder (RingProgram.scalarRing 3 t M cache) hd]
    change (Polynomial.X ^ (i.val+j.val) %ₘ RingProgram.quotientPolynomial
      (RingProgram.scalarRing 3 t M cache) (RingProgram.liftCoefficientsRun t a.coefficients).1).coeff k = _
    rw [RingProgram.modelPolynomial t ht a M cache]
    all_goals rfl
  rw [hc]

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

theorem initialize_eval (a : Data) :
    Eval «initialize_» (initializeCost a) a (initialized a) :=
  eval_liftCommand_from_state (clearMany entryScratch) 175 854 localRegister id a
    (Fin.castAdd_injective _ _) Function.injective_id
    (clearMany_eval entryScratch (projectState localRegister id a))

theorem initialized_stacks (a : Data) (i : Fin 896) :
    (initialized a).stacks i = if i ∈ entryScratch then [] else a.stacks i := by
  exact (embedState_stack localRegister id a
    (clearManyState entryScratch (projectState localRegister id a))
    Function.injective_id i).trans (clearMany_stacks entryScratch
      (projectState localRegister id a) i)

theorem initialized_wordBound (a : Data) (P : ℕ) (ha : WordBound P a) :
    WordBound P (initialized a) := by
  intro i
  rw [initialized_stacks]
  split_ifs
  · simp
  · exact ha i

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableDenotation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual normalized incidence payload has the canonical scalarized
source denotation. Source arrays are witnesses produced by the finite source
machine; their full polynomial meanings identify one fixed incidence jet. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes LayoutProgram
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

theorem rawDenote_constant {n B d : ℕ} (u J : ℕ)
    (f : RingProgram.Code (Word B) d → R) (c : RingProgram.Code (Word B) d) :
    rawDenote (n := n) f (Squarefree.Sparse.constant u J c) =
      Squarefree.canonical u J (Squarefree.Sparse.atom Squarefree.Index.origin (f c)) := by
  have hm : Dictionary.denoteTable f (Squarefree.Sparse.constant (V := Fin n) u J c) =
      Squarefree.Sparse.constant u J (f c) := by
    by_cases h : 0 < u ∧ 0 < J <;>
      simp [Squarefree.Sparse.constant, h, Dictionary.denoteTable]
  change Squarefree.Sparse.denote _ = _
  rw [hm, Squarefree.Sparse.denote_constant]

theorem oneEntries_rawDenote {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (one : RingProgram.Code (Word B) d)
    (hone : f one = 1) :
    rawDenote f (FactorAssignmentProgram.oneEntries (n := n) one) = 1 := by
  simp [FactorAssignmentProgram.oneEntries, rawDenote, Dictionary.denoteTable,
    Squarefree.Sparse.denote, Squarefree.Sparse.decode, hone]

/-- The actual singleton identity is neutral even when one cutoff is zero. -/
theorem oneEntries_rawValue {n B d : ℕ} (u J : ℕ)
    (f : RingProgram.Code (Word B) d → R) (one : RingProgram.Code (Word B) d)
    (hone : f one = 1) :
    rawValue u J f (FactorAssignmentProgram.oneEntries (n := n) one) = 1 := by
  rw [rawValue, oneEntries_rawDenote f one hone, map_one]


/-- Paid cache setup identifies the actual source context, encoded ring unit,
negative unit, and idempotent tape. All assumptions are physical master words;
the table law and coefficient meanings come from the same produced source ring. -/
theorem setup_source_context {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (width : List Bool) (hw : width.length = baseWidth 3 p.t)
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 p.t)))
    (a : FactorAssignmentProgram.Data)
    (hempty : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
    (hn : (a.stacks 128).length = n)
    (hm : a.stacks 194 = p.modulus.bits)
    (hwidth : a.stacks 202 = width) (hz : a.stacks 203 = p.cache.zero.val)
    (htable : a.stacks 201 = RingTriple.tableEncoding
      (HornerProgram.modelTable p.t p.model p.modulus p.cache))
    (hdegree : a.stacks 204 = List.replicate d true)
    (hprec : a.stacks 212 = List.replicate u true)
    (hjet : a.stacks 243 = List.replicate J true)
    (hone : a.stacks 207 = RingProgram.flat p.ops.oneRun.1)
    (hminus : a.stacks 211 = RingProgram.flat p.minusOne)
    (hdigits : a.stacks 281 = IdempotentApplyProgram.triplesTape digits) :
    ∃ b, StructuredCalls.Eval FactorAssignmentProgram.setup
        (FactorAssignmentProgram.setupCost a) a b ∧
      (∀ i : Fin 56, b.stacks (i.castAdd 840) = IdempotentApplyProgram.Steps.low
        (LeafProgram.Factor.sourceContext p n u J width hw) i) ∧
      b.stacks 69 = Product.bytes (FactorAssignmentProgram.oneEntries (n := n) p.ops.oneRun.1) ∧
      LeafProgram.NativeSemantics.Good ∅ u J (FactorAssignmentProgram.oneEntries (n := n) p.ops.oneRun.1) ∧
      rawDenote p.ops.decode (FactorAssignmentProgram.oneEntries (n := n) p.ops.oneRun.1) =
        Squarefree.canonical u J 1 ∧
      rawValue u J p.ops.decode (FactorAssignmentProgram.oneEntries (n := n) p.ops.oneRun.1) = 1 ∧
      b.stacks 76 = RingProgram.flat p.minusOne ∧ p.ops.decode p.minusOne = -1 ∧
      b.stacks 143 = IdempotentApplyProgram.triplesTape digits ∧
      (b.stacks 88).length = n ∧
      (∀ i j : Fin d, RingBasis.basis (p.model.F p.t) i * RingBasis.basis (p.model.F p.t) j =
        ∑ k, LiftRing.of (p.model.F p.t)
          (wordValue 3 p.t ((LeafProgram.Factor.sourceContext p n u J width hw).table i j k)) *
            RingBasis.basis (p.model.F p.t) k) ∧
      ∀ i : Fin 896, i ∉ FactorAssignmentProgram.cachePorts.map FactorAssignmentProgram.lowStack →
        b.stacks i = a.stacks i := by
  obtain ⟨b, he, hlo, hunit, hgood, hframe⟩ :=
    FactorAssignmentProgram.setup_context a p.ops.oneRun.1 u J hu hJ hempty hn hone
  obtain ⟨c, hec, hcache, _⟩ := FactorAssignmentProgram.setup_eval a
  have hcb : c = b := StructuredCalls.Eval.final_unique 0 hec he
  have copied (pair : Fin 768 × Fin 768) (hp : pair ∈ LeafNodeCacheProgram.directCopies) :
      b.stacks (FactorAssignmentProgram.lowStack pair.2) =
        a.stacks (FactorAssignmentProgram.lowStack pair.1) := by
    rw [← hcb]
    exact (hcache pair.2).trans (FactorAssignmentProgram.setup_direct_word _ pair hp)
  refine ⟨b, he, ?_, hunit, hgood, ?_, oneEntries_rawValue u J _ _ p.ops.one_correct,
    ?_, p.hminus, ?_, ?_, LeafProgram.NativeSemantics.model_table_correct p.t p.ht p.hd p.model p.modulus p.cache,
    hframe⟩
  · intro i
    rw [hlo i, hm, hwidth, hz, htable, hdegree, hprec, hjet]
    rfl
  · rw [FactorAssignmentProgram.oneEntries_eq_constant _ u J hu hJ,
      rawDenote_constant, p.ops.one_correct, Squarefree.Sparse.atom_origin_one]
  · exact (copied (211,76) (by decide)).trans hminus
  · exact (copied (281,143) (by decide)).trans hdigits
  · exact (congrArg List.length (copied (128,88) (by decide))).trans hn

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The real initializer and paid cache setup establish the physical boundary
for the actual stored-ID fold. Bounds are fixed before that fold; the current
Good-empty-support seed is serialized on151, the unread suffix on150 and the
reversed original ID on149. No execution service is a field below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem table_entry_written (i : Fin 896) (hi : i ∈ FactorTableProgram.entryPorts) :
    i ∈ FactorTableSpace.writtenPorts := by
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact List.mem_append_left _ (List.mem_map.mpr ⟨j,(List.mem_filter.mp hj).1,rfl⟩)
  · exact List.mem_append_right _ hi

/-- Numeric support of the actual relocated source writes. -/
theorem written_bounds (i : Fin 896) (hi : i ∈ FactorTableSpace.writtenPorts) :
    i.val = 62 ∨ (340 ≤ i.val ∧ i.val ≤ 684) ∨
      i.val = 881 ∨ i.val = 882 ∨ (885 ≤ i.val ∧ i.val ≤ 892) := by
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have hjb := Incidence.mem_workerPorts j |>.mp hj
    unfold FactorTableProgram.basePort
    split_ifs
    all_goals simp only [Fin.coe_ofNat_eq_mod, Fin.val_castAdd]
    all_goals omega
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [Fin.coe_ofNat_eq_mod]

theorem retained_not_entry (i : Fin 896) (hi : i ∈ retainedPorts) :
    i ∉ entryScratch := by
  have small : ∀ i ∈ retainedPorts,
      i ∉ ([149,150,151,159,854] ++ callbackScratch.map lowStack : List (Fin 896)) :=
    List.forall_iff_forall_mem.mp (by decide)
  have outside : ∀ i ∈ retainedPorts,
      i.val ≠ 62 ∧ (i.val < 340 ∨ 684 < i.val) ∧ i.val ≠ 881 ∧ i.val ≠ 882 ∧
        (i.val < 885 ∨ 892 < i.val) := List.forall_iff_forall_mem.mp (by decide)
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · exact small i hi hm
  · have hw := written_bounds i (table_entry_written i hm)
    have ho := outside i hi
    omega

theorem retained_not_cache (i : Fin 896) (hi : i ∈ retainedPorts) :
    i ∉ cachePorts.map lowStack :=
  (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ retainedPorts,
    i ∉ cachePorts.map lowStack) i hi

theorem entry_not_cache (i : Fin 896) (hi : i ∈ entryScratch) :
    i ∉ LeafNodeCacheProgram.cachePorts.map lowStack := by
  have small : ∀ i ∈ ([149,150,151,159,854] ++ callbackScratch.map lowStack : List (Fin 896)),
      i ∉ LeafNodeCacheProgram.cachePorts.map lowStack := List.forall_iff_forall_mem.mp (by decide)
  rcases List.mem_append.mp hi with hi | hi
  · exact small i hi
  · intro hm
    have hw := written_bounds i (table_entry_written i hi)
    have hc : i.val < 340 ∧ i.val ≠ 62 :=
      (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ LeafNodeCacheProgram.cachePorts.map lowStack,
        i.val < 340 ∧ i.val ≠ 62) i hm
    omega

theorem table_written_entry (i : Fin 896) (hi : i ∈ FactorTableSpace.writtenPorts)
    (h556 : i ≠ 556) : i ∈ entryScratch := by
  apply List.mem_append_right
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨j,List.mem_filter.mpr ⟨hj,?_⟩,rfl⟩
    have hn : j ≠ 556 := by intro he; subst j; exact h556 rfl
    simpa only [decide_eq_true_eq] using hn
  · exact List.mem_append_right _ hi

theorem scalar_frame {t d J R n : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d}
    {a b : State 16 768}
    (h : FactorTableNative.ScalarMasters t model M cache J R theta a n)
    (hf : ∀ i ∈ scalarPorts, b.stacks i = a.stacks i) :
    FactorTableNative.ScalarMasters t model M cache J R theta b n := by
  refine ⟨h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hf 194 (by decide)]; exact h.modulus
  · rw [hf 202 (by decide)]; exact h.width
  · rw [hf 203 (by decide)]; exact h.zero
  · rw [hf 201 (by decide)]; exact h.table
  · rw [hf 204 (by decide)]; exact h.degree
  · rw [hf 145 (by decide)]; exact h.choicesLength
  · rw [hf 280 (by decide)]; exact h.zeroWord
  · rw [hf 207 (by decide)]; exact h.oneWord
  · rw [hf 78 (by decide)]; exact h.thetaWord
  · rw [hf 128 (by decide)]; exact h.ambientCount
  · rw [hf 243 (by decide)]; exact h.targetCount
  · rw [hf 138 (by decide)]; exact h.radius
  · rw [hf 703 (by decide)]; exact h.highLength

theorem source_frame {r Q d : ℕ} {p : LayoutProgram.SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)}
    {P : OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData (Fin ps.length)
      (OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType r Q 1)} {a b : State 16 768}
    (h : FactorTableNative.SourceMasters p ps P a)
    (hf : ∀ i ∈ sourcePorts, b.stacks i = a.stacks i) :
    FactorTableNative.SourceMasters p ps P b := by
  constructor
  · rw [hf 130 (by decide)]; exact h.colors
  · rw [hf 131 (by decide)]; exact h.nodes
  · rw [hf 132 (by decide)]; exact h.typeWidth
  · rw [hf 710 (by decide)]; exact h.positive
  · rw [hf 711 (by decide)]; exact h.negative
  · rw [hf 140 (by decide)]; exact h.scalarWidth
  · rw [hf 712 (by decide)]; exact h.power
  · exact h.powerNegative
  · rw [hf 138 (by decide)]; exact h.radius
  · rw [hf 139 (by decide)]; exact h.offset
  · rw [hf 135 (by decide)]; exact h.metadata
  · rw [hf 136 (by decide)]; exact h.plans
  · rw [hf 713 (by decide)]; exact h.inverses
  · rw [hf 714 (by decide)]; exact h.negatives
  · rw [hf 715 (by decide)]; exact h.differences
  · rw [hf 717 (by decide)]; exact h.ringWidth
  · rw [hf 716 (by decide)]; exact h.rowWidth
  · rw [hf 280 (by decide)]; exact h.zero
  · rw [hf 207 (by decide)]; exact h.one
  · rw [hf 211 (by decide)]; exact h.minusOne
  · rw [hf 728 (by decide)]; exact h.inverseDenominator

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}
  {one : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data}


/-- The same fixed initializer/cache command constructs every prepared fact
used by the concrete callback. The fixed boundary P is restored on return. -/
theorem Entry.prepare_oai (h : Entry q P M S a) :
    ∃ b, Eval prepare (prepareCost a) a b ∧
      Ready q P S (oneEntries (n := n) q.p.ops.oneRun.1) b ∧
      NativeSemantics.Good ∅ q.u q.J (oneEntries (n := n) q.p.ops.oneRun.1) ∧
      TruncatedRingProgram.rawDenote q.p.ops.decode (oneEntries (n := n) q.p.ops.oneRun.1) =
        Squarefree.canonical q.u q.J 1 ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode
        (oneEntries (n := n) q.p.ops.oneRun.1) = 1 ∧
      (∀ i ∈ retainedPorts, b.stacks i = a.stacks i) ∧
      (∀ i ∈ ([149,150,151,159,854] : List (Fin 896)), b.stacks i = []) := by
  let a0 := initialized a
  have initFrame (i : Fin 896) (hi : i ∈ retainedPorts) : a0.stacks i = a.stacks i := by
    rw [initialized_stacks, ite_eq_right (retained_not_entry i hi)]
  have scalarMem (i : Fin 768) (hi : i ∈ scalarPorts) :
      FactorTableProgram.basePort i ∈ retainedPorts :=
    List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_append_left _ hi,rfl⟩)
  have sourceMem (i : Fin 768) (hi : i ∈ sourcePorts) :
      FactorTableProgram.basePort i ∈ retainedPorts :=
    List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_append_right _ hi,rfl⟩)
  have hscalar := scalar_frame (b := projectState localRegister FactorTableProgram.basePort a0)
    h.scalar (fun i hi => initFrame _ (scalarMem i hi))
  have hmasters := source_frame (b := projectState localRegister FactorTableProgram.basePort a0)
    h.masters (fun i hi => initFrame _ (sourceMem i hi))
  have hlow : ∀ i : Fin 56, a0.stacks (i.castAdd 840) = [] := by
    intro i
    rw [initialized_stacks]
    split_ifs
    · rfl
    · exact h.lowBlank i
  have hn : (a0.stacks 128).length = n := by
    rw [show a0.stacks 128 = List.replicate n true from hscalar.ambientCount]
    simp
  obtain ⟨b,he,hlo,hunit,hgood,hraw,hdense,hminus,hminusValue,hdigits,hshape,htable,hframe⟩ :=
    FactorTableDenotation.setup_source_context q.p n q.u q.J q.hu q.hJ q.width
      q.widthLength q.digits a0 hlow hn hscalar.modulus
      ((initFrame 202 (by decide)).trans h.width) hscalar.zero hscalar.table
      ((initFrame 204 (by decide)).trans h.degree)
      ((initFrame 212 (by decide)).trans h.precision) hscalar.targetCount hscalar.oneWord
      hmasters.minusOne ((initFrame 281 (by decide)).trans h.digits)
  have frame (i : Fin 896) (hi : i ∈ retainedPorts) : b.stacks i = a.stacks i :=
    (hframe i (retained_not_cache i hi)).trans (initFrame i hi)
  have hinit : WordBound P a0 := initialized_wordBound a P h.incoming
  have shrink (i : Fin 896) : (a0.stacks i).length ≤ (a.stacks i).length := by
    rw [initialized_stacks]
    split_ifs
    · simp
    · exact le_rfl
  obtain ⟨c,hec,hbound,_⟩ := setup_eval_wordBound_max a0 P M hinit
    (fun pair hp => (shrink (lowStack pair.1)).trans (h.copies pair hp))
    ((shrink 128).trans h.ambientCap) ((shrink 207).trans h.oneCap)
  have hcb : c = b := Eval.final_unique 0 hec he
  have hb : WordBound P b := by
    simpa only [hcb,max_eq_left h.cacheFits] using hbound
  obtain ⟨z,hez,hcache,hhigh⟩ := setup_eval a0
  have hzb : z = b := Eval.final_unique 0 hez he
  have empty (i : Fin 896) (hi : i ∈ entryScratch) : b.stacks i = [] := by
    have hi0 : a0.stacks i = [] := by rw [initialized_stacks, ite_eq_left hi]
    have hnot : i ∉ LeafNodeCacheProgram.cachePorts.map lowStack := entry_not_cache i hi
    by_cases hlt : i.val < 768
    · let j : Fin 768 := ⟨i.val,hlt⟩
      have hj : lowStack j = i := Fin.ext rfl
      have hn : j ∉ LeafNodeCacheProgram.cachePorts := by
        intro hm
        exact hnot (List.mem_map.mpr ⟨j,hm,hj⟩)
      rw [← hzb,← hj,hcache j,LeafNodeCacheProgram.cache_frame _ j hn,
        cacheStart,clearMany_stacks]
      split_ifs
      · rfl
      · exact hi0
    · rw [← hzb,hhigh i (by omega)]
      exact hi0
  have hready : Ready q P S (oneEntries (n := n) q.p.ops.oneRun.1) b := by
    refine ⟨scalar_frame h.scalar (fun i hi => frame _ (scalarMem i hi)),
      source_frame h.masters (fun i hi => frame _ (sourceMem i hi)),hb,h.size,h.radius,
      ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hunit,?_,hdigits,hshape,?_,?_,h.seedFits⟩
    · exact (frame 701 (by decide)).trans h.rows
    · exact (frame 700 (by decide)).trans h.clauses
    · exact (frame 704 (by decide)).trans h.count
    · exact (frame 705 (by decide)).trans h.mark
    · exact (frame 706 (by decide)).trans h.flag
    · intro i hi
      exact empty (lowStack i) (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨i,hi,rfl⟩)))
    · intro i hi h62 h556
      exact empty i (table_written_entry i hi h556)
    · rw [frame 857 (by decide)]; exact h.correction
    · rw [frame 708 (by decide)]; exact h.hashWidth
    · rw [frame 707 (by decide)]; exact h.hashModulus
    · rw [frame 280 (by decide)]
      rw [show a.stacks 280 = RingProgram.flat q.p.ops.zeroRun.1 from h.scalar.zeroWord,
        RingProgram.flat_length]
    · intro i
      exact hlo i
    · exact hminus.trans (congrArg RingProgram.flat h.minus.symm)
    · exact empty 63 (by decide)
    · intro i hi
      exact empty _ ((List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ FactorServices.clauseScratch,
        lowStack (Clause.callerStacks i) ∈ entryScratch) i hi)
  exact ⟨b,(initialize_eval a).seq he,hready,hgood,hraw,hdense,frame,
    fun i hi => empty i (List.mem_append_left _ (List.mem_append_left _ hi))⟩

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.Entry.prepare_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.Entry.prepare_oai
