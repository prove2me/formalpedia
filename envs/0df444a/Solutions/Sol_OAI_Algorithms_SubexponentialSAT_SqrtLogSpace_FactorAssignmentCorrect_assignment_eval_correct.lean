-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.assignment_eval_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:37:29.505809+00:00
-- url     : https://prove2.me/submissions/d7301454-5998-4a5b-9d45-5c52b2628d92

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafNodeCacheProgram_local_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary_Entry_prepare
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCorrect_prepared_product_eval_correct

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
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

theorem initializeCost_le (a : Data) (P : ℕ) (ha : WordBound P a) :
    initializeCost a ≤ entryScratch.length * (2 * P + 3) + 1 :=
  Nat.add_le_add_right
    (clearManyCost_le entryScratch (projectState localRegister id a) P ha) 1

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorJet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The incidence meaning depends only on the merged assignment and the
fixed-high context. Parser and accumulator contents do not enter it. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram

theorem factorJet_frame {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (a b : Fin 768 → List Bool)
    (h145 : a 145=b 145) (h702 : a 702=b 702) (h703 : a 703=b 703) :
    factorJet p ps P n f j theta a=factorJet p ps P n f j theta b := by
  unfold factorJet sourceIncidenceJet
  simp only [choiceStore,show (574:Fin 768)≠546 by decide,show (575:Fin 768)≠546 by decide,
    show (575:Fin 768)≠574 by decide,ite_false,ite_true, if_true]
  rw [h145,h702,h703]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}
  {one : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data}

/-- Initialization and cache reconstruction cost one fixed linear polynomial
in the structural boundary, independently of the number of factor records. -/
theorem prepareCost_le (a : FactorAssignmentProgram.Data) (P : ℕ) (ha : WordBound P a) :
    prepareCost a ≤ entryScratch.length * (2*P+3) + 1100*(P+1) + 2 := by
  have hi := initializeCost_le a P ha
  have hs := setupCost_le (initialized a) P (initialized_wordBound a P ha)
  unfold prepareCost
  omega


end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual initializer, source-context cache, dispatcher, specialized
incidence producer and factor arithmetic instantiate the stored-ID fold.
The output is the entire specialized coefficient-ring product on stack854.
Every resource assertion below concerns this same fixed command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary FactorAssignmentLoop

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}

/-- The reassociation is between the two actual syntax trees, with the
same initializer and setup executions. -/
theorem prepare_product_eval {a b c : FactorAssignmentProgram.Data} {k l : ℕ}
    (hp : Eval FactorAssignmentBoundary.prepare k a b) (hq : Eval product l b c) :
    Eval assignment (k + l) a c := by
  unfold FactorAssignmentBoundary.prepare at hp
  cases hp with
  | seq hi hs =>
    simpa only [assignment, Nat.add_assoc] using hi.seq (hs.seq hq)

/-- Initialization and cache rebuilding preserve all unallocated caller
storage. This includes the representative baseline, correction mask and head
sum, without a premise about their contents. -/
theorem prepare_stack_frame {a b : FactorAssignmentProgram.Data} {k : ℕ}
    (he : Eval FactorAssignmentBoundary.prepare k a b) (i : Fin 896)
    (hi : i ∉ entryScratch) (hc : i ∉ cachePorts.map lowStack) :
    b.stacks i = a.stacks i := by
  obtain ⟨z,hz,hlo,hhi⟩ := setup_eval (initialized a)
  have hzb : z = b := Eval.final_unique 0 ((initialize_eval a).seq hz) he
  rw [← hzb]
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val,hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    have hn : j ∉ cachePorts := by
      intro hm
      exact hc (List.mem_map.mpr ⟨j,hm,hj⟩)
    rw [← hj,hlo j,setup_local_frame _ j hn]
    change (initialized a).stacks (lowStack j) = _
    rw [hj, initialized_stacks, ite_eq_right hi]
  · rw [hhi i (by omega), initialized_stacks, ite_eq_right hi]

/-- Full accepted-assignment execution: paid setup and the actual concrete
callback fold produce the specialized original factor product. The return
restores the fixed structural boundary P; prefix storage is bounded separately
by one fixed polynomial budget rather than fed into the next assignment. -/
theorem assignment_eval_correct_oai {a : FactorAssignmentProgram.Data}
    (h : Entry q P M S a) (ids : List ℕ)
    (hids : a.stacks 175 = ProgramEncoding.encodeRecords (records ids))
    (width Z : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width)
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hshape : d * baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z) :
    ∃ (out : Raw n (baseWidth 3 q.p.t) d) (steps : ℕ) (b : FactorAssignmentProgram.Data), NativeSemantics.Good ∅ q.u q.J out ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
        (ids.map (fun f => QueryEvaluation.specializeDense q.u q.J
          (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
          (q.value (a.stacks ∘ lowStack) f))).prod ∧
      steps ≤ assignmentBudget q P S Z ∧
      Eval assignment steps a b ∧
      b.stacks 854 = Product.bytes out ∧ WordBound P b ∧
      (∀ i : Fin 56,
        b.stacks (lowStack (Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i))) =
          IdempotentApplyProgram.Steps.low q.ctx i) ∧
      b.stacks 853 = a.stacks 853 ∧ b.stacks 883 = a.stacks 883 ∧
      b.stacks 884 = a.stacks 884 ∧
      (∀ i, i ∉ entryScratch → i ∉ cachePorts.map lowStack → i ≠ 854 →
        b.stacks i = a.stacks i) ∧
      Trace program (steps + 1) (a.withPC (some program.entry)) (b.withPC none) ∧
      (∀ j z, j ≤ steps + 1 → Trace program j (a.withPC (some program.entry)) z →
        dataBits z ≤ 896 * P + assignmentBudget q P S Z + 1) := by
  obtain ⟨prepared,hprepare,hready,hone,honeval,honedense,hretained,hblank⟩ := h.prepare
  have hpreparedIds : prepared.stacks 175 = ProgramEncoding.encodeRecords (records ids) :=
    (hretained 175 (by decide)).trans hids
  obtain ⟨out,k,b,hout,hvalue,hk,he,hframe,hbound⟩ :=
    prepared_product_eval_correct hready ids hone honeval honedense hpreparedIds hblank
      width Z hwidth hZ hP hbit hshape hhashScale hmarkScale
  have hrun := prepare_product_eval hprepare he
  have htime : prepareCost a + k ≤ assignmentBudget q P S Z := by
    have hp := prepareCost_le a P h.incoming
    unfold assignmentBudget
    omega
  have valueFrame (f : ℕ) : q.value (prepared.stacks ∘ lowStack) f =
      q.value (a.stacks ∘ lowStack) f := by
    have hj (j : ℕ) : Factor.factorJet q.p q.ps q.packing n f j q.theta
        (prepared.stacks ∘ lowStack) = Factor.factorJet q.p q.ps q.packing n f j q.theta
          (a.stacks ∘ lowStack) := by
      apply Factor.factorJet_frame
      all_goals exact hretained _ (by decide)
    unfold Factor.Spec.value Factor.Semantics.hashValue Factor.Semantics.markedValue
    simp_rw [hj]
  have frame (i : Fin 896) (hi : i ∉ entryScratch)
      (hc : i ∉ cachePorts.map lowStack) (h854 : i ≠ 854) : b.stacks i = a.stacks i := by
    rw [hframe,Function.update_of_ne h854]
    exact prepare_stack_frame hprepare i hi hc
  refine ⟨out,prepareCost a+k,b,hout,?_,htime,hrun,?_,hbound,?_,
    frame 853 (by decide) (by decide) (by decide),
    frame 883 (by decide) (by decide) (by decide),
    frame 884 (by decide) (by decide) (by decide),frame,
    compiled_halt_trace hrun 175 854,?_⟩
  · simpa only [hretained 857 (by decide),valueFrame] using hvalue
  · rw [hframe,Function.update_self]
  · intro i
    have hi : lowStack (Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i)) ≠ 854 := by
      intro heq
      have he := congrArg (fun j : Fin 896 => j.val) heq
      have hib := i.isLt
      simp only [lowStack,Factor.nativeStacks,HashCircuitProgram.Native.Memory.lowPort,
        Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at he
      omega
    rw [hframe,Function.update_of_ne hi]
    exact hready.low i
  · intro j z hj hz
    have hg := trace_dataBits program hz
    have ha := StreamResources.dataBits_le_mul (a.withPC (some program.entry)) h.incoming
    change stackBits a.stacks ≤ 896 * P at ha
    change dataBits z ≤ stackBits a.stacks + j at hg
    omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.assignment_eval_correct_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.assignment_eval_correct_oai
