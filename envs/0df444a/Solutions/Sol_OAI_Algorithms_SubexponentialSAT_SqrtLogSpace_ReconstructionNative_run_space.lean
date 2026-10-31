-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:58:49.170642+00:00
-- url     : https://prove2.me/submissions/6a89c3dd-04d1-4304-b126-893b60b4e027

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S179
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_ReconstructionNative_canonical_wide_read
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_ReconstructionSpace_reconstruct_run_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

open BitProgram

theorem readRegs_frame {r : ℕ} (regs : Fin r → Bool) (value present j : Fin r)
    (top : Option Bool) (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present top j = regs j := by
  simp [readRegs, hv, hp]

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete readback/transfer adapter for the marked-query caller. The CRT
result is at261; the exact little-endian integer is delivered at323. The
unread marked-reference stream320 and mass accumulator322 are framed. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

theorem stackMap_injective : Function.Injective stackMap := by decide

theorem afterMove_frame (a : Data) (i : Fin 330) (h1 : i ≠ 261) (h2 : i ≠ 323) (h3 : i ≠ 324) :
    (afterMove a).stacks i = a.stacks i := by
  simp [afterMove, StackRoutines.transferStacks, h1, h2, h3]

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and cleanup facts for the physical CRT count reader. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

theorem finish_output (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) (hs : a.stacks 323 = []) (ht : a.stacks 324 = []) :
    (finish a regs word modulus width).stacks 323 = word := by
  have h323 : (install a ⟨regs, store word modulus [] width⟩).stacks 323 = [] := by
    rw [show (install a ⟨regs, store word modulus [] width⟩).stacks 323 = a.stacks 323 from
      embedState_stack_frame _ _ _ _ _ (by decide)]
    exact hs
  have h324 : (install a ⟨regs, store word modulus [] width⟩).stacks 324 = [] := by
    rw [show (install a ⟨regs, store word modulus [] width⟩).stacks 324 = a.stacks 324 from
      embedState_stack_frame _ _ _ _ _ (by decide)]
    exact ht
  rw [finish, afterMove_output _ h323 h324]
  exact embedState_stack regMap stackMap a _ stackMap_injective 0

theorem finish_register_frame (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) (i : Fin 19) (hi : 8 ≤ i.val) :
    (finish a regs word modulus width).regs i = a.regs i := by
  have h0 : i ≠ 0 := by intro h; subst i; simp at hi
  have h1 : i ≠ 1 := by intro h; subst i; simp at hi
  change (readRegs (install a ⟨regs, store word modulus [] width⟩).regs 0 1 none) i = _
  simp only [readRegs, Function.update_of_ne h1, Function.update_of_ne h0]
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem finish_stack_frame (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) (i : Fin 330)
    (hi : i ∉ ([194, 202, 261, 323, 324, 325, 326, 327, 328, 329] : List (Fin 330))) :
    (finish a regs word modulus width).stacks i = a.stacks i := by
  have h261 : i ≠ 261 := by intro h; subst i; simp at hi
  have h323 : i ≠ 323 := by intro h; subst i; simp at hi
  have h324 : i ≠ 324 := by intro h; subst i; simp at hi
  rw [finish, afterMove_frame _ _ h261 h323 h324]
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  apply hi
  rw [← hj]
  fin_cases j <;> simp [stackMap]

theorem finish_metadata (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) :
    (finish a regs word modulus width).stacks 194 = modulus ∧
    (finish a regs word modulus width).stacks 202 = width := by
  constructor
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 5
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 7

theorem finish_scratch (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) (i : Fin 330)
    (hi : i ∈ ([261, 324, 325, 326, 327, 328, 329] : List (Fin 330))) :
    (finish a regs word modulus width).stacks i = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with h | h | h | h | h | h | h <;> subst i
  · simp [finish, afterMove, StackRoutines.transferStacks]
  · exact afterMove_scratch _
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 1
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 2
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 3
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 4
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 6

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the concrete reader into the shared marked/branch caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

theorem regMap_injective : Function.Injective regMap := Fin.castAdd_injective 19 21
theorem stackMap_injective : Function.Injective stackMap := Fin.castAdd_injective 330 438

theorem register_outside (frame : Data) (a : QueryReadback.Data)
    (i : Fin 40) (hi : 19 ≤ i.val) :
    (install frame a).regs i = frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem stack_outside (frame : Data) (a : QueryReadback.Data)
    (i : Fin 768) (hi : 330 ≤ i.val) :
    (install frame a).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem finished_stack_frame (a : Data) (regs : Fin 8 → Bool)
    (word : List Bool) (i : Fin 768)
    (hi : i ∉ ([194,202,261,323,324,325,326,327,328,329] : List (Fin 768))) :
    (install a (QueryReadback.finish (project a) regs word
      (a.stacks 194) (a.stacks 202))).stacks i = a.stacks i := by
  by_cases hsmall : i.val < 330
  · let j : Fin 330 := ⟨i.val,hsmall⟩
    have heq : stackMap j = i := Fin.ext rfl
    rw [← heq]
    rw [show (install a (QueryReadback.finish (project a) regs word
        (a.stacks 194) (a.stacks 202))).stacks (stackMap j) =
        (QueryReadback.finish (project a) regs word (a.stacks 194) (a.stacks 202)).stacks j from
      embedState_stack regMap stackMap a _ stackMap_injective j]
    rw [QueryReadback.finish_stack_frame]
    · rfl
    · intro hj
      apply hi
      have hm := List.mem_map.mpr ⟨j,hj,heq⟩
      simpa [stackMap] using hm
  · exact stack_outside a _ i (by omega)

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One closed native count-recovery table: Hermite reconstruction over the
computed ring, integer readback, and reclamation of the two CRT entry caches.
Node-jet production and its semantic theorem are composed at the caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem clearCaches_eval (a : Data) :
    Eval clearCaches (2*(a.stacks 5).length+2*(a.stacks 10).length+6) a (cachesCleared a) := by
  let b : Data := ⟨readRegs a.regs 0 1 none,Function.update a.stacks 5 []⟩
  have h1 : Eval (.call (StackRoutines.clearProgram 5 0 1)) (2*(a.stacks 5).length+3) a b := by
    exact Eval.call _ (ListRegisterProgram.clear_run (5 : Fin 768) (0 : Fin 40) 1 a.regs a.stacks)
  have h2 : Eval (.call (StackRoutines.clearProgram 10 0 1)) (2*(b.stacks 10).length+3) b
      ⟨readRegs b.regs 0 1 none,Function.update b.stacks 10 []⟩ := by
    exact Eval.call _ (ListRegisterProgram.clear_run (10 : Fin 768) (0 : Fin 40) 1 b.regs b.stacks)
  convert h1.seq h2 using 1 <;>
    simp [cachesCleared,b,StackRoutines.readRegs_reset] ; omega

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackStore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact wide-store restoration for count readback.  Parser and odometer
registers are preserved even though the reusable narrow ABI includes them. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT BitProgram StructuredCalls

theorem completed_frame (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (i : Fin 768) (hi : i∉changed) : (completed a regs word).stacks i=a.stacks i := by
  by_cases h194 : i=194
  · subst i
    have h := (QueryReadback.finish_metadata (project a) regs word (a.stacks 194) (a.stacks 202)).1
    exact (embedState_stack regMap stackMap a _ stackMap_injective 194).trans h
  by_cases h202 : i=202
  · subst i
    have h := (QueryReadback.finish_metadata (project a) regs word (a.stacks 194) (a.stacks 202)).2
    exact (embedState_stack regMap stackMap a _ stackMap_injective 202).trans h
  apply finished_stack_frame
  simp only [changed,List.mem_cons,List.mem_nil_iff,or_false] at hi ⊢
  tauto

theorem completed_output (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (hs : a.stacks 323=[]) (ht : a.stacks 324=[]) :
    (completed a regs word).stacks 323=word := by
  exact (embedState_stack regMap stackMap a _ stackMap_injective 323).trans
    (QueryReadback.finish_output (project a) regs word (a.stacks 194) (a.stacks 202) hs ht)

theorem completed_scratch (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (i : Fin 768) (hi : i∈([261,324,325,326,327,328,329] : List (Fin 768))) :
    (completed a regs word).stacks i=[] := by
  have localProof (j : Fin 330)
      (hj : j ∈ ([261,324,325,326,327,328,329] : List (Fin 330))) :
      (completed a regs word).stacks (stackMap j) = [] :=
    (embedState_stack regMap stackMap a _ stackMap_injective j).trans
      (QueryReadback.finish_scratch (project a) regs word (a.stacks 194) (a.stacks 202) j hj)
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> subst i
  · exact localProof 261 (by simp)
  · exact localProof 324 (by simp)
  · exact localProof 325 (by simp)
  · exact localProof 326 (by simp)
  · exact localProof 327 (by simp)
  · exact localProof 328 (by simp)
  · exact localProof 329 (by simp)

theorem completed_register_frame (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) : (completed a regs word).regs i=a.regs i := by
  by_cases hsmall : i.val < 19
  · let j : Fin 19 := ⟨i.val,hsmall⟩
    have hji : regMap j=i := Fin.ext rfl
    rw [← hji]
    exact (embedState_register regMap stackMap a _ regMap_injective j).trans
      (QueryReadback.finish_register_frame (project a) regs word (a.stacks 194) (a.stacks 202)
        j hi)
  · exact register_outside a _ i (by omega)

/-- All reader temporaries were blank before the call. Thus only its source
coefficient and output count differ at return. -/
theorem completed_stacks (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (hempty : ∀ i∈([323,324,325,326,327,328,329] : List (Fin 768)), a.stacks i=[]) :
    (completed a regs word).stacks=Function.update (Function.update a.stacks 261 []) 323 word := by
  funext i
  by_cases h261 : i=261
  · subst i
    simp [completed_scratch a regs word 261 (by simp)]
  by_cases h323 : i=323
  · subst i
    simp [completed_output a regs word (hempty 323 (by simp)) (hempty 324 (by simp))]
  by_cases hwork : i∈([324,325,326,327,328,329] : List (Fin 768))
  · rw [completed_scratch a regs word i (by simpa using Or.inr hwork)]
    simp [h261,h323,hempty i (by simpa using Or.inr hwork)]
  · rw [completed_frame a regs word i]
    · simp [h261,h323]
    · simpa [changed,h261,h323] using hwork

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCountCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed count recovery: the native Hermite program, the native first-word
reader, and physical reclamation of the CRT caches. The hypotheses describe
stored data and the polynomial, never an assumed arithmetic execution. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram


theorem crtRegisters_injective : Function.Injective crtRegisters :=
  Fin.castAdd_injective 16 24

theorem crtStacks_injective : Function.Injective crtStacks :=
  Fin.castAdd_injective 320 448

theorem install_stack (frame : Data) (a : SubexpCRTOuterProgram.Data) (i : Fin 320) :
    (install frame a).stacks (crtStacks i) = a.stacks i :=
  embedState_stack crtRegisters crtStacks frame a crtStacks_injective i

theorem install_stack_outside (frame : Data) (a : SubexpCRTOuterProgram.Data)
    (i : Fin 768) (hi : 320 ≤ i.val) :
    (install frame a).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem install_register_outside (frame : Data) (a : SubexpCRTOuterProgram.Data)
    (i : Fin 40) (hi : 16 ≤ i.val) : (install frame a).regs i = frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem install_prepared_stacks (frame : Data) (input : SubexpCRTOuterProgram.Data)
    (rr : Fin 16 → Bool) (word : List Bool) :
    (install frame ⟨rr,Function.update (ReconstructionProgram.Entry.prepared input.stacks) 261 word⟩).stacks =
      Function.update (Function.update (Function.update (install frame input).stacks
        5 (input.stacks 194)) 10 (input.stacks 202)) 261 word := by
  simp only [install,embedState,ReconstructionProgram.Entry.prepared,
    ProgramLinking.extend_update crtStacks_injective] ; rfl

theorem cachesCleared_register_frame (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (cachesCleared a).regs i = a.regs i := by
  apply StackRoutines.readRegs_frame
  · intro h; subst i; simp at hi
  · intro h; subst i; simp at hi

/-- The CRT coefficient is consumed, and the two copied entry caches are
reclaimed. All three were empty in the ready caller, so only the count changes. -/
theorem readback_cleanup_stacks (entry middle : Data) (rr : Fin 8 → Bool)
    (word modulus width coeff : List Bool)
    (hmid : middle.stacks = Function.update (Function.update (Function.update
      entry.stacks 5 modulus) 10 width) 261 coeff)
    (h5 : entry.stacks 5 = []) (h10 : entry.stacks 10 = [])
    (h261 : entry.stacks 261 = [])
    (hempty : ∀ i∈([323,324,325,326,327,328,329] : List (Fin 768)), middle.stacks i=[]) :
    (cachesCleared (QueryReadback.Wide.completed middle rr word)).stacks =
      Function.update entry.stacks 323 word := by
  change Function.update (Function.update (QueryReadback.Wide.completed middle rr word).stacks
    5 []) 10 [] = _
  rw [QueryReadback.Wide.completed_stacks middle rr word hempty,hmid]
  funext i
  by_cases h323 : i=323
  · subst i; simp
  by_cases hi5 : i=5
  · subst i; simp [h5]
  by_cases hi10 : i=10
  · subst i; simp [h10]
  by_cases hi261 : i=261
  · subst i; simp [h261]
  simp [h323,hi5,hi10,hi261]

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One concrete lower-workspace recovery tail: native Hermite reconstruction,
canonical complete binary readback, and paid cache reclamation. All retained
caller stacks enter its local prefix bound; the endpoint changes only count323.
The physical jet and semantic target hypotheses must be produced by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram
open LeafProgram.Count

/-- Complete canonical recovery on one actual trace. This is an internal
composition theorem: its stored jets and target correctness are not final
algorithmic premises, and must be discharged by the streaming query producer. -/
theorem run_space_oai (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → ReconstructionProgram.Native.Coeff t d)
    (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : ReconstructionProgram.Native.Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (polyFrame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input) scalarWidth polyFrame)
    (hclean : ∀ j ∈ ReconstructionProgram.NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t)
    (hdistinct : Function.Injective (fun i => a.rho t ht
      ((RingProgram.modelRing t ht hd a M cache).decode (nodes i))))
    (target : Polynomial (a.O t)) (hdegree : target.natDegree < Q*J)
    (htargetJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd a M cache)
      nodes J (fun i => (jets i).1) target)
    (count m n : ℕ) (hcount : count ≤ m*2^n) (hlarge : m*2^n < 3^t)
    (htarget : target.eval 0 = (count : a.O t))
    (S : ℕ) (hQsize : Q ≤ S) (hJsize : J ≤ S) (htsize : t ≤ S)
    (hdsize : d ≤ S) (hqsize : 3^d ≤ S)
    (hmodsize : (input.stacks 194).length ≤ S)
    (hwidthsize : (input.stacks 202).length ≤ S)
    (frame : Data)
    (hm : BinaryArithmetic.toNat (input.stacks 194) = 3^t)
    (hw : (input.stacks 202).length = baseWidth 3 t)
    (hreader : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), frame.stacks i = []) :
    ∃ steps out, steps+1 ≤ budget S ∧
      Eval command steps (install frame input) out ∧
      Trace program (steps+1) ((install frame input).withPC (some program.entry))
        (out.withPC none) ∧
      out.stacks = Function.update (install frame input).stacks 323
        (DisjointReuse.binaryNat count) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = (install frame input).regs i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
        Trace program prefixSteps ((install frame input).withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits (install frame input).stacks + budget S := by
  obtain ⟨b,rf,nr,hnr,hr,hb,_,_⟩ :=
    ReconstructionSpace.reconstruct_run_space t ht hd a M cache hcanon hzbits J hJpos hB
      nodes jets minusOne hminus input hscalar scalarWidth polyFrame hpoly hclean
      hzero hone hneg hJ hnodes hjets hexponent hprecision hdistinct target hdegree htargetJets
      S hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize count m n hcount hlarge htarget
  let localOut : SubexpCRTOuterProgram.Data :=
    ⟨rf,Function.update (ReconstructionProgram.Entry.prepared input.stacks) 261 (RingProgram.flat b)⟩
  let middle := install frame localOut
  have hre : Eval LeafProgram.Count.reconstruct nr (install frame input) middle :=
    eval_call_lifted ReconstructionProgram.Native.program crtRegisters crtStacks frame
      crtRegisters_injective crtStacks_injective hr
  have hs (i : Fin 320) : middle.stacks (crtStacks i) = localOut.stacks i :=
    install_stack frame localOut i
  have h194 : middle.stacks 194 = input.stacks 194 := by
    rw [show (194 : Fin 768) = crtStacks 194 from rfl,hs]
    simp [localOut,ReconstructionProgram.Entry.prepared]
  have h202 : middle.stacks 202 = input.stacks 202 := by
    rw [show (202 : Fin 768) = crtStacks 202 from rfl,hs]
    simp [localOut,ReconstructionProgram.Entry.prepared]
  have h5 : middle.stacks 5 = input.stacks 194 := by
    rw [show (5 : Fin 768) = crtStacks 5 from rfl,hs]
    simp [localOut,ReconstructionProgram.Entry.prepared]
  have h10 : middle.stacks 10 = input.stacks 202 := by
    rw [show (10 : Fin 768) = crtStacks 10 from rfl,hs]
    simp [localOut,ReconstructionProgram.Entry.prepared]
  have hv : middle.stacks 261 = RingProgram.flat b := by
    rw [show (261 : Fin 768) = crtStacks 261 from rfl,hs]
    simp [localOut]
  have he : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), middle.stacks i = [] := by
    intro i hi
    rw [install_stack_outside frame localOut i]
    · exact hreader i hi
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with h|h|h|h|h|h|h <;> subst i <;> decide
  have hmod : (middle.stacks 194).length ≤ 2*(S+1)^2 := by
    rw [h194]
    nlinarith only [hmodsize]
  have hbase : baseWidth 3 t ≤ 2*(S+1)^2 := by
    rw [RingProgram.ternary_baseWidth]
    nlinarith only [htsize]
  have hflat : (RingProgram.flat b).length ≤ 2*(S+1)^2 := by
    rw [RingProgram.flat_length,RingProgram.ternary_baseWidth]
    have hprod := Nat.mul_le_mul hdsize htsize
    nlinarith only [hprod]
  obtain ⟨nk,rr,hnk,her⟩ := canonical_wide_read t ht hd a M cache b count
    (hcount.trans_lt hlarge) hb middle hv (by simpa only [h194] using hm)
      (by simpa only [h202] using hw) he (2*(S+1)^2) hbase hmod hflat
  let afterRead := LeafProgram.QueryReadback.Wide.completed middle rr (DisjointReuse.binaryNat count)
  have hf5 : afterRead.stacks 5 = input.stacks 194 := by
    rw [LeafProgram.QueryReadback.Wide.completed_frame middle rr _ 5 (by decide),h5]
  have hf10 : afterRead.stacks 10 = input.stacks 202 := by
    rw [LeafProgram.QueryReadback.Wide.completed_frame middle rr _ 10 (by decide),h10]
  let nc := 2*(afterRead.stacks 5).length+2*(afterRead.stacks 10).length+6
  have hcost : nr+(nk+nc)+1 ≤ budget S := by
    dsimp only [nc]
    rw [hf5,hf10]
    unfold budget
    omega
  have heval : Eval command (nr+(nk+nc)) (install frame input) (cachesCleared afterRead) :=
    hre.seq (her.seq (clearCaches_eval afterRead))
  have hstart (j : Fin 320) : (install frame input).stacks (crtStacks j) = input.stacks j :=
    install_stack frame input j
  have hstart5 : (install frame input).stacks 5 = [] :=
    (hstart 5).trans (hclean 5 (by decide))
  have hstart10 : (install frame input).stacks 10 = [] :=
    (hstart 10).trans (hclean 10 (by decide))
  have hstart261 : (install frame input).stacks 261 = [] :=
    (hstart 261).trans (hclean 261 (by decide))
  have hmiddle : middle.stacks = Function.update (Function.update (Function.update
      (install frame input).stacks 5 (input.stacks 194)) 10 (input.stacks 202)) 261 (RingProgram.flat b) :=
    install_prepared_stacks frame input rf (RingProgram.flat b)
  have hstore := readback_cleanup_stacks (install frame input) middle rr (DisjointReuse.binaryNat count)
    (input.stacks 194) (input.stacks 202) (RingProgram.flat b) hmiddle hstart5 hstart10 hstart261 he
  refine ⟨nr+(nk+nc),cachesCleared afterRead,hcost,heval,compiled_halt_trace heval 256 323,hstore,?_,?_⟩
  · intro i hi
    rw [cachesCleared_register_frame afterRead i (by omega)]
    rw [LeafProgram.QueryReadback.Wide.completed_register_frame middle rr _ i (by omega)]
    exact (install_register_outside frame localOut i hi).trans
      (install_register_outside frame input i hi).symm
  · intro prefixSteps intermediate hprefix hp
    exact StructuredSpace.local_stack_bound program (steps := budget S) (by rfl)
      prefixSteps intermediate (hprefix.trans hcost) hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.run_space_oai
