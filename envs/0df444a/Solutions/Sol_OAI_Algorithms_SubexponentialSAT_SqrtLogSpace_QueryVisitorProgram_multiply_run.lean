-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:33:17.113374+00:00
-- url     : https://prove2.me/submissions/c8b826ff-dd06-4e26-a6b4-89450a73736f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorProductSpace_accumulate_run_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorFrames_tupleMultiply_not_mem_writes
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram_product_dense

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLogic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured verification rules for fixed bit programs

Every execution judgment below contains actual transitions of one fixed step
function. Loop iterations may be controlled by unbounded data; neither the
transition function nor its finite control changes with the iteration count.
No judgment assigns a cost to an unimplemented mathematical function.
-/

namespace SubexponentialSAT.ProgramLogic

open SubexponentialSAT.Computation
open scoped BigOperators

section Traces

variable {Cfg : Type} {step : Cfg → Option Cfg}

/-- A frame observation preserved by each actual step is preserved by the run. -/
theorem frame_trace {Frame : Type} (frame : Cfg → Frame)
    (preserve : ∀ a b, step a = some b → frame b = frame a)
    {steps : ℕ} {a b : Cfg} (h : Trace step steps a b) : frame b = frame a := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans (preserve _ _ hs)

end Traces

section BitPrograms

open SubexponentialSAT.BitProgram

variable {r s l : ℕ}

theorem execInstr_register_frame (instr : Instr r s l) (c : Cfg r s l) (k : Fin r)
    (hk : k ∉ registerWrites instr) : (execInstr instr c).regs k = c.regs k := by
  cases instr <;> simp_all [registerWrites, execInstr, readRegs]

theorem step_register_frame (p : Program r s l) {a b : Cfg r s l} (k : Fin r)
    (safe : ∀ label, a.pc = some label → k ∉ registerWrites (p.code label))
    (hs : step p a = some b) : b.regs k = a.regs k := by
  cases hp : a.pc with
  | none => simp [step, hp] at hs
  | some label =>
      have heq : execInstr (p.code label) a = b := by simpa [step, hp] using hs
      subst b
      exact execInstr_register_frame _ _ _ (safe label hp)

end BitPrograms

end SubexponentialSAT.ProgramLogic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandRegisterFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Register frames derived from the actual finite instruction tables and
structured command syntax. These footprints describe code, not an assumed
semantic behavior of a callback. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

open OAI BitProgram ProgramLogic

theorem trace_register_frame {r s l : ℕ} (p : Program r s l)
    {steps : ℕ} {a b : Cfg r s l} (ht : Trace p steps a b)
    (i : Fin r) (hi : i ∉ programWrites p) : b.regs i = a.regs i := by
  apply ProgramLogic.frame_trace (fun c : Cfg r s l => c.regs i) ?_ ht
  intro a b hs
  exact step_register_frame p i (fun label _ => (not_mem_programWrites p i).mp hi label) hs

theorem base_eval_register_frame {r s : ℕ} {c : StructuredProgram.Cmd r s}
    {steps : ℕ} {a b : StructuredProgram.State r s}
    (ht : StructuredProgram.Eval c steps a b) (i : Fin r)
    (hi : i ∉ baseWrites c) : b.regs i = a.regs i := by
  induction ht with
  | skip => rfl
  | atom atom a => exact execInstr_register_frame (atom.instr (0 : Fin 1)) (a.withPC none) i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ baseWrites first ∧ i ∉ baseWrites second := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Every actual execution preserves each register outside the static writes. -/
theorem eval_register_frame {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (ht : StructuredCalls.Eval c steps a b) (i : Fin r)
    (hi : i ∉ writes c) : b.regs i = a.regs i := by
  induction ht with
  | base he => exact base_eval_register_frame he i hi
  | call p ht => exact trace_register_frame p ht i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ writes first ∧ i ∉ writes second := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

theorem insertCode_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (Dictionary.insertCode p t M cache k x seed)).Nodup := by
  unfold Dictionary.insertCode
  have heq : Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed) =
      (Squarefree.Sparse.keys seed).filter (fun j => decide (j ≠ k)) := by
    clear hn
    induction seed with
    | nil => rfl
    | cons a seed ih =>
      by_cases h : a.1=k <;> simpa [Squarefree.Sparse.erase,Squarefree.Sparse.keys,h] using ih
  have he : (Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed)).Nodup := by
    rw [heq]
    exact hn.filter _
  have hnot : k ∉ Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed) := by
    rw [heq]
    simp
  simp only [Squarefree.Sparse.keys,List.map_cons,List.map_reverse]
  exact List.nodup_cons.mpr ⟨by simpa [Squarefree.Sparse.keys] using hnot,
    by simpa [Squarefree.Sparse.keys] using he⟩

theorem run_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (run p t M cache source seed)).Nodup := by
  induction source generalizing seed with
  | nil => exact hn
  | cons a source ih => exact ih _ (insertCode_nodup p t M cache a.1 a.2 seed hn)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Index

variable {V : Type*} [DecidableEq V]

theorem Valid.join {a b : Index V} (ha : a.Valid) (hb : b.Valid) : (a.join b).Valid :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)

end Index

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEnvironment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The seven fixed persistent cache words are physically copied into the
native arithmetic environment. Cleanup clears those seven copies; both
commands frame all other stacks, including the query buffers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment

open OAI BitProgram StructuredCalls
open SubexpSetupStorage SqrtLog.MomentsProgram

theorem pairs_valid : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ p.1 ≠ 159 ∧ (159 : Fin 896) ≠ p.2 := by
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem bootstrap_eval (a : Data) (htmp : a.stacks 159 = []) :
    Eval bootstrap (bootstrapCost a) a (bootstrapResult a) := by
  have he := copyMany_eval 159 pairs (projectState registerMap id a) pairs_valid htmp
  exact eval_liftCommand_from_state bootstrap16 194 5 registerMap id a
    (Fin.castAdd_injective 16 24) Function.injective_id he

private theorem embed_identity_stacks (a : Data) (b : State 16 896) :
    (embedState registerMap id a b).stacks = b.stacks := by
  funext i
  exact Function.injective_id.extend_apply b.stacks a.stacks i

theorem bootstrap_stacks (a : Data) :
    (bootstrapResult a).stacks =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update a.stacks 5 (a.stacks 194 ++ a.stacks 5))
          12 (a.stacks 202 ++ a.stacks 12)) 17 (a.stacks 203 ++ a.stacks 17))
          22 (a.stacks 201 ++ a.stacks 22)) 39 (a.stacks 204 ++ a.stacks 39))
          45 (a.stacks 212 ++ a.stacks 45)) 46 (a.stacks 243 ++ a.stacks 46) := by
  funext i
  rw [bootstrapResult, embed_identity_stacks]
  simp only [pairs, copyManyState, copyState, StackRoutines.copyStacks, projectState,
    Function.comp_apply, id_eq, Function.update_of_ne (by decide : (202 : Fin 896) ≠ 5),
    Function.update_of_ne (by decide : (12 : Fin 896) ≠ 5)]
  simp

theorem bootstrap_frame (a : Data) (i : Fin 896) (hi : i ∉ environmentPorts) :
    (bootstrapResult a).stacks i = a.stacks i := by
  rw [bootstrapResult, embed_identity_stacks]
  apply copyMany_frame
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  simp only [environmentPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hi
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only; tauto

theorem bootstrap_low (a : Data) (hempty : ∀ i, a.stacks (lowPort i) = []) :
    ∀ i, (bootstrapResult a).stacks (lowPort i) =
      Product.tapes (Product.idle (a.stacks 194) (a.stacks 202) (a.stacks 203)
        (a.stacks 201) (a.stacks 204) (a.stacks 212) (a.stacks 243)) i := by
  have h5 : a.stacks 5 = [] := hempty 5
  have h12 : a.stacks 12 = [] := hempty 12
  have h17 : a.stacks 17 = [] := hempty 17
  have h22 : a.stacks 22 = [] := hempty 22
  have h39 : a.stacks 39 = [] := hempty 39
  have h45 : a.stacks 45 = [] := hempty 45
  have h46 : a.stacks 46 = [] := hempty 46
  intro i
  have hi := hempty i
  clear hempty
  rw [bootstrap_stacks]
  fin_cases i <;> simp_all [lowPort, Product.tapes, Product.idle]

private theorem word_le_total (a : Data) (i : Fin 896) :
    (a.stacks i).length ≤ stackBits a.stacks :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((a.stacks j).length)) (Finset.mem_univ i)

theorem bootstrapCost_le (a : Data) : bootstrapCost a ≤ 49 * stackBits a.stacks + 36 := by
  have h194 := word_le_total a 194
  have h202 := word_le_total a 202
  have h203 := word_le_total a 203
  have h201 := word_le_total a 201
  have h204 := word_le_total a 204
  have h212 := word_le_total a 212
  have h243 := word_le_total a 243
  simp [bootstrapCost, pairs, copyManyCost, copyState, StackRoutines.copyStacks, projectState]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem run_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (left right seed : List (Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (run p t M cache table u J left right seed)).Nodup := by
  induction left generalizing seed with
  | nil => exact hn
  | cons a left ih =>
    exact ih _ (Normalize.run_nodup p t M cache _ seed hn)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramValidity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

namespace Normalize
variable {K : Type*} [DecidableEq K]

theorem insertCode_preserves_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (P : K → Prop) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hk : P k) (hs : ∀ a ∈ seed, P a.1) :
    ∀ a ∈ Dictionary.insertCode p t M cache k x seed, P a.1 := by
  intro a ha
  simp only [Dictionary.insertCode,List.mem_cons,List.mem_reverse] at ha
  rcases ha with rfl|ha
  · exact hk
  · exact hs a (List.mem_filter.mp ha).1

theorem run_preserves_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (P : K → Prop)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hs : ∀ a ∈ source, P a.1) (hi : ∀ a ∈ seed, P a.1) :
    ∀ a ∈ run p t M cache source seed, P a.1 := by
  induction source generalizing seed with
  | nil => exact hi
  | cons a source ih =>
    apply ih _ (fun b hb => hs b (by simp [hb]))
    exact insertCode_preserves_keys p t M cache P a.1 a.2 seed (hs a (by simp)) hi
end Normalize

namespace Product

theorem keptJoin_valid {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (a : Squarefree.Index (Fin n)) (entries : List (Entry n B d))
    (ha : a.Valid ∧ a.vars ⊆ vars) (he : ∀ b ∈ entries, ValidKey vars u J b.1) :
    ∀ b ∈ keptJoin a u J entries, ValidKey vars u J b.1 := by
  induction entries with
  | nil => intro b hb; simp [keptJoin] at hb
  | cons b entries ih =>
    intro c hc
    have hb := he b (by simp)
    have ht := ih (fun c hc => he c (by simp [hc]))
    by_cases h : (a.join b.1).Kept u J
    · simp only [keptJoin,h,ite_true, if_true,List.mem_cons] at hc
      rcases hc with rfl|hc
      · exact ⟨h,ha.1.join hb.2.1,Finset.union_subset ha.2 hb.2.2⟩
      · exact ht c hc
    · simp only [keptJoin,h,ite_false] at hc
      exact ht c hc

theorem block_valid (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d))
    (ha : ValidKey vars u J a.1) (hr : ∀ b ∈ right, ValidKey vars u J b.1) :
    ∀ b ∈ block p t M cache table u J a right, ValidKey vars u J b.1 := by
  intro b hb
  have h := keptJoin_valid vars u J a.1
    (Squarefree.ScaleProgram.scaled p t M cache table a.2 right) ha.2
    (by intro c hc; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc; exact hr e he)
  exact h b (by simpa [block] using hb)

theorem run_valid (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ)
    (left right seed : List (Entry n (baseWidth p t) d))
    (hl : ∀ a ∈ left, ValidKey vars u J a.1)
    (hr : ∀ b ∈ right, ValidKey vars u J b.1) (hi : ∀ b ∈ seed, ValidKey vars u J b.1) :
    ∀ b ∈ run p t M cache table u J left right seed, ValidKey vars u J b.1 := by
  induction left generalizing seed with
  | nil => exact hi
  | cons a left ih =>
    apply ih _ (fun b hb => hl b (by simp [hb]))
    exact Normalize.run_preserves_keys p t M cache (ValidKey vars u J) _ seed
      (block_valid p t M cache table vars u J a right (hl a (by simp)) hr) hi

end Product
end SubexponentialSAT.SqrtLog.MomentsProgram

end OAI.Algorithms
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
section NativeValidity

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (vars : Finset (Fin n)) (u J : ℕ)

theorem product_good (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good vars u J left) (hr : Good vars u J right) :
    Good vars u J (Product.run p t M cache table u J left right []) :=
  ⟨Product.run_valid p t M cache table vars u J left right [] hl.valid hr.valid (by simp),
    Product.run_nodup p t M cache table u J left right [] (by simp [Squarefree.Sparse.keys])⟩


end NativeValidity

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem clearOne_eval (i : Fin 896) (a : Data) :
    Eval (clearOne i) (2 * (a.stacks i).length + 3) a (cleared i a) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 a.regs a.stacks)

theorem clearMany_eval (ps : List (Fin 896)) (a : Data) :
    Eval (clearMany ps) (clearCost ps a) a (clearedMany ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih => exact (clearOne_eval p a).seq (ih _)

theorem clearCost_le (ps : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : clearCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearCost]
  | cons p ps ih =>
      have hb : ∀ i, ((cleared p a).stacks i).length ≤ B := by
        intro i
        by_cases hi : i = p
        · subst i; simp [cleared]
        · simpa [cleared, hi] using ha i
      have ht := ih (cleared p a) hb
      have hp := ha p
      simp only [clearCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAssembler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem low_mem (i : Fin 896) :
    i∈(List.finRange 56).map (Fin.castAdd 840) ↔ i.val<56 := by
  constructor
  · intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  · intro h
    exact List.mem_map.mpr ⟨⟨i.val,h⟩,List.mem_finRange _,Fin.ext rfl⟩

private theorem normalize_mem (i : Fin 896) :
    i∈(List.finRange 28).map (fun j => (⟨100+j.val,by omega⟩ : Fin 896)) ↔
      100 ≤ i.val ∧ i.val<128 := by
  constructor
  · intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change 100+j.val=i.val at hv
    omega
  · intro h
    refine List.mem_map.mpr ⟨⟨i.val-100,by omega⟩,List.mem_finRange _,?_⟩
    apply Fin.ext
    dsimp
    omega

theorem pairScratch_mem (i : Fin 896) : i∈pairScratch ↔
    i.val<56 ∨ (100 ≤ i.val ∧ i.val<128) ∨ i=159 ∨ i=841 ∨ i=848 ∨ i=849 := by
  simp [pairScratch,low_mem,normalize_mem]

theorem clearPair_eval (a : Data) : Eval clearPair (clearPairCost a) a (clearPairState a) :=
  eval_liftCommand_from_state _ 0 0 FactorEnvironment.registerMap id a
    (Fin.castAdd_injective 16 24) Function.injective_id
    (SubexpSetupStorage.clearMany_eval pairScratch _)

theorem clearPair_stacks (a : Data) (i : Fin 896) :
    (clearPairState a).stacks i = if i∈pairScratch then [] else a.stacks i := by
  unfold clearPairState
  rw [show (embedState FactorEnvironment.registerMap id a
    (SubexpSetupStorage.clearManyState pairScratch
      (projectState FactorEnvironment.registerMap id a))).stacks i =
    (SubexpSetupStorage.clearManyState pairScratch
      (projectState FactorEnvironment.registerMap id a)).stacks i from
        embedState_stack FactorEnvironment.registerMap id a _ Function.injective_id i]
  rw [SubexpSetupStorage.clearMany_stacks]
  rfl

theorem clearPair_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((clearPairState a).stacks i).length≤ B := by
  intro i
  rw [clearPair_stacks]
  split
  · exact Nat.zero_le _
  · exact hb i

theorem clearPair_low (a : Data) (i : Fin 56) :
    (clearPairState a).stacks (FactorEnvironment.lowPort i) = [] := by
  rw [clearPair_stacks,ite_eq_left]
  rw [pairScratch_mem]
  exact Or.inl i.isLt

private theorem bootstrapPair_bound (a : Data) (B : ℕ)
    (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((FactorEnvironment.bootstrapResult (clearPairState a)).stacks i).length≤ B := by
  intro i
  by_cases hi : i∈FactorEnvironment.environmentPorts
  · simp only [FactorEnvironment.environmentPorts,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [FactorEnvironment.bootstrap_stacks]
    all_goals simp [clearPair_stacks,pairScratch_mem]
    all_goals exact hb _
  · rw [FactorEnvironment.bootstrap_frame _ _ hi]
    exact clearPair_bound a B hb i

theorem clearPairCost_le (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    clearPairCost a ≤ 176*B+265 := by
  have h := SubexpSetupStorage.clearManyCost_le pairScratch
    (projectState FactorEnvironment.registerMap id a) B hb
  have hl : pairScratch.length=88 := by simp [pairScratch]
  rw [hl] at h
  unfold clearPairCost
  omega

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/
namespace TupleMultiply

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram

theorem ports_injective : Function.Injective ports := by
  have small (i : Fin 768) (h67 : i≠67) (h151 : i≠151) : (ports i).val<768 := by
    simpa only [ports,h67,h151,ite_false,Fin.val_castAdd] using i.isLt
  intro i j hij
  by_cases hi67 : i=67
  · subst i
    by_cases hj67 : j=67
    · exact hj67.symm
    by_cases hj151 : j=151
    · subst j
      exact False.elim ((by decide : (853 : Fin 896)≠852) hij)
    have hj := small j hj67 hj151
    have hv := congrArg Fin.val hij
    change 853=(ports j).val at hv
    omega
  by_cases hi151 : i=151
  · subst i
    by_cases hj67 : j=67
    · subst j
      exact False.elim ((by decide : (852 : Fin 896)≠853) hij)
    by_cases hj151 : j=151
    · exact hj151.symm
    have hj := small j hj67 hj151
    have hv := congrArg Fin.val hij
    change 852=(ports j).val at hv
    omega
  have hi := small i hi67 hi151
  by_cases hj67 : j=67
  · subst j
    have hv := congrArg Fin.val hij
    change (ports i).val=853 at hv
    omega
  by_cases hj151 : j=151
  · subst j
    have hv := congrArg Fin.val hij
    change (ports i).val=852 at hv
    omega
  simp only [ports,hi67,hi151,hj67,hj151,ite_false] at hij
  exact Fin.castAdd_injective 768 128 hij

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) := by
  have ht : (clearPairState (raw a)).stacks 159=[] := by
    rw [clearPair_stacks,ite_eq_left (by decide : (159 : Fin 896)∈pairScratch)]
  have he := (NodeReadoutSpace.clearMany_eval [61,70] a).seq
    ((clearPair_eval (raw a)).seq (FactorEnvironment.bootstrap_eval _ ht))
  exact he

theorem prepared_low (a : Data) (i : Fin 56) :
    (prepared a).stacks (FactorEnvironment.lowPort i)=Product.tapes (environment a) i := by
  have h := FactorEnvironment.bootstrap_low (clearPairState (raw a)) (clearPair_low (raw a)) i
  simpa [prepared,environment,clearPair_stacks,pairScratch_mem,raw,
    NodeReadoutSpace.clearedMany_stack] using h

theorem ports_low (i : Fin 56) :
    ports (Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i))=
      FactorEnvironment.lowPort i := by
  have h67 : Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i)≠67 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=67 at hv
    omega
  have h151 : Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i)≠151 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=151 at hv
    omega
  simp only [ports,h67,h151,ite_false]
  rfl

theorem prepared_ready (a : Data) :
    Factor.lowReady (projectState id ports (prepared a)) (environment a) := by
  intro i
  change (prepared a).stacks (ports (Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i)))=_
  rw [ports_low]
  exact prepared_low a i

theorem prepared_scratch (a : Data) :
    (prepared a).stacks 61=[] ∧ (prepared a).stacks 70=[] ∧ (prepared a).stacks 159=[] := by
  simp [prepared,FactorEnvironment.bootstrap_stacks,clearPair_stacks,pairScratch_mem,
    raw,NodeReadoutSpace.clearedMany_stack]

theorem prepared_frame (a : Data) (i : Fin 896)
    (hp : i∉pairScratch) (h61 : i≠61) (h70 : i≠70) :
    (prepared a).stacks i=a.stacks i := by
  have he : i∉FactorEnvironment.environmentPorts := by
    intro hi
    simp only [FactorEnvironment.environmentPorts,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hp (by decide)
  rw [prepared,FactorEnvironment.bootstrap_frame _ i he,clearPair_stacks,ite_eq_right hp,
    raw,NodeReadoutSpace.clearedMany_stack,ite_eq_right (by simp [h61,h70])]

theorem raw_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length ≤ B) :
    ∀ i,((raw a).stacks i).length ≤ B := by
  intro i
  rw [raw,NodeReadoutSpace.clearedMany_stack]
  split
  · exact Nat.zero_le _
  · exact hb i

theorem prepared_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length ≤ B) :
    ∀ i,((prepared a).stacks i).length ≤ B :=
  bootstrapPair_bound (raw a) B (raw_bound a B hb)

theorem multiply_eval (a : Data) (b : Factor.Data) (steps : ℕ)
    (he : Eval Factor.accumulate steps (projectState id ports a) b) :
    Eval multiply (steps+1) a (productState a b) :=
  eval_liftCommand_from_state _ 67 151 id ports a Function.injective_id ports_injective he

theorem productState_stacks (a : Data) (b : Factor.Data) (word : List Bool)
    (hb : b.stacks=Function.update (Function.update (projectState id ports a).stacks 67 []) 151 word) :
    (productState a b).stacks=Function.update (Function.update a.stacks 853 []) 852 word := by
  funext i
  by_cases hi : ∃ j,ports j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [productState,embedState_stack id ports a b ports_injective j,hb]
    by_cases h67 : j=67
    · subst j
      simp [ports]
    by_cases h151 : j=151
    · subst j
      simp [ports]
    have h853 : ports j≠853 := by
      intro h
      have : ports j=ports 67 := h
      exact h67 (ports_injective this)
    have h852 : ports j≠852 := by
      intro h
      have : ports j=ports 151 := h
      exact h151 (ports_injective this)
    simp [h67,h151,h853,h852,projectState]
  · have h853 : i≠853 := by intro h; subst i; exact hi ⟨67,rfl⟩
    have h852 : i≠852 := by intro h; subst i; exact hi ⟨151,rfl⟩
    rw [productState,embedState_stack_frame id ports a b i hi]
    simp [h853,h852]

theorem prepareCost_le (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length ≤ B) :
    prepareCost a ≤ 50000*(B+1) := by
  have hc := NodeReadoutSpace.clearCost_le [61,70] a B hb
  have hp := clearPairCost_le (raw a) B (raw_bound a B hb)
  have hs : stackBits (clearPairState (raw a)).stacks ≤ 896*B :=
    StreamResources.dataBits_le_mul ((clearPairState (raw a)).withPC (none : Option (Fin 1)))
      (clearPair_bound (raw a) B (raw_bound a B hb))
  have ht := FactorEnvironment.bootstrapCost_le (clearPairState (raw a))
  simp only [List.length_cons,List.length_nil] at hc
  unfold prepareCost
  omega

theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (seed head : List (Product.Entry n (baseWidth p t) d))
    (hs : Good ∅ u J seed) (hh : Good ∅ u J head) (a : Data) (B : ℕ)
    (henv : environment a=Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true))
    (hseed : a.stacks 852=Product.bytes seed) (hhead : a.stacks 853=Product.bytes head)
    (hb : ∀ i,(a.stacks i).length ≤ B)
    (hcapacity : FactorProductSpace.byteBound n (baseWidth p t) d u J ≤ B) :
    let result := Product.run p t M cache table u J seed head []
    ∃ steps b, Eval command steps a b ∧ Good ∅ u J result ∧
      b.stacks 852=Product.bytes result ∧ b.stacks 853=[] ∧
      (∀ i,i∉pairScratch → i≠61 → i≠70 → i≠852 → i≠853 → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length ≤ B) ∧
      steps+1 ≤ 51000*(B+1)+FactorProductSpace.budget n (baseWidth p t) d u J ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (b.withPC none) ∧
      ∀ q z,q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i,(z.stacks i).length ≤ 896*B+51000*(B+1)+
          FactorProductSpace.budget n (baseWidth p t) d u J := by
  dsimp only
  let c := prepared a
  have hlo := prepared_ready a
  rw [henv] at hlo
  have hseed' : (projectState id ports c).stacks 151=Product.bytes seed := by
    change c.stacks 852=Product.bytes seed
    rw [prepared_frame a 852 (by decide) (by decide) (by decide)]
    exact hseed
  have hhead' : (projectState id ports c).stacks 67=Product.bytes head := by
    change c.stacks 853=Product.bytes head
    rw [prepared_frame a 853 (by decide) (by decide) (by decide)]
    exact hhead
  have h61 : (projectState id ports c).stacks 61=[] := (prepared_scratch a).1
  have h70 : (projectState id ports c).stacks 70=[] := (prepared_scratch a).2.1
  have h159 : (projectState id ports c).stacks 159=[] := (prepared_scratch a).2.2
  obtain ⟨nt,b,hnt,hgood,he,hbstacks,hbytes,_,_⟩ :=
    FactorProductSpace.accumulate_run_space p t M cache hz table degree width hd hw u J
      seed head hs hh (projectState id ports c) hlo hseed' hhead' h61 h70 h159
  let r := productState c b
  have hr : r.stacks=Function.update (Function.update c.stacks 853 []) 852
      (Product.bytes (Product.run p t M cache table u J seed head [])) :=
    productState_stacks c b _ hbstacks
  have hrbound : ∀ i,(r.stacks i).length ≤ B := by
    intro i
    rw [hr]
    by_cases hi : i=852
    · subst i
      simpa using hbytes.trans hcapacity
    by_cases hi' : i=853
    · subst i
      simp
    simpa [Function.update_of_ne hi,Function.update_of_ne hi'] using prepared_bound a B hb i
  have hrun : Eval command (prepareCost a+((nt+1)+clearPairCost r)) a (clearPairState r) :=
    (prepare_eval a).seq ((multiply_eval c b nt he).seq (clearPair_eval r))
  have ht : prepareCost a+((nt+1)+clearPairCost r)+1 ≤
      51000*(B+1)+FactorProductSpace.budget n (baseWidth p t) d u J := by
    have hp := prepareCost_le a B hb
    have hc := clearPairCost_le r B hrbound
    omega
  refine ⟨_,clearPairState r,hrun,hgood,?_,?_,?_,clearPair_bound r B hrbound,ht,
    compiled_halt_trace hrun 853 852,?_⟩
  · rw [clearPair_stacks,ite_eq_right (by decide : (852 : Fin 896)∉pairScratch),hr]
    simp
  · rw [clearPair_stacks,ite_eq_right (by decide : (853 : Fin 896)∉pairScratch),hr]
    simp
  · intro i hi h61i h70i h852i h853i
    rw [clearPair_stacks,ite_eq_right hi,hr,Function.update_of_ne h852i,
      Function.update_of_ne h853i]
    exact prepared_frame a i hi h61i h70i
  · intro q z hq hz' i
    have hentry : dataBits (a.withPC (some program.entry)) ≤ 896*B :=
      StreamResources.dataBits_le_mul _ hb
    have hlocal := StructuredSpace.local_stack_bound program hentry q z (hq.trans ht) hz' i
    simpa only [Nat.add_assoc] using hlocal

end TupleMultiply

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

theorem PrefixBound.mono {command : Code} {steps B D : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hBD : B ≤ D) :
    PrefixBound command steps a D :=
  ⟨fun q z hq hz i => (h.bound q z hq hz i).trans hBD⟩

theorem prefix_local (command : Code) (steps B : ℕ) (a : Data)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    PrefixBound command steps a (896*B+steps) := by
  constructor
  exact StructuredSpace.local_stack_bound (compiled command 838 838)
    (StreamResources.dataBits_le_mul _ ha)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One executed factor step, specialized to the actual source ring, its
computed multiplication table, and the three physical assignment masters. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native
open LeafProgram.NativeSemantics LeafProgram.AssignmentSemantics
open scoped BigOperators

variable {r Q d n : ℕ}

theorem context_table_correct (p : SourceBank.Parameters r Q d) (u J : ℕ)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t) (i j : Fin d) :
    RingBasis.basis (p.model.F p.t) i * RingBasis.basis (p.model.F p.t) j =
      ∑ k, LiftRing.of (p.model.F p.t)
        (wordValue 3 p.t ((sourceContext p n u J width hw).table i j k)) *
        RingBasis.basis (p.model.F p.t) k :=
  model_table_correct p.t p.ht p.hd p.model p.modulus p.cache i j

end SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics

end OAI.Algorithms
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

theorem degree_length {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a : Data}
    (h : QueryReady q node H high E U P a) : (a.stacks 204).length=d := by
  rw [h.degree,List.length_replicate]

end QueryReady

namespace DenseWord

/-- The existing native product uses the actual source-ring table. Its full
dense multiplication law is applied before any additive marker readout. -/
theorem multiplied {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (left right : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hl : Good ∅ q.p.t q.J left) (hr : Good ∅ q.p.t q.J right)
    (b : Data) (port : Fin 896)
    (hb : b.stacks port=Product.bytes
      (Product.run 3 q.p.t q.p.modulus q.p.cache q.ctx.table q.p.t q.J left right [])) :
    DenseWord q port (rawValue q.p.t q.J q.p.ops.decode left*
      rawValue q.p.t q.J q.p.ops.decode right) b := by
  refine ⟨_,hb,product_good 3 q.p.t q.p.modulus q.p.cache q.ctx.table ∅ q.p.t q.J left right hl hr,?_⟩
  have hv := product_dense 3 q.p.t q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    q.ctx.table (Factor.Semantics.context_table_correct q.p q.u q.J q.width q.widthLength)
    q.p.t q.J left right
  exact hv

end DenseWord

namespace PairAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : PairAccumulatorMeaning q value a) (hf : b.stacks 851=a.stacks 851) :
    PairAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end PairAccumulatorMeaning

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed concrete two-pass visitor. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
open OAI BitProgram StructuredCalls

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage


/-- Concrete multiplication preserves the retained query snapshot. Its
changing head/tuple dictionaries are separate from the pair accumulator. -/
theorem multiply_masterFrame {a b : Data}
    (hf : ∀ i,i∉QueryAssembler.pairScratch → i≠61 → i≠70 → i≠852 → i≠853 →
      b.stacks i=a.stacks i) : QueryMasterFrame a b := by
  constructor
  intro i hi
  have hs : i∉QueryAssembler.pairScratch ∧ i≠61 ∧ i≠70 ∧ i≠852 ∧ i≠853 := by
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact hf i hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2

/-- The fixed native multiply consumes the actual head sum and retains its
full dense product. Readout is deferred until the completed tuple is added. -/
theorem multiply_run_oai {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {left right : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hl : DenseWord q 852 left a) (hh : DenseWord q 853 right a)
    (ha : WordBound B a)
    (hcap : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J≤B) :
    ∃ steps b, Eval QueryAssembler.TupleMultiply.command steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (left*right) b ∧ b.stacks 853=[] ∧ QueryMasterFrame a b ∧
      WordBound B b ∧
      (∀ i,i∉QueryAssembler.pairScratch → i≠61 → i≠70 → i≠852 → i≠853 →
        b.stacks i=a.stacks i) ∧
      (∀ i,16≤ i.val → b.regs i=a.regs i) ∧
      steps+1≤51000*(B+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J ∧
      QueryExecution.PrefixBound QueryAssembler.TupleMultiply.command (steps+1) a
        (896*B+51000*(B+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J) := by
  obtain ⟨seed,hseed,hseedGood,hleft⟩:=hl.entries
  obtain ⟨head,hhead,hheadGood,hright⟩:=hh.entries
  have henv : QueryAssembler.TupleMultiply.environment a=
      Product.idle q.p.modulus.bits q.width q.p.cache.zero.val
        (RingTriple.tableEncoding q.ctx.table) (a.stacks 204)
        (List.replicate q.p.t true) (List.replicate q.J true) := by
    unfold QueryAssembler.TupleMultiply.environment
    rw [hr.modulus,hr.width,hr.scalarZero,hr.table,hr.precision,hr.order]
    rfl
  obtain ⟨steps,b,he,_,houtput,hzero,hframe,hb,hcost,_,_⟩:=
    QueryAssembler.TupleMultiply.command_eval 3 q.p.t q.p.modulus q.p.cache q.p.hz q.ctx.table
      (a.stacks 204) q.width hr.degree_length q.widthLength seed head hseedGood hheadGood a B
      henv hseed hhead ha hcap
  have hf:=multiply_masterFrame hframe
  have hv:=DenseWord.multiplied q seed head hseedGood hheadGood b 852 houtput
  rw [hleft,hright] at hv
  refine ⟨steps,b,he,hr.frame hf,hm.frame (hframe 851 (by decide) (by decide) (by decide)
    (by decide) (by decide)),hv,hzero,hf,hb,hframe,?_,hcost,?_⟩
  · intro i hi
    exact CommandRegisterFrames.eval_register_frame he i
      (QueryVisitorFrames.tupleMultiply_not_mem_writes i hi)
  · exact (QueryExecution.prefix_local QueryAssembler.TupleMultiply.command _ B a ha).mono (by omega)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run_oai
