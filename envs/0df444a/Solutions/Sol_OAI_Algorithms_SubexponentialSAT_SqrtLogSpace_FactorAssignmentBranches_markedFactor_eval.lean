-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:21:10.753679+00:00
-- url     : https://prove2.me/submissions/5848039f-8915-452f-8029-22127eae0bf7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_marked_value_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches_prepareIncidence_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace_markedWork_polynomial

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native lookup theorem specialized to actual hash-indexed incidence
payloads. Every occurrence of a variable uses the payload from the selected
hash slice; lookup correctness is discharged rather than an extra premise. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem lookup_graph {K : Type*} [DecidableEq K]
    (encode : K → List Bool) (hinj : Function.Injective encode)
    (payload : K → List Bool) (xs : List K) (k : K) (hk : k ∈ xs) :
    (xs.map fun j => (encode j,payload j)).lookup (encode k) = some (payload k) := by
  induction xs with
  | nil => simp at hk
  | cons j xs ih =>
    by_cases hj : j = k
    · subst j
      simp []
    · have he : encode j ≠ encode k := fun h => hj (hinj h)
      have hm : k ∈ xs := by simpa [hj,Ne.symm hj] using hk
      simp only [List.map_cons,List.lookup_cons]
      simp [beq_false_of_ne he.symm,ih hm]

theorem incidenceEntries_lookup {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) (v : Fin n) :
    (incidenceEntries payload i).lookup (Encoding.encodeNat v.val) = some (payload i v) := by
  apply lookup_graph (fun j : Fin n => Encoding.encodeNat j.val)
  · intro a b h
    exact Fin.ext (Encoding.encodeNat_injective h)
  · simp

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/

/-! Loop stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

theorem scaled_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (entries) :
    (scaled (K := K) p t M cache table scalar entries).map Prod.fst = entries.map Prod.fst := by
  simp [scaled, List.map_map, Function.comp_def]

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Cost stage. -/

/-! Semantics stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {K V R : Type*} [DecidableEq V] [CommRing R]

theorem scaled_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (constant : RingProgram.Code (Word (baseWidth p t)) d) (entries)
    (h : (entries.map Prod.fst).Nodup) :
    ((scaled (K := K) p t M cache table constant entries).map Prod.fst).Nodup := by
  rwa [scaled_keys]

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Wide native factor arithmetic and paid tape movement. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

theorem move_eval (a : Data) (src dst : Fin 768)
    (hsd : src ≠ dst) (hst : src ≠ 159) (htd : (159 : Fin 768) ≠ dst)
    (htmp : a.stacks 159 = []) :
    Eval (move src dst) (9*(a.stacks src).length+8) a (moved a src dst) := by
  have h1 := SubexpScanPrimitives.copy_eval a src dst 159 0 1 hsd hst htd (by decide) htmp
  let b := SubexpScanPrimitives.afterCopy a src dst 0 1
  have h2 : Eval (clear src) (2*(b.stacks src).length+3) b
      ⟨readRegs b.regs 0 1 none,Function.update b.stacks src []⟩ :=
    Eval.call _ (ListRegisterProgram.clear_run src (0 : Fin 40) 1 b.regs b.stacks)
  have hlen : b.stacks src = a.stacks src := by
    simp [b,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,hsd]
  have hout : (⟨readRegs b.regs 0 1 none,Function.update b.stacks src []⟩ : Data) =
      moved a src dst := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [b,SubexpScanPrimitives.afterCopy,StackRoutines.readRegs_reset]
    · rfl
  rw [hout] at h2
  have h := h1.seq h2
  simpa only [move,copy,hlen,show 7*(a.stacks src).length+5+
      (2*(a.stacks src).length+3)=9*(a.stacks src).length+8 by omega] using h


end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (vars : Finset (Fin n)) (u J : ℕ)

 theorem scaled_good (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (h : Good vars u J a) :
    Good vars u J (Squarefree.ScaleProgram.scaled p t M cache table c a) := by
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact h.valid y hy
  · exact Squarefree.ScaleProgram.scaled_nodup p t M cache table c a h.nodup

theorem normalize_good (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : ∀ x ∈ source, Product.ValidKey vars u J x.1) (hi : Good vars u J seed) :
    Good vars u J (Normalize.run p t M cache source seed) :=
  ⟨Normalize.run_preserves_keys p t M cache _ source seed hs hi.valid,
    Normalize.run_nodup p t M cache source seed hi.nodup⟩

theorem product_good (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good vars u J left) (hr : Good vars u J right) :
    Good vars u J (Product.run p t M cache table u J left right []) :=
  ⟨Product.run_valid p t M cache table vars u J left right [] hl.valid hr.valid (by simp),
    Product.run_nodup p t M cache table u J left right [] (by simp [Squarefree.Sparse.keys])⟩

variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))

include hone in
theorem literal_good (payload : List (Product.Entry n (baseWidth p t) d))
    (hp : Good vars u J payload) (positive : Bool) :
    Good vars u J (LiteralCallback.value p t M cache table minusOne one payload positive) := by
  cases positive
  · exact hp
  · exact normalize_good p t M cache vars u J _ one
      (scaled_good p t M cache table vars u J minusOne payload hp).valid hone

include hone hi in
theorem step_good (l : SAT.Literal (Fin n))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (Clause.step p t M cache table minusOne one incidence u J l acc) :=
  product_good p t M cache table vars u J acc _ ha
    (literal_good p t M cache table vars u J minusOne one hone _ (hi l.variable) l.positive)

include hone hi in
theorem clause_fold_good (ls : List (SAT.Literal (Fin n)))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (DynamicFold.value
      (Clause.step p t M cache table minusOne one incidence u J) ls acc) := by
  induction ls generalizing acc with
  | nil => exact ha
  | cons l ls ih => exact ih _ (step_good p t M cache table vars u J minusOne one incidence hone hi l acc ha)

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Denotation of the concrete raw row recurrence used by the native program. -/


/-! Instantiation at the actual supplied-polynomial unramified ring. -/


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Execution of the computed factor value and its multiplication into the
current head product. Input incidence dictionaries are the physically
produced tables supplied by the preceding service. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem low_ne (i : Fin 56) (j : Fin 768) (hj : 56 ≤ j.val) :
    nativeStacks (Memory.lowPort i)  ≠  j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=j.val at hv
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate correction specialization keeps every factor dictionary over the
empty formal-variable support. The retained key capacity is polynomial u*J.
The bounds below apply to the actual native indicator, clause and product
programs, including their input parsers and paid tape cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps NativeSemantics FactorBounds

variable {p t n d : ℕ} [Fact p.Prime]

theorem clauseResult_good (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) :
    Good (∅ : Finset (Fin n)) ctx.u ctx.J (FactorServices.clauseResult ctx minus one incidence ls) :=
  clause_fold_good p t ctx.modulus ctx.cache ctx.table (∅ : Finset (Fin n)) ctx.u ctx.J
    minus one incidence hone hi ls one hone

theorem markedArithmetic_run_space (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) (a : Factor.Data)
    (hlow : ∀ i, a.stacks (Clause.callerStacks (Memory.lowPort i)) = low ctx i)
    (hsource : a.stacks 63 = Encoding.encodeList id (ls.map Clause.literalBits))
    (htable : a.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence))
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch, a.stacks (Clause.callerStacks i) = [])
    (hseedTape : a.stacks 151 = Product.bytes seed) (htmp : a.stacks 159 = []) :
    let budget := serviceBudget (baseWidth p t) d n ctx.u ctx.J ls.length 0 0
    let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
      (FactorServices.clauseResult ctx minus one incidence ls) []
    let program := compiled markedArithmetic 63 151
    ∃ steps b, steps ≤ budget ∧ Good ∅ ctx.u ctx.J result ∧
      Eval markedArithmetic steps a b ∧
      b.stacks = Function.update (Function.update (Function.update
        (Function.update a.stacks 63 []) 67 []) 62 []) 151 (Product.bytes result) ∧
      Trace program (steps + 1) (a.withPC (some program.entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ stackBits a.stacks + budget + 1 := by
  dsimp only
  obtain ⟨steps, b, hs, he, hb⟩ := Factor.marked_value_eval ctx minus one seed incidence
    (Cost.entries incidence)
    (incidenceEntries_lookup (fun (_ : Unit) v => Product.bytes (incidence v)) ())
    ls a hlow hsource htable honeTape hminus hwork hseedTape htmp
  rw [htable] at hs
  have hbound := hs.trans (markedWork_polynomial ctx minus one seed incidence hone hseed hi ls)
  have hgood := product_good p t ctx.modulus ctx.cache ctx.table ∅ ctx.u ctx.J seed _ hseed
    (clauseResult_good ctx minus one incidence hone hi ls)
  refine ⟨steps, b, hbound, hgood, he, hb, compiled_halt_trace he 63 151, ?_⟩
  intro prefixSteps intermediate hp htrace
  have hgrowth := trace_dataBits (compiled markedArithmetic 63 151) htrace
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual ordinary and marked factor branches. The physical factor ID is
converted to the unary source counter, then the specialized table is produced
before the original finite-ring arithmetic is run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram


/-- The marked branch moves the actual parsed clause into the native reader,
evaluates it, and multiplies it into the retained group product. -/
theorem marked_arithmetic_eval {t n d : ℕ} (ctx : Context 3 t n d)
    (minus : RingProgram.Code (Word (baseWidth 3 t)) d)
    (one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) (a : Factor.Data)
    (hraw : a.stacks 154 = Encoding.encodeList id (ls.map Clause.literalBits))
    (houtput : a.stacks 63 = [])
    (hlow : ∀ i, a.stacks (Clause.callerStacks (Memory.lowPort i)) = low ctx i)
    (htable : a.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence))
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch, a.stacks (Clause.callerStacks i) = [])
    (hseedTape : a.stacks 151 = Product.bytes seed) (htmp : a.stacks 159 = []) :
    let result := Product.run 3 t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
      (FactorServices.clauseResult ctx minus one incidence ls) []
    ∃ steps e,
      steps ≤ 9 * (a.stacks 154).length + 8 +
        FactorEvaluationSpace.serviceBudget (baseWidth 3 t) d n ctx.u ctx.J ls.length 0 0 ∧
      Good ∅ ctx.u ctx.J result ∧
      Eval (.seq (Factor.move 154 63) FactorEvaluationSpace.markedArithmetic) steps a e ∧
      e.stacks = Function.update (Function.update (Function.update (Function.update
        (Function.update a.stacks 154 []) 63 []) 67 []) 62 []) 151 (Product.bytes result) := by
  dsimp only
  let mid := Factor.moved a 154 63
  have hm : mid.stacks = Function.update (Function.update a.stacks 63 (a.stacks 154)) 154 [] := by
    simp [mid, Factor.moved, houtput]
  have hmlow : ∀ i, mid.stacks (Clause.callerStacks (Memory.lowPort i)) = low ctx i := by
    intro i
    have hn (j : Fin 768) (hj : 56 ≤ j.val) :
        Clause.callerStacks (Memory.lowPort i) ≠ j := Factor.low_ne i j hj
    rw [hm, Function.update_of_ne (hn 154 (by decide)),
      Function.update_of_ne (hn 63 (by decide))]
    exact hlow i
  have hmwork : ∀ i ∈ FactorServices.clauseScratch,
      mid.stacks (Clause.callerStacks i) = [] := by
    intro i hi
    have hn : Clause.callerStacks i ≠ 154 ∧ Clause.callerStacks i ≠ 63 :=
      (by decide : ∀ i ∈ FactorServices.clauseScratch,
        Clause.callerStacks i ≠ 154 ∧ Clause.callerStacks i ≠ 63) i hi
    rw [hm, Function.update_of_ne hn.1, Function.update_of_ne hn.2]
    exact hwork i hi
  obtain ⟨steps,e,hsteps,hgood,he,hstore,_,_⟩ :=
    FactorEvaluationSpace.markedArithmetic_run_space ctx minus one seed incidence hone hseed hi ls mid
      hmlow (by simpa [hm] using hraw) (by simpa [hm] using htable)
      (by simpa [hm] using honeTape) (by simpa [hm] using hminus) hmwork
      (by simpa [hm] using hseedTape) (by simpa [hm] using htmp)
  refine ⟨9 * (a.stacks 154).length + 8 + steps,e,Nat.add_le_add_left hsteps _,hgood,
    (Factor.move_eval a 154 63 (by decide) (by decide) (by decide) htmp).seq he,?_⟩
  rw [hstore,hm]
  funext i
  by_cases h154 : i = 154 <;> by_cases h63 : i = 63 <;>
    by_cases h67 : i = 67 <;> by_cases h62 : i = 62 <;> by_cases h151 : i = 151 <;>
    simp [h154, h63, h67, h62, h151]


/-- A marked factor is computed entirely from retained physical words. The
returned specialized incidence dictionaries are the very witnesses used by
the clause arithmetic; the complete private table bank is restored. -/
theorem markedFactor_eval_oai {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (ctx : Context 3 p.t n d) (f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (ls : List (SAT.Literal (Fin n))) (a : FactorAssignmentProgram.Data)
    (hid : a.stacks 149 = (Encoding.encodeNat f).reverse)
    (h556 : a.stacks 556 = []) (h359 : a.stacks 359 = []) (h62 : a.stacks 62 = [])
    (hready : FactorTableNative.Ready p ps P ctx.u ctx.J n f B S theta (tableInput a f))
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = [])
    (hraw : a.stacks 154 = Encoding.encodeList id (ls.map Clause.literalBits))
    (houtput : a.stacks 63 = [])
    (hlow : ∀ i, a.stacks (lowStack (Clause.callerStacks (Memory.lowPort i))) = low ctx i)
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch,
      a.stacks (lowStack (Clause.callerStacks i)) = [])
    (hseedTape : a.stacks 151 = Product.bytes seed) (htmp : a.stacks 159 = []) :
    ∃ (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)), ∃ steps e,
      (∀ v, TruncatedRingProgram.Good ∅ ctx.u ctx.J (incidence v)) ∧
      (∀ v, FactorTableNative.PayloadMeaning p ps P ctx.u ctx.J n f theta
        (FactorTableProgram.staged (tableInput a f)).stacks v.val (Product.bytes (incidence v))) ∧
      let result := Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
        (FactorServices.clauseResult ctx minus one incidence ls) []
      steps ≤ 7 * (f + 1) + 7 + tableTime p ctx.u ctx.J n B S a f +
        (9 * (a.stacks 154).length + 9 +
          FactorEvaluationSpace.serviceBudget (baseWidth 3 p.t) d n ctx.u ctx.J ls.length 0 0) ∧
      Good ∅ ctx.u ctx.J result ∧
      Eval FactorAssignmentProgram.markedFactor steps a e ∧
      e.stacks = Function.update (Function.update a.stacks 154 []) 151 (Product.bytes result) := by
  obtain ⟨incidence,ki,mid,hgood,_,hmeaning,hki,hei,hm⟩ :=
    prepareIncidence_eval p ps P ctx.u ctx.J f B S theta a hid h556 h359 hready hblank
  let small := projectState id lowStack mid
  have frame (i : Fin 768) (hi : i ≠ 62) : small.stacks i = a.stacks (lowStack i) := by
    change mid.stacks (lowStack i) = _
    rw [hm, Function.update_of_ne]
    intro he
    exact hi (Fin.ext (congrArg (fun k : Fin 896 => k.val) he))
  have lowReady : ∀ i, small.stacks (Clause.callerStacks (Memory.lowPort i)) = low ctx i := by
    intro i
    exact (frame (Clause.callerStacks (Memory.lowPort i))
      (show Clause.callerStacks (Memory.lowPort i) ≠ 62 from
        Factor.low_ne i 62 (by decide))).trans (hlow i)
  have workReady : ∀ i ∈ FactorServices.clauseScratch,
      small.stacks (Clause.callerStacks i) = [] := by
    intro i hi
    have hn : Clause.callerStacks i ≠ 62 :=
      (by decide : ∀ i ∈ FactorServices.clauseScratch, Clause.callerStacks i ≠ 62) i hi
    rw [frame _ hn]
    exact hwork i hi
  have ht : small.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence) := by
    change mid.stacks 62 = _
    simp [hm]
  obtain ⟨ka,z,hka,hresult,hea,hz⟩ := marked_arithmetic_eval ctx minus one seed incidence
    hone hseed (fun v => ⟨(hgood v).valid,(hgood v).nodup⟩) ls small
    ((frame 154 (by decide)).trans hraw) ((frame 63 (by decide)).trans houtput)
    lowReady ht ((frame 69 (by decide)).trans honeTape)
    ((frame 76 (by decide)).trans hminus) workReady
    ((frame 151 (by decide)).trans hseedTape) ((frame 159 (by decide)).trans htmp)
  let e := embedState id lowStack mid z
  have her : Eval (liftLow (.seq (Factor.move 154 63) FactorEvaluationSpace.markedArithmetic)
      154 151) (ka+1) mid e :=
    eval_liftCommand_from_state _ 154 151 id lowStack mid
      Function.injective_id (Fin.castAdd_injective _ _) hea
  have hbase : Function.extend lowStack small.stacks mid.stacks = mid.stacks :=
    congrArg (fun state : State 40 896 => state.stacks) (embedState_project id lowStack mid
      Function.injective_id (Fin.castAdd_injective _ _))
  have hstore : e.stacks = Function.update (Function.update (Function.update (Function.update
      (Function.update mid.stacks 154 []) 63 []) 67 []) 62 []) 151
        (Product.bytes (Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (FactorServices.clauseResult ctx minus one incidence ls) [])) := by
    change Function.extend lowStack z.stacks mid.stacks = _
    rw [hz]
    rw [ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),hbase]
    rfl
  have h67 : a.stacks 67 = [] := hwork 67 (by decide)
  refine ⟨incidence,ki+(ka+1),e,hgood,hmeaning,?_,hresult,hei.seq her,?_⟩
  · rw [frame 154 (by decide)] at hka
    rw [show lowStack (154 : Fin 768) = (154 : Fin 896) from rfl] at hka
    omega
  · rw [hstore,hm]
    funext i
    by_cases h154 : i = 154 <;> by_cases h63 : i = 63 <;>
      by_cases hi67 : i = 67 <;> by_cases hi62 : i = 62 <;> by_cases h151 : i = 151 <;>
      simp [h154, h63, hi67, hi62, h151, houtput, h67, h62]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval_oai
