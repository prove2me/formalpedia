-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.hashFactor_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:20:24.014642+00:00
-- url     : https://prove2.me/submissions/cf76dd75-3de7-40d5-bc43-d9edbe090a5f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_expanded_hash_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches_prepareIncidence_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace_hashWork_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace_result_good

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

theorem nativeStacks_injective : Function.Injective nativeStacks :=
  Fin.castAdd_injective 96 672


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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed per-assignment factor evaluation. Factors are dispatched by runtime
ID; hash rows are expanded and tested by the computed idempotent, the marked
clause is multiplied directly, and added neutral factors contribute one.
Every operation below is an actual finite instruction table or native loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

theorem indicatorStacks_injective : Function.Injective indicatorStacks :=
  (Equiv.swap 78 143).injective.comp nativeStacks_injective

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem product_good (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good vars u J left) (hr : Good vars u J right) :
    Good vars u J (Product.run p t M cache table u J left right []) :=
  ⟨Product.run_valid p t M cache table vars u J left right [] hl.valid hr.valid (by simp),
    Product.run_nodup p t M cache table u J left right [] (by simp [Squarefree.Sparse.keys])⟩

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

theorem indicatorStacks_low (i : Fin 56) :
    indicatorStacks (Memory.lowPort i)=nativeStacks (Memory.lowPort i) := by
  have h78 := low_ne i 78 (by decide)
  have h143 := low_ne i 143 (by decide)
  simp [indicatorStacks,Equiv.swap_apply_def,h78,h143]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical factor inputs that are retained by the incidence producer. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

theorem HashInput.frame {t n d : ℕ} {ctx : Context 3 t n d}
    {minus : RingProgram.Code (Word (baseWidth 3 t)) d}
    {one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d)}
    {source : List (List (SAT.Literal (Fin n)))}
    {terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3)}
    {digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 t))}
    {b : ℕ} {a z : Data} (h : HashInput ctx minus one seed source terms digits b a)
    (hz : ∀ i : Fin 768,i≠62 → z.stacks i=a.stacks i) :
    HashInput ctx minus one seed source terms digits b z := by
  constructor
  · rw [hz 154 (by decide)]; exact h.raw
  · rw [hz 700 (by decide)]; exact h.formula
  · rw [hz 708 (by decide)]; exact h.width
  · rw [hz 707 (by decide)]; exact h.modulus
  · rw [hz 280 (by decide)]; exact h.ringShape
  · rw [hz 64 (by decide)]; exact h.output
  · intro i hi
    have hne : i≠(62 : Fin 768) := by
      intro he
      subst i
      simp [Expansion.scratch] at hi
    rw [hz i hne]
    exact h.expand i hi
  · rw [hz 358 (by decide)]; exact h.work358
  · rw [hz 359 (by decide)]; exact h.work359
  · intro i
    rw [hz _ (by rw [indicatorStacks_low]; exact low_ne i 62 (by decide))]
    exact h.low i
  · rw [hz 69 (by decide)]; exact h.one
  · rw [hz 76 (by decide)]; exact h.minus
  · rw [hz 143 (by decide)]; exact h.tape
  · rw [hz 88 (by decide)]; exact h.shape
  · intro i hi
    have hne : indicatorStacks i≠62 := by
      intro he
      have hi62 : i=(62 : Fin 96) :=
        indicatorStacks_injective (he.trans (by rfl))
      subst i
      simp [FactorServices.indicatorScratch] at hi
    rw [hz _ hne]
    exact h.work i hi
  · rw [hz 151 (by decide)]; exact h.seed
  · rw [hz 159 (by decide)]; exact h.temporary

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
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


/-- Original row expansion and native indicator evaluation share the same
empty-support dictionary witnesses and fixed polynomial arithmetic budget. -/
theorem hash_arithmetic_eval {t n d : ℕ} (ctx : Context 3 t n d)
    (ht : 0 < t) (hd : 0 < d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth 3 t)) d)
    (one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 t)))
    (b width : ℕ) (hb : 0 < b)
    (hbound : 3 * (HashInputProgram.Expansion.encodedClauses source).length ≤ 2 ^ b)
    (hwidth : ∀ w ∈ HashInputProgram.Expansion.weightedRow t d source terms,
      w.literals.length ≤ width)
    (a : Factor.Data) (hin : Factor.HashInput ctx minus one seed source terms digits b a)
    (htable : a.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence)) :
    let result := Product.run 3 t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
      (Indicator.result ctx minus one incidence
        (HashInputProgram.Expansion.weightedRow t d source terms) digits) []
    ∃ steps e,
      steps ≤ 9 * (a.stacks 154).length + 10 +
        HashInputProgram.Loop.uniformBudget t (d-1) b (a.stacks 707)
          (HashInputProgram.Expansion.encodedClauses source) terms.length +
        FactorEvaluationSpace.serviceBudget (baseWidth 3 t) d n ctx.u ctx.J
          width terms.length digits.length ∧
      Good ∅ ctx.u ctx.J result ∧
      Eval (.seq Expansion.forwardCommand FactorEvaluationSpace.hashArithmetic) steps a e ∧
      e.stacks = Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update a.stacks 154 []) 64 []) 67 []) 68 []) 62 []) 151
          (Product.bytes result) := by
  dsimp only
  obtain ⟨steps,e,hsteps,he,hstore⟩ := Factor.expanded_hash_eval ctx ht hd minus one seed incidence
    (Cost.entries incidence)
    (incidenceEntries_lookup (fun (_ : Unit) v => Product.bytes (incidence v)) ())
    source terms digits b hb hbound a hin.raw hin.formula hin.width hin.modulus
    hin.ringShape hin.output hin.expand hin.work358 hin.work359 hin.low
    htable hin.one hin.minus hin.tape hin.shape hin.work hin.seed hin.temporary
  have hwork := FactorEvaluationSpace.hashWork_polynomial ctx hu hJ
    minus one seed incidence hone hseed hi
    (HashInputProgram.Expansion.weightedRow t d source terms) digits width hwidth
  rw [HashInputProgram.Expansion.weightedRow_length] at hwork
  rw [htable] at hsteps
  have hgood := product_good 3 t ctx.modulus ctx.cache ctx.table ∅ ctx.u ctx.J seed _ hseed
    (FactorEvaluationSpace.result_good ctx hu hJ minus one incidence
      hone hi (HashInputProgram.Expansion.weightedRow t d source terms) digits)
  exact ⟨steps,e,by omega,hgood,he,hstore⟩


/-- Ordinary factors read the selected original raw row, expand its original
clauses, apply the actual idempotent program, and multiply only after immediate
correction specialization. No expanded row or incidence service is assumed. -/
theorem hashFactor_eval_oai {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (ctx : Context 3 p.t n d) (f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 p.t)))
    (b width : ℕ) (hb : 0 < b)
    (hbound : 3 * (HashInputProgram.Expansion.encodedClauses source).length ≤ 2 ^ b)
    (hwidth : ∀ w ∈ HashInputProgram.Expansion.weightedRow p.t d source terms,
      w.literals.length ≤ width)
    (a : FactorAssignmentProgram.Data)
    (hid : a.stacks 149 = (Encoding.encodeNat f).reverse)
    (h556 : a.stacks 556 = []) (h62 : a.stacks 62 = [])
    (hready : FactorTableNative.Ready p ps P ctx.u ctx.J n f B S theta (tableInput a f))
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = [])
    (hin : Factor.HashInput ctx minus one seed source terms digits b
      (projectState id lowStack a)) :
    ∃ (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)), ∃ steps e,
      (∀ v, TruncatedRingProgram.Good ∅ ctx.u ctx.J (incidence v)) ∧
      (∀ v, FactorTableNative.PayloadMeaning p ps P ctx.u ctx.J n f theta
        (FactorTableProgram.staged (tableInput a f)).stacks v.val (Product.bytes (incidence v))) ∧
      let result := Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
        (Indicator.result ctx minus one incidence
          (HashInputProgram.Expansion.weightedRow p.t d source terms) digits) []
      steps ≤ 7 * (f + 1) + 7 + tableTime p ctx.u ctx.J n B S a f +
        (9 * (a.stacks 154).length + 11 +
          HashInputProgram.Loop.uniformBudget p.t (d-1) b (a.stacks 707)
            (HashInputProgram.Expansion.encodedClauses source) terms.length +
          FactorEvaluationSpace.serviceBudget (baseWidth 3 p.t) d n ctx.u ctx.J
            width terms.length digits.length) ∧
      Good ∅ ctx.u ctx.J result ∧
      Eval FactorAssignmentProgram.hashFactor steps a e ∧
      e.stacks = Function.update (Function.update a.stacks 154 []) 151 (Product.bytes result) := by
  obtain ⟨incidence,ki,mid,hgood,_,hmeaning,hki,hei,hm⟩ :=
    prepareIncidence_eval p ps P ctx.u ctx.J f B S theta a hid h556 hin.work359 hready hblank
  let small := projectState id lowStack mid
  have frame (i : Fin 768) (hi : i ≠ 62) : small.stacks i = a.stacks (lowStack i) := by
    change mid.stacks (lowStack i) = _
    rw [hm, Function.update_of_ne]
    intro he
    exact hi (Fin.ext (congrArg (fun k : Fin 896 => k.val) he))
  have hinput : Factor.HashInput ctx minus one seed source terms digits b small :=
    hin.frame frame
  have ht : small.stacks 62 = Squarefree.Program.lookupRecords (Cost.entries incidence) := by
    change mid.stacks 62 = _
    simp [hm]
  obtain ⟨ka,z,hka,hresult,hea,hz⟩ := hash_arithmetic_eval ctx p.ht p.hd
    hready.positiveU hready.positiveJ minus one seed incidence hone hseed
    (fun v => ⟨(hgood v).valid,(hgood v).nodup⟩) source terms digits b width hb hbound hwidth
    small hinput ht
  rw [frame 154 (by decide),frame 707 (by decide)] at hka
  rw [show lowStack (154 : Fin 768) = (154 : Fin 896) from rfl,
    show lowStack (707 : Fin 768) = (707 : Fin 896) from rfl] at hka
  let e := embedState id lowStack mid z
  have her : Eval (liftLow (.seq Expansion.forwardCommand FactorEvaluationSpace.hashArithmetic)
      154 151) (ka+1) mid e :=
    eval_liftCommand_from_state _ 154 151 id lowStack mid
      Function.injective_id (Fin.castAdd_injective _ _) hea
  have hbase : Function.extend lowStack small.stacks mid.stacks = mid.stacks :=
    congrArg (fun state : State 40 896 => state.stacks) (embedState_project id lowStack mid
      Function.injective_id (Fin.castAdd_injective _ _))
  have hstore : e.stacks = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update mid.stacks 154 []) 64 []) 67 []) 68 []) 62 []) 151
        (Product.bytes (Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (Indicator.result ctx minus one incidence
            (HashInputProgram.Expansion.weightedRow p.t d source terms) digits) [])) := by
    change Function.extend lowStack z.stacks mid.stacks = _
    rw [hz]
    rw [ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),
      ProgramLinking.extend_update (show Function.Injective lowStack from Fin.castAdd_injective 768 128),hbase]
    rfl
  have h64 : a.stacks 64 = [] := hin.output
  have h67 : a.stacks 67 = [] := hin.work 67 (by decide)
  have h68 : a.stacks 68 = [] := hin.work 68 (by decide)
  refine ⟨incidence,ki+(ka+1),e,hgood,hmeaning,?_,hresult,hei.seq her,?_⟩
  · omega
  · rw [hstore,hm]
    funext i
    by_cases h154 : i = 154 <;> by_cases hi64 : i = 64 <;>
      by_cases hi67 : i = 67 <;> by_cases hi68 : i = 68 <;>
      by_cases hi62 : i = 62 <;> by_cases h151 : i = 151 <;>
      simp [h154, hi64, hi67, hi68, hi62, h151, h64, h67, h68, h62]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.hashFactor_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.hashFactor_eval_oai
