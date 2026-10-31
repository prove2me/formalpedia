-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:09:25.973045+00:00
-- url     : https://prove2.me/submissions/a1940f4b-0a47-4528-b5b9-88dc3754ba63

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem mem_indexUniverse (vars : Finset V) (t J : ℕ) (a : Index V) :
    a ∈ indexUniverse vars t J ↔ a.Kept t J ∧ a.vars ⊆ vars ∧ a.vars.card < J := by
  rcases a with ⟨u, z, s⟩
  simp [indexUniverse, supportUniverse, Index.Kept, Finset.mem_image]

theorem indexUniverse_card_le (vars : Finset V) (t J : ℕ) :
    (indexUniverse vars t J).card ≤ t * J * (supportUniverse vars J).card := by
  exact (Finset.card_image_le).trans (by simp)

end Sparse
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact stored-list specification of the native Horner application. The
operations here are the functional results of the concrete normalized-add
and sparse-product machines, rather than operations on noncomputable jets. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open SubexpLiftRing SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}

omit [Fact (Nat.Prime p)] in
theorem constantStored_nodup (word : RingProgram.ScalarCode p t) :
    (Squarefree.Sparse.keys (constantStored p t cache (n:=n) (d:=d) word)).Nodup := by
  simp [constantStored,Squarefree.Sparse.keys]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem keptJoin_length {n B d : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) : (keptJoin a u J entries).length ≤ entries.length := by
  induction entries with
  | nil => simp [keptJoin]
  | cons b entries ih =>
    by_cases h : (a.join b.1).Kept u J <;> simp [keptJoin,h] <;> omega

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsCapacity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Finite record capacity for the actual normalized stored lists. The finite
universe is used for counting only; the program never enumerates it. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram

theorem valid_nil {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ) :
    Valid vars u J ([] : List (Product.Entry n B d)) := by
  intro a ha
  simp at ha

theorem good_nil {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ) :
    Good vars u J ([] : List (Product.Entry n B d)) :=
  ⟨valid_nil vars u J, by simp [Squarefree.Sparse.keys]⟩

theorem length_le_capacity {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) (h : Good vars u J entries) :
    entries.length ≤ capacity vars u J := by
  have hs : (Squarefree.Sparse.keys entries).toFinset ⊆
      Squarefree.Sparse.indexUniverse vars u J := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    have hh := h.1 a ha
    exact (Squarefree.Sparse.mem_indexUniverse vars u J a.1).mpr
      ⟨hh.1, hh.2.2, hh.2.1.trans_lt hh.1.2⟩
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup h.2] at hc
  have hl : entries.length ≤ (Squarefree.Sparse.indexUniverse vars u J).card := by
    simpa only [Squarefree.Sparse.keys,List.length_map] using hc
  exact hl.trans (Squarefree.Sparse.indexUniverse_card_le vars u J)

variable {p t n d : ℕ} [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
theorem constant_good (cache : RingProgram.ScalarCache p t)
    (vars : Finset (Fin n)) (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (word : RingProgram.ScalarCode p t) :
    Good vars u J (constantStored p t cache (d:=d) word) := by
  refine ⟨?_, constantStored_nodup p t cache word⟩
  intro a ha
  simp only [constantStored,List.mem_singleton] at ha
  subst a
  simp [Product.ValidKey,Squarefree.Index.origin,Squarefree.Index.Kept,
    Squarefree.Index.Valid,hu,hJ]

theorem add_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (vars : Finset (Fin n)) (u J : ℕ)
    (a b : Stored p t (n:=n) (d:=d)) (ha : Valid vars u J a) (hb : Good vars u J b) :
    Good vars u J (addStored p t M cache a b) := by
  exact ⟨Normalize.run_preserves_keys p t M cache (Product.ValidKey vars u J) a b ha hb.1,
    Normalize.run_nodup p t M cache a b hb.2⟩

theorem mul_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ) (a b : Stored p t (n:=n) (d:=d))
    (ha : Valid vars u J a) (hb : Valid vars u J b) :
    Good vars u J (mulStored p t M cache table u J a b) := by
  exact ⟨Product.run_valid p t M cache table vars u J a b [] ha hb (valid_nil vars u J),
    Product.run_nodup p t M cache table u J a b [] (by simp [Squarefree.Sparse.keys])⟩

theorem triple_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (h : Stored p t (n:=n) (d:=d)) (hh : Valid vars u J h)
    (v : Triple (RingProgram.ScalarCode p t)) :
    Good vars u J (tripleStored p t M cache table u J h v) := by
  have hc := constant_good (d:=d) cache vars u J hu hJ v.c
  have hb := constant_good (d:=d) cache vars u J hu hJ v.b
  have ha := constant_good (d:=d) cache vars u J hu hJ v.a
  have hch := mul_good M cache table vars u J _ h hc.1 hh
  have hchb := add_good M cache vars u J _ _ hch.1 hb
  have hchbh := mul_good M cache table vars u J _ h hchb.1 hh
  exact add_good M cache vars u J _ _ hchbh.1 ha

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial envelopes for the concrete degree-two coefficient and
Horner machines. Every byte copy, dictionary scan, product and tape reversal
in the native cost definitions is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

theorem loopResult_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h g : Stored p t (n:=n) (d:=d))
    (hh : Valid vars ctx.u ctx.J h) (hg : Valid vars ctx.u ctx.J g)
    (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Stored p t (n:=n) (d:=d))
    (ha : Good vars ctx.u ctx.J a) :
    Good vars ctx.u ctx.J (loopResult ctx h g vs a) := by
  induction vs generalizing a with
  | nil => exact ha
  | cons v vs ih =>
    have he := triple_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J hu hJ h hh v
    have hm := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J a g ha.1 hg
    exact ih _ (add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ _ hm.1 he)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsMultiplier
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The setup charge includes scaling by cached minus one, normalized cubic
arithmetic, construction of the U key, and the physical key-map loop. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps Multiplier

variable {p t n d : ℕ} [Fact p.Prime]

theorem scaled_valid (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h : Stored p t (n:=n) (d:=d)) (hh : Valid vars ctx.u ctx.J h) :
    Valid vars ctx.u ctx.J
      (Squarefree.ScaleProgram.scaled p t ctx.modulus ctx.cache ctx.table minus h) := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact hh b hb

theorem complemented_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Valid vars ctx.u ctx.J h) (ho : Good vars ctx.u ctx.J one) :
    Good vars ctx.u ctx.J (complemented ctx minus h one) :=
  add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ one (scaled_valid ctx vars minus h hh) ho

theorem cubic_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Valid vars ctx.u ctx.J h) (ho : Good vars ctx.u ctx.J one) :
    Good vars ctx.u ctx.J (cubic ctx minus h one) := by
  have ha := complemented_good ctx vars minus h one hh ho
  have hb := add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ one ha.1 ho
  have hq := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J _ _ hb.1 ha.1
  exact mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J _ h hq.1 hh

omit [Fact (Nat.Prime p)] in
theorem shiftForward_eq_keptJoin (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (xs : Stored p t (n:=n) (d:=d)) :
    shiftForward a u J xs=Product.keptJoin a u J xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b,c⟩
    simp only [shiftForward,Product.keptJoin,ih]

theorem prepared_bounded (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Valid vars ctx.u ctx.J h) (ho : Good vars ctx.u ctx.J one) :
    Bounded ctx vars (prepared ctx minus h one) := by
  have hc := cubic_good ctx vars minus h one hh ho
  have hv := Product.keptJoin_valid vars ctx.u ctx.J (uKey n) (cubic ctx minus h one)
    (by simp [uKey,Squarefree.Index.Valid]) hc.1
  constructor
  · intro a ha
    apply hv a
    simpa only [prepared,shifted,List.mem_reverse,shiftForward_eq_keptJoin] using ha
  · have hl := Product.keptJoin_length (uKey n) ctx.u ctx.J (cubic ctx minus h one)
    simpa only [prepared,shifted,List.length_reverse,shiftForward_eq_keptJoin] using
      hl.trans (length_le_capacity vars ctx.u ctx.J _ hc)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

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

namespace Good
variable {n B d u J : ℕ} {vars : Finset (Fin n)}

 theorem nil : Good (B := B) (d := d) vars u J [] :=
  ⟨by simp, by simp [Squarefree.Sparse.keys]⟩

end Good

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

include hone hi in
theorem row_step_good (w : Row.WeightedClause n (baseWidth p t) d)
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (Row.value p t M cache table minusOne one incidence u J w acc) :=
  normalize_good p t M cache vars u J _ acc
    (scaled_good p t M cache table vars u J w.scalar _
      (clause_fold_good p t M cache table vars u J minusOne one incidence hone hi w.literals one hone)).valid ha

include hone hi in
theorem row_fold_good (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (DynamicFold.value
      (Row.value p t M cache table minusOne one incidence u J) ws acc) := by
  induction ws generalizing acc with
  | nil => exact ha
  | cons w ws ih => exact ih _ (row_step_good p t M cache table vars u J minusOne one incidence hone hi w acc ha)

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Denotation of the concrete raw row recurrence used by the native program. -/


/-! Instantiation at the actual supplied-polynomial unramified ring. -/


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentSemanticsFactors
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected factor map matches the runtime dispatcher: hashes first,
one optional direct marked clause, then skipped neutral IDs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open NativeSemantics
open IdempotentApplyProgram.Steps (Context)

variable {p t n d : ℕ} [Fact p.Prime]

theorem indicator_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ v, Good vars ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t))) :
    Good vars ctx.u ctx.J (Indicator.result ctx minus one incidence ws digits) := by
  have hh := row_fold_good p t ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J
    minus one incidence hone hi ws [] Good.nil
  have ho : IdempotentApplyProgram.Bounds.Good vars ctx.u ctx.J one := ⟨hone.valid,hone.nodup⟩
  have hg := IdempotentApplyProgram.Bounds.prepared_bounded ctx vars minus
    (Indicator.rawHash ctx minus one incidence ws) one hh.valid ho
  have h := IdempotentApplyProgram.Bounds.loopResult_good ctx vars hu hJ
    (Indicator.rawHash ctx minus one incidence ws) _ hh.valid hg.1 digits.reverse []
    (IdempotentApplyProgram.Bounds.good_nil vars ctx.u ctx.J)
  exact ⟨h.1,h.2⟩

theorem selectedFactor_good_oai (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (id : ℕ) (factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (h : selectedFactor ctx minus one incidence hashes marked clause digits id = some factor) :
    Good vars ctx.u ctx.J factor := by
  unfold selectedFactor at h
  split at h
  · cases h
    exact indicator_good ctx vars hu hJ minus one _ hone (hi id) _ digits
  · split at h
    · cases h
      exact clause_fold_good p t ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J
        minus one _ hone (hi id) clause one hone
    · simp at h

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_good_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_good_oai
