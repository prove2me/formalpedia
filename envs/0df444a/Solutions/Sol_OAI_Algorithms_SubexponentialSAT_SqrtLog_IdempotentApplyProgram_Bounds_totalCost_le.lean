-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.totalCost_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:53:29.062652+00:00
-- url     : https://prove2.me/submissions/388430d7-f802-45b4-8c86-014468e5a776

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Bounds_loopCost_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Bounds_prepareCost_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

 theorem rawEntries_length_le (entries : List (List Bool × List Bool)) (W C : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C) :
    (Squarefree.Program.rawEntries entries).length ≤ entries.length * (2*W+2*C+2) := by
  induction entries with
  | nil => simp [Squarefree.Program.rawEntries]
  | cons a entries ih =>
    have h1 := hk a (by simp)
    have h2 := hc a (by simp)
    have h3 := ih (fun b hb => hk b (by simp [hb])) (fun b hb => hc b (by simp [hb]))
    simp only [Squarefree.Program.rawEntries,List.length_append,Encoding.length_frame,List.length_cons]
    nlinarith

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeIndex_length_le {n t J : ℕ} (a : Index (Fin n))
    (h : a.Kept t J) : (encodeIndex a).length ≤ t + J + n := by
  rw [encodeIndex_length]
  obtain ⟨hu, hz⟩ := h
  omega

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

theorem bytes_length_le {n B d : ℕ} (entries : List (Entry n B d)) (W : ℕ)
    (h : Normalize.KeyBound Squarefree.encodeIndex W entries) :
    (bytes entries).length ≤ entries.length*(2*W+2*(d*B)+2) := by
  have hh := Dictionary.rawEntries_length_le
    (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries) W (d*B)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact h b hb)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2))
  simpa [bytes,Normalize.bytes,Squarefree.Program.encodeDictionary] using hh

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

theorem valid_keyBound {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) (h : Valid vars u J entries) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) entries := by
  intro a ha
  have hh := Squarefree.encodeIndex_length_le a.1 (h a ha).1
  omega

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte order for descending Horner application. A single whole-tape reversal
puts the last digit first and each digit's coefficients in c,b,a order. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open SubexpQuarticRing

theorem triplesTape_reverse {B : ℕ} (vs : List (Triple (Word B))) :
    (triplesTape vs).reverse=descendingTape vs.reverse := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp [triplesTape,descendingTape,tripleTape,List.reverse_cons,List.map_append,
      List.flatten_append,List.reverse_append]
    simpa [triplesTape,descendingTape,List.map_reverse,List.append_assoc] using ih


theorem descendingTape_cons {B : ℕ} (v : Triple (Word B)) (vs : List (Triple (Word B))) :
    descendingTape (v::vs)=v.c.val.reverse++(v.b.val.reverse++(v.a.val.reverse++descendingTape vs)) := by
  simp [descendingTape,List.append_assoc]

theorem descendingTape_length {B : ℕ} (vs : List (Triple (Word B))) :
    (descendingTape vs).length=3*B*vs.length := by
  induction vs with
  | nil => simp [descendingTape]
  | cons v vs ih =>
    rw [descendingTape_cons]
    simp only [List.length_append,List.length_reverse, v.a.property,v.b.property,v.c.property,List.length_cons,ih,Nat.mul_add,Nat.mul_one]
    omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

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

omit [Fact (Nat.Prime p)] in
theorem good_bounded (ctx : Context p t n d) (vars : Finset (Fin n))
    (a : Stored p t (n:=n) (d:=d)) (ha : Good vars ctx.u ctx.J a) :
    Bounded ctx vars a := ⟨ha.1, length_le_capacity vars ctx.u ctx.J a ha⟩

omit [Fact (Nat.Prime p)] in
theorem bounded_bytes (ctx : Context p t n d) (vars : Finset (Fin n))
    (a : Stored p t (n:=n) (d:=d)) (ha : Bounded ctx vars a) :
    (Product.bytes a).length ≤
      byteCapacity n (baseWidth p t) d ctx.u ctx.J (capacity vars ctx.u ctx.J) :=
  (Product.bytes_length_le a (n+ctx.u+ctx.J)
    (valid_keyBound vars ctx.u ctx.J a ha.1)).trans (Nat.mul_le_mul_right _ ha.2)

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

theorem triplesTape_length {B : ℕ} (vs : List (Triple (Word B))) :
    (triplesTape vs).length=3*B*vs.length := by
  have h := congrArg List.length (triplesTape_reverse vs)
  simpa only [List.length_reverse,descendingTape_length] using h

theorem applyLoopCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h g : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (hg : Bounded ctx vars g)
    (vs : List (Triple (RingProgram.ScalarCode p t))) (key : List Bool) :
    applyLoopCost ctx h g vs key ≤
      applyEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) vs.length key.length := by
  have hn := good_nil (B:=baseWidth p t) (d:=d) vars ctx.u ctx.J
  have ho := loopResult_good ctx vars hu hJ h g hh.1 hg.1 vs.reverse [] hn
  have bo := bounded_bytes ctx vars (loopResult ctx h g vs.reverse []) (good_bounded ctx vars _ ho)
  have bg := bounded_bytes ctx vars g hg
  have bl := loopCost_le ctx vars hu hJ h g hh hg vs.reverse [] (good_bounded ctx vars _ hn)
  rw [List.length_reverse] at bl
  dsimp only [applyLoopCost,applyEnvelope]
  rw [triplesTape_length]
  nlinarith

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierKey. -/

/-! Construction and application of the U monomial by actual native instructions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native


theorem uKey_encode (n : ℕ) :
    Squarefree.encodeIndex (uKey n)=true :: List.replicate (n+2) false := by
  simp [uKey,Squarefree.encodeIndex,Encoding.encodeNat,Squarefree.encodeMask,
    List.ofFn_const,List.replicate_succ]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier


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

theorem totalCost_le_oai (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (ho : Good vars ctx.u ctx.J one)
    (vs : List (Triple (RingProgram.ScalarCode p t))) :
    prepareCost ctx minus h one+
      applyLoopCost ctx h (prepared ctx minus h one) vs (Squarefree.encodeIndex (uKey n))+1 ≤
      totalEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) vs.length := by
  have hp := prepareCost_le ctx vars minus h one hh ho
  have hg := prepared_bounded ctx vars minus h one hh.1 ho
  have ha := applyLoopCost_le ctx vars hu hJ h (prepared ctx minus h one) hh hg vs
    (Squarefree.encodeIndex (uKey n))
  have hk : (Squarefree.encodeIndex (uKey n)).length=n+3 := by simp [uKey_encode]
  rw [hk] at ha
  exact Nat.add_le_add_right (Nat.add_le_add hp ha) 1

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.totalCost_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.totalCost_le_oai
