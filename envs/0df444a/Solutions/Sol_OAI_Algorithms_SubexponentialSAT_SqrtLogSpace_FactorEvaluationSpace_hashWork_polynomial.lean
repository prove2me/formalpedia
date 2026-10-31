-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.hashWork_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:21:24.818908+00:00
-- url     : https://prove2.me/submissions/9f7fdeea-20f8-40dd-85d6-d5bed1ef4ffb

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Cost_product_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace_indicatorBudget_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace_result_good

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable normalized sparse coefficient lists. Zero coefficients may stay
in the list; keys are unique, so this does not enlarge the finite index bound.
No equality decision for coefficients or full ambient Boolean table is used. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {K R A : Type*} [DecidableEq K] [AddCommMonoid R]

omit [AddCommMonoid R] in
theorem length_le_card (l : Data K R) (s : Finset K) (hn : (keys l).Nodup)
    (hs : ∀ k ∈ keys l, k ∈ s) : l.length ≤ s.card := by
  have hsub : (keys l).toFinset ⊆ s := by
    intro k hk
    exact hs k (List.mem_toFinset.mp hk)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn] at hcard
  simpa only [keys, List.length_map] using hcard

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

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



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K C R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

omit [DecidableEq K] [CommRing R] in
theorem denoteTable_keys (f : C → R) (entries : List (K × C)) :
    Squarefree.Sparse.keys (denoteTable f entries) = Squarefree.Sparse.keys entries := by
  simp [denoteTable,Squarefree.Sparse.keys,List.map_map,Function.comp_def]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


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

omit [CommSemiring R] in
theorem ValidData.in_universe {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) : ∀ a ∈ keys l, a ∈ indexUniverse vars t J := by
  intro a ha
  rcases h a ha with ⟨hk, hv, hs⟩
  exact (mem_indexUniverse vars t J a).mpr ⟨hk, hs, hv.trans_lt hk.2⟩

omit [CommSemiring R] in
theorem ValidData.length_le {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) (hn : (keys l).Nodup) :
    l.length ≤ t * J * (supportUniverse vars J).card :=
  (length_le_card l _ hn h.in_universe).trans (indexUniverse_card_le vars t J)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

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

theorem decoded_valid {R : Type*} [CommRing R] {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) (h : ∀ a ∈ entries, ValidKey vars u J a.1) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f entries) := by
  intro k hk
  simp only [Squarefree.Sparse.keys,Dictionary.denoteTable,List.map_map,Function.comp_def] at hk
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hk
  exact h a ha

end Product
end SubexponentialSAT.SqrtLog.MomentsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLookupBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial byte and scan bounds for the selected incidence table.
All dictionary payloads are still physically copied and scanned. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.LookupBounds

theorem records_length (entries : List (List Bool × List Bool)) (W P : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hp : ∀ a ∈ entries, a.2.length ≤ P) :
    (Squarefree.Program.lookupRecords entries).length ≤ entries.length*(2*W+2*P+2) := by
  induction entries with
  | nil => simp [Squarefree.Program.lookupRecords,Subexp.SelectorProgram.rawRecords]
  | cons a entries ih =>
    have ha := hk a (by simp)
    have hb := hp a (by simp)
    have ht := ih (fun x hx => hk x (by simp [hx])) (fun x hx => hp x (by simp [hx]))
    simp only [Squarefree.Program.lookupRecords,Subexp.SelectorProgram.rawRecords,
      List.flatMap_cons,List.length_append,Encoding.length_frame,List.length_cons] at *
    nlinarith

theorem incidence_entries_length {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) :
    (incidenceEntries payload i).length = n := by
  simp [incidenceEntries]

theorem incidence_key_length {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) :
    ∀ a ∈ incidenceEntries payload i, a.1.length ≤ n := by
  intro a ha
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
  simp only [Encoding.length_encodeNat]
  exact v.isLt

theorem incidence_payload_length {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) (P : ℕ)
    (hp : ∀ v, (payload i v).length ≤ P) :
    ∀ a ∈ incidenceEntries payload i, a.2.length ≤ P := by
  intro a ha
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
  exact hp v

end SubexponentialSAT.SqrtLog.HashCircuitProgram.LookupBounds

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

theorem decoded_valid {R : Type*} [CommRing R]
    {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (f : RingProgram.Code (Word B) d → R) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f a) :=
  Product.decoded_valid f vars u J a h.valid

theorem length_le {a : List (Product.Entry n B d)} (h : Good vars u J a) :
    a.length ≤ u*J*(Squarefree.Sparse.supportUniverse vars J).card := by
  have hv := h.decoded_valid (fun _ => (0 : ℤ))
  have hn : (Squarefree.Sparse.keys (Dictionary.denoteTable (fun _ => (0 : ℤ)) a)).Nodup := by
    simpa only [Dictionary.denoteTable_keys] using h.nodup
  simpa only [Dictionary.denoteTable,List.length_map] using hv.length_le hn

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial envelopes for the concrete native raw-hash interpreter.
S bounds the number of retained keys; B and d are actual encoded coefficient
width and extension dimension. No arithmetic or parser callback is free. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open Native
open LeafProgram.NativeSemantics

variable {n B d u J S : ℕ} {vars : Finset (Fin n)}

theorem good_length {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (hS : u*J*(Squarefree.Sparse.supportUniverse vars J).card ≤ S) : a.length ≤ S :=
  h.length_le.trans hS

theorem good_keyBound {a : List (Product.Entry n B d)} (h : Good vars u J a) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) a := by
  intro x hx
  have hh := Squarefree.encodeIndex_length_le x.1 (h.valid x hx).1
  omega

theorem good_bytes {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (hS : u*J*(Squarefree.Sparse.supportUniverse vars J).card ≤ S) :
    (Product.bytes a).length ≤ bytesBound B d n u J S := by
  exact (Product.bytes_length_le a (n+u+J) (good_keyBound h)).trans
    (Nat.mul_le_mul_right _ (good_length h hS))

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

theorem totalEnvelope_diagonal (S : ℕ) :
    totalEnvelope S S S S S S S =
      120000*S^8+680660*S^7+1660420*S^6+2270665*S^5+1901221*S^4+
        987023*S^3+298918*S^2+42025*S+304 := by
  dsimp only [totalEnvelope,prepareEnvelope,arithmeticEnvelope,complementEnvelope,
    scaleStepEnvelope,normalizeStepEnvelope,applyEnvelope,loopEnvelope,
    quadraticEnvelope,accumulatorEnvelope,wordEnvelope,mulEnvelope,addEnvelope,
    byteCapacity,MomentsProgram.Product.stepEnvelope,MomentsProgram.Dictionary.codeBranchBudget]
  ring

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform numerical bounds. Z bounds encoded sizes and retained capacity,
not merely the bit length of the original formula. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open HashCircuitProgram

theorem hashServiceBound_mono (B d n u J N k m L Z : ℕ)
    (hB : B ≤ Z) (hd : d ≤ Z) (hn : n ≤ Z) (hu : u ≤ Z) (hJ : J ≤ Z)
    (hN : N ≤ Z) (hk : k ≤ Z) (hm : m ≤ Z) (hL : L ≤ Z) :
    hashServiceBound B d n u J N k m L ≤ hashServiceBound Z Z Z Z Z Z Z Z Z := by
  dsimp only [hashServiceBound,tableBound,Cost.programBound,Cost.rowBound,Cost.payloadBound,
    Cost.literalBound,Cost.negativeBound,Cost.fetchBound,Cost.bytesBound,Cost.productBound,
    Cost.scaleBound,Cost.normalizeBound,
    IdempotentApplyProgram.Bounds.totalEnvelope,IdempotentApplyProgram.Bounds.prepareEnvelope,
    IdempotentApplyProgram.Bounds.arithmeticEnvelope,IdempotentApplyProgram.Bounds.complementEnvelope,
    IdempotentApplyProgram.Bounds.scaleStepEnvelope,IdempotentApplyProgram.Bounds.normalizeStepEnvelope,
    IdempotentApplyProgram.Bounds.applyEnvelope,IdempotentApplyProgram.Bounds.loopEnvelope,
    IdempotentApplyProgram.Bounds.quadraticEnvelope,IdempotentApplyProgram.Bounds.accumulatorEnvelope,
    IdempotentApplyProgram.Bounds.wordEnvelope,IdempotentApplyProgram.Bounds.mulEnvelope,
    IdempotentApplyProgram.Bounds.addEnvelope,IdempotentApplyProgram.Bounds.byteCapacity,
    MomentsProgram.Product.stepEnvelope,MomentsProgram.Dictionary.codeBranchBudget]
  gcongr

theorem hashServiceBound_diagonal (Z : ℕ) :
    hashServiceBound Z Z Z Z Z Z Z Z Z =
      40000*Z^9+360220*Z^8+1367320*Z^7+2879817*Z^6+3704995*Z^5+
      2976138*Z^4+1442724*Z^3+380529*Z^2+42371*Z+376 := by
  unfold hashServiceBound
  rw [IdempotentApplyProgram.Bounds.totalEnvelope_diagonal]
  dsimp only [tableBound,Cost.programBound,Cost.rowBound,Cost.payloadBound,
    Cost.literalBound,Cost.negativeBound,Cost.fetchBound,Cost.bytesBound,Cost.productBound,
    Cost.scaleBound,Cost.normalizeBound,
    MomentsProgram.Product.stepEnvelope,MomentsProgram.Dictionary.codeBranchBudget]
  ring

theorem hashServiceBound_le (B d n u J N k m L Z : ℕ) (hZ : 1 ≤ Z)
    (hB : B ≤ Z) (hd : d ≤ Z) (hn : n ≤ Z) (hu : u ≤ Z) (hJ : J ≤ Z)
    (hN : N ≤ Z) (hk : k ≤ Z) (hm : m ≤ Z) (hL : L ≤ Z) :
    hashServiceBound B d n u J N k m L ≤ 14000000*Z^9 := by
  apply (hashServiceBound_mono B d n u J N k m L Z hB hd hn hu hJ hN hk hm hL).trans
  rw [hashServiceBound_diagonal]
  have hp (k : ℕ) (hk : k ≤ 9) : Z^k ≤ Z^9 := Nat.pow_le_pow_right hZ hk
  have h0 : 1 ≤ Z^9 := by simpa using hp 0 (by decide)
  have h1 : Z ≤ Z^9 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

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

theorem rawHash_good (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d)) :
    Good (∅ : Finset (Fin n)) ctx.u ctx.J (Indicator.rawHash ctx minus one incidence ws) :=
  row_fold_good p t ctx.modulus ctx.cache ctx.table (∅ : Finset (Fin n)) ctx.u ctx.J
    minus one incidence hone hi ws [] Good.nil

omit [Fact p.Prime] in
theorem table_length (ctx : Context p t n d)
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v)) :
    (Squarefree.Program.lookupRecords (Cost.entries incidence)).length ≤
      tableBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) := by
  have hp := fun v => Cost.good_bytes (hi v) (le_refl
    (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J))
  simpa only [Cost.entries,LookupBounds.incidence_entries_length,tableBound] using
    LookupBounds.records_length (Cost.entries incidence) n _
      (LookupBounds.incidence_key_length _ ())
      (LookupBounds.incidence_payload_length _ () _ hp)

theorem productBudget_le (ctx : Context p t n d)
    (seed factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hs : Good (∅ : Finset (Fin n)) ctx.u ctx.J seed)
    (hf : Good (∅ : Finset (Fin n)) ctx.u ctx.J factor) :
    Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor ≤
      56*Cost.bytesBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J)+
      Cost.productBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J)+54 := by
  have hcap := le_refl (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J)
  have bs := Cost.good_bytes hs hcap
  have bf := Cost.good_bytes hf hcap
  have br := Cost.good_bytes (product_good p t ctx.modulus ctx.cache ctx.table
    (∅ : Finset (Fin n)) ctx.u ctx.J seed factor hs hf) hcap
  have hw := Cost.product_le p t ctx.modulus ctx.cache ctx.table hcap seed factor hs hf
  dsimp only [Factor.productBudget]
  omega

theorem hashService_le (ctx : Context p t n d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one) (hs : Good (∅ : Finset (Fin n)) ctx.u ctx.J seed)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits+
      (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
        2*(Squarefree.Program.lookupRecords (Cost.entries incidence)).length+6+
        Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (Indicator.result ctx minus one incidence ws digits)) ≤
      hashServiceBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) k ws.length digits.length := by
  have h1 := indicatorBudget_le ctx hu hJ minus one incidence hone hi ws digits k hk
  have h2 := table_length ctx incidence hi
  have h3 := Cost.good_bytes (rawHash_good ctx minus one incidence hone hi ws)
    (le_refl (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J))
  have h4 := productBudget_le ctx seed _ hs (result_good ctx hu hJ minus one incidence hone hi ws digits)
  unfold hashServiceBound
  omega

theorem empty_capacity_le (u J : ℕ) :
    IdempotentApplyProgram.Bounds.capacity (∅ : Finset (Fin n)) u J ≤ u * J := by
  have h : (Squarefree.Sparse.supportUniverse (∅ : Finset (Fin n)) J).card ≤ 1 := by
    calc
      _ ≤ ((∅ : Finset (Fin n)).powerset).card := Finset.card_filter_le _ _
      _ = 1 := by simp
  simpa only [IdempotentApplyProgram.Bounds.capacity, Nat.mul_one] using
    Nat.mul_le_mul_left (u * J) h

theorem hashWork_polynomial_oai (ctx : Context p t n d)
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits +
      (2 * (Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length +
        2 * (Squarefree.Program.lookupRecords (Cost.entries incidence)).length + 6 +
        Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (Indicator.result ctx minus one incidence ws digits)) ≤
      serviceBudget (baseWidth p t) d n ctx.u ctx.J k ws.length digits.length := by
  have hs := hashService_le ctx hu hJ minus one seed incidence hone hseed hi ws digits k hk
  have hc := empty_capacity_le (n:=n) ctx.u ctx.J
  let Z := inputScale (baseWidth p t) d n ctx.u ctx.J k ws.length digits.length
  exact hs.trans (FactorBounds.hashServiceBound_le (baseWidth p t) d n ctx.u ctx.J
    (IdempotentApplyProgram.Bounds.capacity (∅ : Finset (Fin n)) ctx.u ctx.J)
    k ws.length digits.length Z
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega)
    (by dsimp [Z, inputScale]; omega) (by dsimp [Z, inputScale]; omega))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.hashWork_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.hashWork_polynomial_oai
