-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:37:14.645323+00:00
-- url     : https://prove2.me/submissions/ee448d00-372a-41bb-bfd9-bb546cbbb2b3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S145
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_accumulate_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram_product_work_le

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

namespace Good

variable {n B d u J : ℕ} {vars : Finset (Fin n)}

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

theorem product_good (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good vars u J left) (hr : Good vars u J right) :
    Good vars u J (Product.run p t M cache table u J left right []) :=
  ⟨Product.run_valid p t M cache table vars u J left right [] hl.valid hr.valid (by simp),
    Product.run_nodup p t M cache table u J left right [] (by simp [Squarefree.Sparse.keys])⟩


end NativeValidity

variable {V R : Type*} [DecidableEq V] [CommRing R]

omit [DecidableEq V] in
/-- Empty formal support has at most one possible support, also when `J = 0`. -/
theorem empty_support_card_le (J : ℕ) :
    (Squarefree.Sparse.supportUniverse (∅ : Finset V) J).card ≤ 1 := by
  calc
    _ ≤ ((∅ : Finset V).powerset).card := Finset.card_filter_le _ _
    _ = 1 := by simp

theorem empty_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) : a.length ≤ u * J := by
  exact ha.length_le.trans (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (u * J)
      (empty_support_card_le (V := Fin n) J))

theorem empty_bytes_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) :
    (Product.bytes a).length ≤ u * J * (2 * (u + J + n) + 2 * (d * B) + 2) := by
  exact (Product.bytes_length_le a (u + J + n)
    (fun x hx => Squarefree.encodeIndex_length_le x.1 (ha.valid x hx).1)).trans
      (Nat.mul_le_mul_right _ (empty_length_le ha))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorProductSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original concrete factor accumulator, with empty correction support.
All three tape moves and the original sparse product call are charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram MomentsProgram

/-- The same executed accumulator returns a valid bounded dictionary and an
exact frame for every other stack. Its polynomial local time controls every
prefix, including all caller storage and all native arithmetic temporaries. -/
theorem accumulate_run_space_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (seed factor : List (Product.Entry n (baseWidth p t) d))
    (hs : TruncatedRingProgram.Good ∅ u J seed) (hf : TruncatedRingProgram.Good ∅ u J factor) (a : Factor.Data)
    (hlow : Factor.lowReady a (Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (hseed : a.stacks 151 = Product.bytes seed)
    (hfactor : a.stacks 67 = Product.bytes factor)
    (h61 : a.stacks 61 = []) (h70 : a.stacks 70 = []) (h159 : a.stacks 159 = []) :
    let result := Product.run p t M cache table u J seed factor []
    let program := compiled Factor.accumulate 67 151
    ∃ steps b, steps ≤ budget n (baseWidth p t) d u J ∧ TruncatedRingProgram.Good ∅ u J result ∧
      Eval Factor.accumulate steps a b ∧
      b.stacks = Function.update (Function.update a.stacks 67 []) 151 (Product.bytes result) ∧
      (Product.bytes result).length ≤ byteBound n (baseWidth p t) d u J ∧
      Trace program (steps + 1) (a.withPC (some program.entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ stackBits a.stacks + budget n (baseWidth p t) d u J + 1 := by
  dsimp only
  obtain ⟨steps, b, hsteps, he, hb⟩ := Factor.accumulate_eval p t M cache hz table
    degree width hd hw u J seed factor a hlow hseed hfactor h61 h70 h159
  have hgood := TruncatedRingProgram.product_good p t M cache table ∅ u J seed factor hs hf
  have hslen := TruncatedRingProgram.empty_bytes_length_le hs
  have hflen := TruncatedRingProgram.empty_bytes_length_le hf
  have hrlen := TruncatedRingProgram.empty_bytes_length_le hgood
  have hwork := TruncatedRingProgram.product_work_le p t M cache table u J seed factor hs hf
  have hbound : steps ≤ budget n (baseWidth p t) d u J := by
    dsimp only [budget, byteBound]
    omega
  refine ⟨steps, b, hbound, hgood, he, hb, hrlen, compiled_halt_trace he 67 151, ?_⟩
  intro prefixSteps intermediate hp htrace
  have hgrowth := trace_dataBits (compiled Factor.accumulate 67 151) htrace
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space_oai
