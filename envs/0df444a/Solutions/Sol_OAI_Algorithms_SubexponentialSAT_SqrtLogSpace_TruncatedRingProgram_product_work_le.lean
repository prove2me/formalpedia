-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:03:46.448512+00:00
-- url     : https://prove2.me/submissions/5edf8373-cb86-4b48-96b1-bfcd07c5bdbf

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S151

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive dictionary lookup. Dictionary normalization guarantees
unique keys. All key and coefficient bits are scanned by the existing finite
record program; key width, coefficient width and dictionary length are runtime
data and do not affect the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

variable {K C : Type*} [DecidableEq K]

/-- All scan costs, including failed key comparisons, are linear in serialized
key/payload lengths times the number of entries, with explicit query scans. -/
theorem lookupBudget_bound (query : List Bool) (entries : List (List Bool × List Bool))
    (W B : ℕ) (hk : ∀ a ∈ entries, a.1.length ≤ W)
    (hc : ∀ a ∈ entries, a.2.length ≤ B) :
    lookupBudget query entries ≤ entries.length * (17 * W + 9 * query.length + 13 * B + 40) + 1 := by
  induction entries with
  | nil => simp [lookupBudget, SubexponentialSAT.Subexp.SelectorProgram.scanBudget]
  | cons a entries ih =>
    rcases a with ⟨k,c⟩
    have h1 := hk (k,c) (by simp)
    have h2 := hc (k,c) (by simp)
    have h3 := ih (fun a ha => hk a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
    simp only [lookupBudget, SubexponentialSAT.Subexp.SelectorProgram.scanBudget,
      recordCost, List.length_cons] at *
    nlinarith

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem eraseBudget_bound (query : List Bool) (entries : List ByteRecord) (W B : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ B) :
    eraseBudget query entries ≤ entries.length * (28*W+9*query.length+13*B+53)+1 := by
  induction entries with
  | nil => simp [eraseBudget]
  | cons a entries ih =>
    rcases a with ⟨k,c⟩
    have h1 := hk (k,c) (by simp)
    have h2 := hc (k,c) (by simp)
    have h3 := ih (fun a ha => hk a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
    simp only [eraseBudget,List.length_cons] at *
    nlinarith
end SubexponentialSAT.SqrtLog.Squarefree.Program

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

theorem updatedBytes_length_le (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (W C : ℕ) (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C)
    (hq : query.length ≤ W) (hv : coeff.length ≤ C) :
    (updatedBytes entries query coeff).length ≤ (entries.length+1)*(2*W+2*C+2) := by
  have hn : (((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse)).length ≤ entries.length+1 := by
    simpa [Squarefree.Program.erasedEntries] using Nat.add_le_add_right
      (List.length_filter_le (fun a : List Bool × List Bool => decide (a.1 ≠ query)) entries) 1
  have hb := rawEntries_length_le ((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse) W C
    (by intro a ha; simp only [List.mem_cons,List.mem_reverse] at ha; rcases ha with rfl|ha; exact hq
        exact hk a (List.mem_filter.mp ha).1)
    (by intro a ha; simp only [List.mem_cons,List.mem_reverse] at ha; rcases ha with rfl|ha; exact hv
        exact hc a (List.mem_filter.mp ha).1)
  exact hb.trans (Nat.mul_le_mul_right _ hn)

/-- Total insertion work includes both full table scans, copied table bytes,
coefficient addition, and final replacement serialization. -/
theorem insertBudget_le (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (branch W C : ℕ) (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C)
    (hq : query.length ≤ W) (hv : coeff.length ≤ C) :
    insertBudget entries query coeff branch ≤ 200*(entries.length+1)*(W+C+1)+branch := by
  have hr := rawEntries_length_le entries W C hk hc
  have hu := updatedBytes_length_le entries query coeff W C hk hc hq hv
  have hl := Squarefree.Program.lookupBudget_bound query entries W C hk hc
  have he := Squarefree.Program.eraseBudget_bound query entries W C hk hc
  unfold insertBudget finishBudget
  nlinarith [Nat.mul_le_mul_left entries.length hq]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

theorem insertCode_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) :
    (Dictionary.insertCode p t M cache k x seed).length ≤ seed.length+1 := by
  unfold Dictionary.insertCode
  have h := List.length_filter_le (fun a : K × RingProgram.Code (Word (baseWidth p t)) d => decide (a.1 ≠ k)) seed
  simpa [Squarefree.Sparse.erase] using Nat.add_le_add_right h 1

theorem run_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) :
    (run p t M cache source seed).length ≤ source.length+seed.length := by
  induction source generalizing seed with
  | nil => simp [run]
  | cons a source ih =>
    have h := ih (Dictionary.insertCode p t M cache a.1 a.2 seed)
    have hl := insertCode_length p t M cache a.1 a.2 seed
    change (run p t M cache source (Dictionary.insertCode p t M cache a.1 a.2 seed)).length ≤ _
    simp only [List.length_cons]
    omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

theorem insertCode_keyBound (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (W : ℕ)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hk : (key k).length ≤ W) (hs : KeyBound key W seed) :
    KeyBound key W (Dictionary.insertCode p t M cache k x seed) := by
  intro a ha
  simp only [Dictionary.insertCode,List.mem_cons,List.mem_reverse] at ha
  rcases ha with rfl|ha
  · exact hk
  · exact hs a (List.mem_filter.mp ha).1

theorem stepBudget_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (W : ℕ)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hk : (key k).length ≤ W) (hs : KeyBound key W seed) :
    stepBudget p t M cache key seed k x ≤
      220*(seed.length+1)*(W+d*baseWidth p t+1) + Dictionary.codeBranchBudget (baseWidth p t) d := by
  let value := match seed.lookup k with
    | none => x
    | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
  have hv : (RingProgram.flat value).length ≤ d*baseWidth p t := by rw [RingProgram.flat_length]
  have h := Dictionary.insertBudget_le (Squarefree.Program.encodeDictionary key RingProgram.flat seed)
    (key k) (RingProgram.flat value) (Dictionary.codeBranchBudget (baseWidth p t) d) W (d*baseWidth p t)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact hs b hb)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2)) hk hv
  simp only [Squarefree.Program.encodeDictionary,List.length_map] at h
  change 6*(key k).length+11*(RingProgram.flat x).length+15+ _ ≤ _
  rw [RingProgram.flat_length]
  change Dictionary.insertBudget _ _ (RingProgram.flat value) _ ≤ _ at h
  dsimp only [value,Squarefree.Program.encodeDictionary] at h ⊢
  have hmul : 1 * (W + d * baseWidth p t + 1) ≤ (seed.length + 1) * (W + d * baseWidth p t + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  refine le_trans (Nat.add_le_add_left h _) ?_
  nlinarith [hmul, hk]

/-- A uniform polynomial bound for the complete runtime normalization loop. -/
theorem work_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (W N : ℕ)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hs : KeyBound key W source) (hi : KeyBound key W seed)
    (hn : source.length+seed.length ≤ N) :
    work p t M cache key source seed ≤ source.length *
      (220*(N+1)*(W+d*baseWidth p t+1) + Dictionary.codeBranchBudget (baseWidth p t) d + 2) + 1 := by
  induction source generalizing seed with
  | nil => simp [work]
  | cons a source ih =>
    have ha := hs a (by simp)
    have htail : KeyBound key W source := fun b hb => hs b (by simp [hb])
    have hnext := insertCode_keyBound p t M cache key W seed a.1 a.2 ha hi
    have hlen := insertCode_length p t M cache a.1 a.2 seed
    have hcap : source.length + (Dictionary.insertCode p t M cache a.1 a.2 seed).length ≤ N := by
      simp only [List.length_cons] at hn; omega
    have hrec := ih _ htail hnext hcap
    have hstep := stepBudget_le p t M cache key W seed a.1 a.2 ha hi
    have hsize : seed.length+1 ≤ N+1 := by simp only [List.length_cons] at hn; omega
    have hmul := Nat.mul_le_mul_right (W+d*baseWidth p t+1) (Nat.mul_le_mul_left 220 hsize)
    simp only [work,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem stepBudget_bound {n : ℕ} (a b : Index (Fin n)) (t J C : ℕ)
    (ha : a.Kept t J) (hb : b.Kept t J) :
    stepBudget a b t J C ≤ 100*(n+t+J+C+2) := by
  obtain ⟨hau,haz⟩ := ha
  obtain ⟨hbu,hbz⟩ := hb
  simp only [stepBudget,encodeIndex_length,Index.join]
  omega

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem budget_bound {n : ℕ} (a : Index (Fin n)) (t J C : ℕ) (entries : List (Entry n))
    (ha : a.Kept t J) (hb : ∀ b ∈ entries, b.1.Kept t J)
    (hc : ∀ b ∈ entries, b.2.length ≤ C) :
    budget a t J entries ≤ entries.length * (100*(n+t+J+C+2)+2)+1 := by
  induction entries with
  | nil => simp [budget]
  | cons b entries ih =>
    have hs := stepBudget_bound a b.1 t J b.2.length ha (hb b (by simp))
    have hbc := hc b (by simp)
    have ht := ih (fun b h => hb b (by simp [h])) (fun b h => hc b (by simp [h]))
    cases b
    simp only [budget,List.length_cons] at *
    nlinarith

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

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

/-! Cost stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

theorem encode_length {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) :
    (encode key entries).length = 2*keyBits key entries + entries.length*(2*(d*B)+2) := by
  induction entries with
  | nil => simp [encode,keyBits,Program.rawEntries,Program.encodeDictionary]
  | cons a entries ih =>
      simp only [encode_cons,List.length_append,Encoding.length_frame,RingProgram.flat_length,
        ih,keyBits,List.length_cons]
      ring

theorem loopBudget_eq {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) :
    loopBudget key entries = entries.length*(RingScan.serviceMulBudget B d+29*(d*B)+7*d+51) +
      16*keyBits key entries+1 := by
  induction entries with
  | nil => simp [loopBudget,keyBits]
  | cons a entries ih => simp only [loopBudget,stepBudget,ih,keyBits,List.length_cons]; ring

theorem budget_eq {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) :
    budget key entries + 1 =
      entries.length*(RingScan.serviceMulBudget B d+35*(d*B)+7*d+57) +
      22*keyBits key entries+6 := by
  rw [budget,loopBudget_eq,encode_length]
  ring

theorem keyBits_le {C : Type*} (key : K → List Bool) (entries : List (K × C))
    (L : ℕ) (h : ∀ a ∈ entries, (key a.1).length ≤ L) :
    keyBits key entries ≤ entries.length*L := by
  induction entries with
  | nil => simp [keyBits]
  | cons a entries ih =>
      have ha := h a (by simp)
      have ht := ih (fun a ha => h a (by simp [ha]))
      simp only [keyBits,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem budget_le {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d))
    (L : ℕ) (h : ∀ a ∈ entries, (key a.1).length ≤ L) :
    budget key entries + 1 ≤
      entries.length*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+22*L+57)+6 := by
  rw [budget_eq]
  have hk := keyBits_le key entries L h
  have hs := RingScan.serviceMulBudget_le B d
  calc
    _ ≤ entries.length*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+57) +
        22*(entries.length*L)+6 :=
      Nat.add_le_add_right
        (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left 22 hk)) 6
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Semantics stage. -/

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

theorem keptJoin_keyBound {n B d : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) (keptJoin a u J entries) := by
  induction entries with
  | nil => intro b hb; simp [keptJoin] at hb
  | cons b entries ih =>
    intro c hc
    by_cases h : (a.join b.1).Kept u J
    · simp only [keptJoin,h,ite_true, if_true,List.mem_cons] at hc
      rcases hc with rfl|hc
      · have hh := Squarefree.encodeIndex_length_le (a.join b.1) h
        change (Squarefree.encodeIndex (a.join b.1)).length ≤ n+u+J
        omega
      · exact ih c hc
    · simp only [keptJoin,h,ite_false] at hc
      exact ih c hc

theorem block_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    (block p t M cache table u J a right).length ≤ right.length := by
  simpa [block,Squarefree.ScaleProgram.scaled] using
    keptJoin_length a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right)

theorem block_keyBound (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) (block p t M cache table u J a right) := by
  intro b hb
  apply keptJoin_keyBound a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right) b
  simpa [block] using hb

theorem bytes_length_le {n B d : ℕ} (entries : List (Entry n B d)) (W : ℕ)
    (h : Normalize.KeyBound Squarefree.encodeIndex W entries) :
    (bytes entries).length ≤ entries.length*(2*W+2*(d*B)+2) := by
  have hh := Dictionary.rawEntries_length_le
    (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries) W (d*B)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact h b hb)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2))
  simpa [bytes,Normalize.bytes,Squarefree.Program.encodeDictionary] using hh

theorem normalize_keyBound (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {K : Type*} [DecidableEq K] {d : ℕ}
    (key : K → List Bool) (W : ℕ)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hs : Normalize.KeyBound key W source) (hi : Normalize.KeyBound key W seed) :
    Normalize.KeyBound key W (Normalize.run p t M cache source seed) := by
  induction source generalizing seed with
  | nil => exact hi
  | cons a source ih =>
    apply ih _ (fun b hb => hs b (by simp [hb]))
    exact Normalize.insertCode_keyBound p t M cache key W seed a.1 a.2 (hs a (by simp)) hi

theorem stepBudget_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J N : ℕ)
    (a : Entry n (baseWidth p t) d) (right seed : List (Entry n (baseWidth p t) d))
    (ha : a.1.Kept u J) (hr : ∀ b ∈ right, b.1.Kept u J)
    (hi : Normalize.KeyBound Squarefree.encodeIndex (n+u+J) seed)
    (hN : right.length+seed.length ≤ N) :
    stepBudget p t M cache table u J a right seed ≤
      stepEnvelope (baseWidth p t) d n u J N right.length := by
  let W := n+u+J
  let C := d*baseWidth p t
  let scaled := Squarefree.ScaleProgram.scaled p t M cache table a.2 right
  let source := block p t M cache table u J a right
  have hk : (Squarefree.encodeIndex a.1).length ≤ W := by
    have h := Squarefree.encodeIndex_length_le a.1 ha; dsimp [W]; omega
  have hright : Normalize.KeyBound Squarefree.encodeIndex W right := by
    intro b hb; have h := Squarefree.encodeIndex_length_le b.1 (hr b hb); dsimp [W]; omega
  have hscaled : Normalize.KeyBound Squarefree.encodeIndex W scaled := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact hright c hc
  have hsl : scaled.length = right.length := by simp [scaled,Squarefree.ScaleProgram.scaled]
  have hbl : source.length ≤ right.length := block_length p t M cache table u J a right
  have hbs : Normalize.KeyBound Squarefree.encodeIndex W source := block_keyBound p t M cache table u J a right
  have hbr := bytes_length_le right W hright
  have hbc := bytes_length_le scaled W hscaled
  have hbb := bytes_length_le source W hbs
  have hb := Squarefree.ScaleProgram.budget_le Squarefree.encodeIndex right W hright
  have hm := Squarefree.KeyMapProgram.budget_bound a.1 u J C (coefficientBytes scaled) ha
    (by intro b hb; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
        obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc; exact hr e he)
    (by intro b hb; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb; exact le_of_eq (RingProgram.flat_length c.2))
  have hn := Normalize.work_le p t M cache Squarefree.encodeIndex W N source seed hbs hi (by omega)
  have hnb := Nat.mul_le_mul_right
    (220*(N+1)*(W+C+1)+Dictionary.codeBranchBudget (baseWidth p t) d+2) hbl
  have hbb' := Nat.mul_le_mul_right (2*W+2*C+2) hbl
  simp only [coefficientBytes,List.length_map] at hm
  rw [hsl] at hbc hm
  unfold stepBudget stepEnvelope
  simp only [RingProgram.flat_length]
  dsimp [scaled,source,W,C] at *
  simp only [coefficientBytes]
  nlinarith only [hk,hbr,hbc,hbb,hb,hm,hn,hnb,hbb']

/-- Quadratic record accumulation is paid explicitly; no sparse lookup is free. -/
theorem work_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J N : ℕ)
    (left right seed : List (Entry n (baseWidth p t) d))
    (hl : ∀ a ∈ left, a.1.Kept u J) (hr : ∀ b ∈ right, b.1.Kept u J)
    (hi : Normalize.KeyBound Squarefree.encodeIndex (n+u+J) seed)
    (hN : left.length*right.length+seed.length ≤ N) :
    work p t M cache table u J left right seed ≤
      left.length*(stepEnvelope (baseWidth p t) d n u J N right.length+2)+1 := by
  induction left generalizing seed with
  | nil => simp [work]
  | cons a left ih =>
    let next := Normalize.run p t M cache (block p t M cache table u J a right) seed
    have hs := Normalize.run_length p t M cache (block p t M cache table u J a right) seed
    have hb := block_length p t M cache table u J a right
    have hn : left.length*right.length+next.length ≤ N := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hN
      dsimp [next]; omega
    have hnext := normalize_keyBound p t M cache Squarefree.encodeIndex (n+u+J)
      (block p t M cache table u J a right) seed (block_keyBound p t M cache table u J a right) hi
    have hrec := ih next (fun a ha => hl a (by simp [ha])) hnext hn
    have hstep := stepBudget_le p t M cache table u J N a right seed (hl a (by simp)) hr hi
      (by simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hN; omega)
    dsimp only [next] at hrec
    simp only [work,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

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

namespace Product

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

theorem product_work_le_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good ∅ u J left) (hr : Good ∅ u J right) :
    Product.work p t M cache table u J left right [] + 2 ≤
      productBudget n (baseWidth p t) d u J := by
  have hleft := empty_length_le hl
  have hright := empty_length_le hr
  have hw := Product.work_le p t M cache table u J ((u * J) ^ 2) left right []
    (fun a ha => (hl.valid a ha).1) (fun b hb => (hr.valid b hb).1)
    (by simp [Normalize.KeyBound]) (by simpa [pow_two] using Nat.mul_le_mul hleft hright)
  have henv : Product.stepEnvelope (baseWidth p t) d n u J ((u * J) ^ 2) right.length ≤
      Product.stepEnvelope (baseWidth p t) d n u J ((u * J) ^ 2) (u * J) := by
    dsimp [Product.stepEnvelope]
    gcongr
  have htotal := Nat.mul_le_mul hleft (Nat.add_le_add_right henv 2)
  unfold productBudget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le_oai
