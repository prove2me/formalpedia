-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.staged_rounds_time_hashCalls
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:13:11.001488+00:00
-- url     : https://prove2.me/submissions/04fe6b2d-6d3d-4ab9-9c8e-3d9ac778264d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DyadicWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A positive dyadic width for bounded tuple enumeration, including zero. -/

namespace SubexponentialSAT.DyadicWidth

theorem two_pow_width_le (m : ℕ) : 2 ^ width m ≤ 2 * (m + 1) := by
  by_cases hm : m = 0
  · subst m
    norm_num [width]
  · have h := Nat.pow_log_le_self 2 hm
    unfold width
    rw [pow_succ]
    omega

theorem width_le_succ (m : ℕ) : width m ≤ m + 1 := by
  by_cases hm : m = 0
  · subst m
    norm_num [width]
  · have h := Nat.log_lt_self 2 hm
    unfold width
    omega

end SubexponentialSAT.DyadicWidth

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem digits_two_eq_map_toNat (a : ℕ) :
    Nat.digits 2 a = a.bits.map Bool.toNat := by
  rw [Nat.digits_two_eq_bits]
  induction a.bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all

@[simp] theorem countWord_decode (a : ℕ) :
    Nat.ofDigits 2 ((countWord a).map Bool.toNat) = a := by
  by_cases h : a = 0
  · subst a
    rfl
  · rw [countWord, ite_eq_right h, ← digits_two_eq_map_toNat]
    exact Nat.ofDigits_digits 2 a

@[simp] theorem countWord_toNat (a : ℕ) : BinaryArithmetic.toNat (countWord a) = a := by
  have h (word : List Bool) :
      BinaryArithmetic.toNat word = Nat.ofDigits 2 (word.map Bool.toNat) := by
    induction word with
    | nil => rfl
    | cons b word ih =>
        cases b <;> simp [BinaryArithmetic.toNat, BinaryArithmetic.bitVal, ih,
          Nat.ofDigits]
  rw [h, countWord_decode]

theorem countWord_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (countWord a).length ≤ n + 1 := by
  by_cases h : a = 0
  · simp [countWord, h]
  · simpa only [countWord, ite_eq_right h, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
The hash stream visits binary payloads in increasing unsigned order and reduces
each indexed ternary digit modulo3*m before the existing row assembler. Every
original candidate is attained and unchanged by normalization. Extra normalized
duplicates preserve the minimum. Visits are bounded by the square of the old family.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily

/-- All binary trials, including duplicate decoded rows, fit a fixed square
of the original explicit ternary family count. -/
theorem candidate_count_le_square {m : ℕ} (hm : 0 < m) (depth : ℕ) :
    2 ^ payloadWidth m depth ≤ ((3 * m) ^ depth) ^ 2 := by
  have hbase : 2 ^ digitWidth m ≤ (3 * m) ^ 2 := by
    have h := DyadicWidth.two_pow_width_le (3 * m)
    dsimp [digitWidth]
    nlinarith
  calc
    2 ^ payloadWidth m depth = (2 ^ digitWidth m) ^ depth := by
      rw [payloadWidth, Nat.mul_comm, pow_mul]
    _ ≤ ((3 * m) ^ 2) ^ depth := Nat.pow_le_pow_left hbase depth
    _ = ((3 * m) ^ depth) ^ 2 := by simp [← pow_mul, Nat.mul_comm]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

namespace Normalize

open OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives



theorem budget_polynomial (m depth : ℕ) :
    budget m depth + 1 ≤
      6000 * (depth + 1) * (HashCandidates.digitWidth m + 1) ^ 2 := by
  unfold budget HashCandidates.payloadWidth
  nlinarith [Nat.zero_le (depth * HashCandidates.digitWidth m ^ 2)]


end Normalize

namespace Leaf

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open scoped BigOperators

theorem budget_polynomial (m depth : ℕ) :
    budget m depth + 1 ≤ 6200 * (depth + 1) * (HashCandidates.digitWidth m + 1) ^ 2 := by
  have hn := Normalize.budget_polynomial m depth
  have hp : HashCandidates.payloadWidth m depth + HashCandidates.digitWidth m + 1 ≤
      (depth + 1) * (HashCandidates.digitWidth m + 1) ^ 2 := by
    unfold HashCandidates.payloadWidth
    nlinarith
  unfold budget
  nlinarith

end Leaf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

namespace NativeRound

theorem round_budget_le (attemptCost scoreWidth payloadWidth : ℕ) :
    roundBudget attemptCost scoreWidth payloadWidth ≤
      400 * (2 ^ payloadWidth) * (attemptCost + scoreWidth + payloadWidth + 1) := by
  have hpositive : 1 ≤ 2 ^ payloadWidth := by
    have hp : 0 < (2 : ℕ) ^ payloadWidth := pow_pos (by decide) _
    omega
  unfold roundBudget
  nlinarith [Nat.mul_le_mul_left attemptCost hpositive,
    Nat.mul_le_mul_left scoreWidth hpositive,
    Nat.mul_le_mul_left payloadWidth hpositive]

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact reference values for the payload and full natural score physically
produced by the native candidate attempt. These accessors are proof objects;
the executable program retains only the current word and running minimum. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

/-- Canonical alphabet width never exceeds an actual word encoding 3*m. -/
theorem digitWidth_le_word_length {m : ℕ} (hm : 0 < m) (word : List Bool)
    (hvalue : CounterPrograms.value word = 3 * m) :
    HashCandidates.digitWidth m ≤ word.length := by
  have hlt : 3 * m < 2 ^ word.length := by
    simpa only [hvalue] using ExecCNFTupleOdometer.value_lt_power_length word
  have hlog := Nat.log_lt_of_lt_pow (by omega : 3 * m ≠ 0) hlt
  unfold HashCandidates.digitWidth DyadicWidth.width
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

theorem outputGrowth_le (width : List Bool → ℕ) (records : List (List Bool))
    (W : ℕ) (hW : ∀ bits ∈ records, width bits ≤ W) :
    outputGrowth width records ≤ records.length*(W+1) := by
  induction records with
  | nil => simp [outputGrowth]
  | cons bits rest ih =>
      have hw := hW bits (by simp)
      have hr := ih (fun b hb => hW b (by simp [hb]))
      simp only [outputGrowth,List.map_cons,List.sum_cons,List.length_cons] at *
      nlinarith


open LeafOuterProgram

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial overhead for the actual marked-mass command. The query
cost bound is charged for every original clause reference, including the last. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassBounds

open SqrtLog HashMassAdapter

/-- The actual generated unary index has at most m bits when its index is
strictly below m. No exponential reference table is present. -/
theorem reference_length (m : ℕ) (bits : List Bool)
    (hb : bits ∈ RowSelectionProgram.Index.alphabet m) : bits.length ≤ m := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  have hj' : j < m := by simpa using hj
  simp only [Encoding.length_encodeNat]
  omega

theorem reference_bound (f : List Bool → ℕ) (m B : ℕ)
    (hf : ∀ e : Fin m, f (Encoding.encodeNat e.val) ≤ B) :
    ∀ bits ∈ RowSelectionProgram.Index.alphabet m, f bits ≤ B := by
  intro bits hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  exact hf ⟨j, by simpa using hj⟩

theorem input_size_le (width : List Bool → ℕ) (m W : ℕ)
    (hw : ∀ e : Fin m, width (Encoding.encodeNat e.val) ≤ W) :
    valueInputSize width (RowSelectionProgram.Index.alphabet m) ≤ m * (m + W + 1) := by
  have h := List.sum_le_card_nsmul
    ((RowSelectionProgram.Index.alphabet m).map fun bits => bits.length + width bits + 1)
    (m + W + 1) (by
      intro x hx
      obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hx
      have hl := reference_length m bits hb
      have hw' := reference_bound width m W hw bits hb
      omega)
  simp only [valueInputSize, List.length_map, RowSelectionProgram.Index.alphabet_length,
    nsmul_eq_mul] at h ⊢
  omega

theorem query_sum_le (queryCost : List Bool → ℕ) (m T : ℕ)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    ((RowSelectionProgram.Index.alphabet m).map queryCost).sum ≤ m * T := by
  have h := List.sum_le_card_nsmul
    ((RowSelectionProgram.Index.alphabet m).map queryCost) T
    (by
      intro x hx
      obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hx
      exact reference_bound queryCost m T ht bits hb)
  simpa using h

/-- A fixed cube suffices for all paid reference production, parser, additions,
normalization, routing and cleanup around the uniformly charged query cost. -/
theorem massBudget_le (a : HashMassAdapter.Data) (queryCost width : List Bool → ℕ)
    (m W D T : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (hw : ∀ e : Fin m, width (Encoding.encodeNat e.val) ≤ W)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    massBudget a queryCost width m ≤ 1000 * (m + W + D + 1) ^ 3 * (T + 1) := by
  let S := m + W + D + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hmS : m ≤ S := by dsimp [S]; omega
  have hm1S : m + 1 ≤ S := by dsimp [S]; omega
  have hWS : W + 1 ≤ S := by dsimp [S]; omega
  have hDS : D + 1 ≤ S := by dsimp [S]; omega
  have hsumS : m + W + 1 ≤ S := by dsimp [S]; omega
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have hS3 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h1S3 : 1 ≤ S ^ 3 := hS.trans (hS2.trans hS3)
  have hLS : (a.stacks 782).length + 1 ≤ S := by omega
  have hcore : CounterConversions.coreBound (a.stacks 782) ≤ 26 * S ^ 2 := by
    have hprod : (m + 1) * ((a.stacks 782).length + 1) ≤ S ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hm1S hLS
    rw [CounterConversions.coreBound, hm]
    nlinarith only [hprod, hS2, hS, hmS, hLS]
  have hroute : LeafOuterProgram.routeCost (782,0) a ≤ 17 * S ^ 2 := by
    simp only [LeafOuterProgram.routeCost]
    nlinarith only [h0, h782, hDS, hS2, hS]
  have hreference : LeafOuterNative.References.budget (a.stacks 782) ≤ 78 * S ^ 2 := by
    have hmsquare : m * m ≤ S * S := Nat.mul_le_mul hmS hmS
    unfold LeafOuterNative.References.budget
    rw [hm]
    nlinarith only [hcore, hmsquare, hmS, hS2, hS]
  have hsetup : LeafOuterProgram.routeCost (782,0) a +
      LeafOuterNative.References.budget (a.stacks 782) + 1 ≤ 100 * S ^ 2 := by nlinarith only [hroute, hreference, hS, hS2]
  have hin := input_size_le width m W hw
  have hinput : valueInputSize width (RowSelectionProgram.Index.alphabet m) ≤ S ^ 2 := by
    have hp : m * (m + W + 1) ≤ S * S := Nat.mul_le_mul hmS hsumS
    exact hin.trans (by simpa only [pow_two] using hp)
  have hq := query_sum_le queryCost m T ht
  have hqS : ((RowSelectionProgram.Index.alphabet m).map queryCost).sum ≤ S * T :=
    hq.trans (Nat.mul_le_mul_right T hmS)
  have hval : valueBudget queryCost width (RowSelectionProgram.Index.alphabet m) [] ≤
      4 + S * T + S * (22 * S ^ 2 + 26) := by
    unfold valueBudget
    simp only [List.length_nil, Nat.zero_add, RowSelectionProgram.Index.alphabet_length]
    have hp : m * (22 * valueInputSize width (RowSelectionProgram.Index.alphabet m) + 26) ≤
        S * (22 * S ^ 2 + 26) := Nat.mul_le_mul hmS (by omega)
    exact Nat.add_le_add (Nat.add_le_add_left hqS 4) hp
  have hg := outputGrowth_le width (RowSelectionProgram.Index.alphabet m) W
    (reference_bound width m W hw)
  have hgS : outputGrowth width (RowSelectionProgram.Index.alphabet m) ≤ S ^ 2 := by
    have hp : m * (W + 1) ≤ S * S := Nat.mul_le_mul hmS hWS
    simp only [RowSelectionProgram.Index.alphabet_length] at hg
    exact hg.trans (by simpa only [pow_two] using hp)
  have hfinish : 50 * (outputGrowth width (RowSelectionProgram.Index.alphabet m) +
      (a.stacks 769).length + 1) ≤ 150 * S ^ 2 := by
    nlinarith only [hgS, h769, hDS, hS2, hS]
  have hST : S * T ≤ S ^ 3 * T := Nat.mul_le_mul_right T (hS2.trans hS3)
  change massBudget a queryCost width m ≤ 1000 * S ^ 3 * (T + 1)
  unfold massBudget
  nlinarith only [hsetup, hval, hfinish, hST, hS2, hS3, h1S3, hS]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyBudgets
open SqrtLog HashGreedyProgram

/-- The explicit old controller pays every scored candidate, independently of
whether the candidate wins. -/
theorem controller_lower (B C cost familyBits count rounds : ℕ) :
    rounds * count * (cost + B + C + 1) ≤
      HashSelectProgram.controllerBudget B C cost familyBits count rounds := by
  unfold HashSelectProgram.controllerBudget HashSelectProgram.roundsBudget
    HashSelectProgram.roundBudget HashSelectProgram.selectBudget HashSelectProgram.loadBudget
  nlinarith only [Nat.zero_le (rounds * familyBits), Nat.zero_le (rounds * count * cost),
    Nat.zero_le (rounds * count * B), Nat.zero_le (rounds * count * C)]

/-- All actual seed and streamed candidate attempts are paid. The retained
payload count can be exponentially large, but appears only in time. -/
theorem rounds_le_square (attempt B C oldCost oldWidth familyBits count rounds factor : ℕ)
    (hcount : 1 ≤ count) (hfamily : 2 ^ C ≤ count ^ 2)
    (hC : C ≤ oldWidth)
    (hattempt : attempt ≤ factor * (oldCost + B + oldWidth + 1)) :
    HashSelectProgram.roundsBudget (NativeRound.roundBudget attempt B C) rounds ≤
      402 * (factor + 1) * count *
        (HashSelectProgram.controllerBudget B oldWidth oldCost familyBits count rounds + 1) := by
  let X := oldCost + B + oldWidth + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hsum : attempt + B + C + 1 ≤ (factor + 1) * X := by
    dsimp [X] at *
    nlinarith only [hattempt, hC, Nat.zero_le oldCost]
  have hround := (NativeRound.round_budget_le attempt B C).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 400 hfamily) hsum)
  have hlower := controller_lower B oldWidth oldCost familyBits count rounds
  change rounds * count * X ≤ _ at hlower
  have hprod := Nat.mul_le_mul_left (400 * (factor + 1) * count) hlower
  have hr := Nat.mul_le_mul_left rounds hround
  have hrounds : rounds ≤ rounds * count * X := by
    have h := Nat.mul_le_mul hcount hX
    nlinarith only [Nat.mul_le_mul_left rounds h]
  unfold HashSelectProgram.roundsBudget
  nlinarith only [hprod, hr, hrounds, hcount,
    Nat.mul_le_mul_left (rounds * count * X) (show 1 ≤ factor + 1 by omega),
    Nat.mul_le_mul_left (rounds * count * X) hcount,
    Nat.zero_le (factor * count)]

/-- Paid preparation, every marked query, and full score padding have a fixed
polynomial overhead in retained parameters and the uniform query cost. -/
theorem attempt_polynomial (a : HashMassAdapter.Data) (queryCost width : List Bool → ℕ)
    (m depth W D T B : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (hw : ∀ e : Fin m, width (Encoding.encodeNat e.val) ≤ W)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    15 * HashCandidateProgram.Leaf.budget m depth +
      HashMassAdapter.massBudget a queryCost width m + 23 * B + 20 ≤
        2000000 * (m + depth + W + D + B + 1) ^ 3 * (T + 1) := by
  let S := m + depth + W + D + B + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hd : depth + 1 ≤ S := by dsimp [S]; omega
  have hmS : m + 1 ≤ S := by dsimp [S]; omega
  have hBS : B ≤ S := by dsimp [S]; omega
  have hmass := HashMassBounds.massBudget_le a queryCost width m W D T hm h0 h782 h769 hw ht
  have hmassS : HashMassAdapter.massBudget a queryCost width m ≤ 1000 * S ^ 3 * (T + 1) :=
    hmass.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by dsimp [S]; omega) 3)))
  have hwidth : HashCandidates.digitWidth m + 1 ≤ 3 * S := by
    have h := DyadicWidth.width_le_succ (3 * m)
    change HashCandidates.digitWidth m ≤ 3 * m + 1 at h
    omega
  have hprep := HashCandidateProgram.Leaf.budget_polynomial m depth
  have hprepS : HashCandidateProgram.Leaf.budget m depth ≤ 55800 * S ^ 3 := by
    have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 6200 hd)
      (Nat.pow_le_pow_left hwidth 2)
    nlinarith only [hprep, hp]
  have hS3 : S ≤ S ^ 3 := (Nat.le_self_pow (by omega) S).trans
    (Nat.pow_le_pow_right hS (show 2 ≤ 3 by omega))
  have hST : S ^ 3 ≤ S ^ 3 * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
  change _ ≤ 2000000 * S ^ 3 * (T + 1)
  nlinarith only [hmassS, hprepS, hBS, hS, hS3, hST]


/-- The named actual attempt includes the all-mark mass collector and the
common-width score padding after the native normalizer. -/
theorem attemptBudget_polynomial (a : HashMassAdapter.Data) (queryCost : List Bool → ℕ)
    (n m depth D T : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    HashGreedyExecution.attemptBudget a n m depth queryCost ≤
      2000000 * (m + depth + (n + 1) + D + HashSelect.loopCap n m + 1) ^ 3 * (T + 1) := by
  have h := attempt_polynomial a queryCost (fun _ => n + 1) m depth (n + 1) D T
    (HashSelect.loopCap n m) hm h0 h782 h769 (fun _ => le_rfl) ht
  unfold HashGreedyExecution.attemptBudget
  omega

/-- The old explicit family-generation term alone dominates the square of
its original ternary candidate count. -/
theorem family_square_le_polynomial (count depth rounds : List Bool) (B C cost : ℕ)
    (hc : 2 ≤ CounterPrograms.value count) :
    (CounterPrograms.value count ^ CounterPrograms.value depth) ^ 2 ≤
      Execution.Hash.polynomialBudget count depth rounds B C cost := by
  let A := CounterPrograms.value count
  let P := CounterPrograms.value depth
  let M := A ^ P
  have hcoef : 1 ≤ 400 * (P + 1) * A ^ 2 * ((P + 1) * count.length + 1) := by
    have hA : 1 ≤ A := by dsimp [A]; omega
    have hApos : 0 < A := by omega
    have hp : 0 < 400 * (P + 1) * A ^ 2 * ((P + 1) * count.length + 1) := by positivity
    omega
  have hprod := Nat.mul_le_mul_right (M ^ 2) hcoef
  change M ^ 2 ≤ _
  unfold Execution.Hash.polynomialBudget
  change M ^ 2 ≤ _ + 400 * (P + 1) * A ^ 2 * M ^ 2 * ((P + 1) * count.length + 1) + 15 + _
  nlinarith only [hprod]

/-- Replacing materialized candidates by the complete binary stream costs a
fixed square of the old worst-case budget. No successful-run time is used. -/
theorem rounds_le_polynomial (count depth rounds : List Bool)
    (m B cost attempt factor : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3 * m)
    (hattempt : attempt ≤ factor * (cost + B + CounterPrograms.value depth * count.length + 1)) :
    HashSelectProgram.roundsBudget
      (NativeRound.roundBudget attempt B
        (HashCandidates.payloadWidth m (CounterPrograms.value depth)))
      (CounterPrograms.value rounds) ≤
        402 * (factor + 1) *
          (Execution.Hash.polynomialBudget count depth rounds B
            (CounterPrograms.value depth * count.length) cost + 1) ^ 2 := by
  let P := CounterPrograms.value depth
  let M := CounterPrograms.value count ^ P
  let E := Execution.Hash.polynomialBudget count depth rounds B (P * count.length) cost
  have hcount' : 2 ≤ CounterPrograms.value count := by omega
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
  have hM2 : M ^ 2 ≤ E := family_square_le_polynomial count depth rounds B _ cost hcount'
  have hME : M ≤ E := (show M ≤ M ^ 2 by nlinarith only [hM]).trans hM2
  have hcwidth := HashGreedyCandidate.digitWidth_le_word_length hm count hcount
  have hwidth : HashCandidates.payloadWidth m P ≤ P * count.length :=
    Nat.mul_le_mul_left P hcwidth
  have hfamily : 2 ^ HashCandidates.payloadWidth m P ≤ M ^ 2 := by
    simpa only [M, hcount] using HashCandidates.candidate_count_le_square hm P
  have hcontrol : HashSelectProgram.controllerBudget B (P * count.length) cost
      (1 + (2 * (P * count.length) + 2) * M) M (CounterPrograms.value rounds) ≤ E := by
    dsimp [E, Execution.Hash.polynomialBudget, M, P]
    omega
  have h := rounds_le_square attempt B (HashCandidates.payloadWidth m P) cost
    (P * count.length) (1 + (2 * (P * count.length) + 2) * M) M
    (CounterPrograms.value rounds) factor hM hfamily hwidth hattempt
  have hprod : M * (HashSelectProgram.controllerBudget B (P * count.length) cost
      (1 + (2 * (P * count.length) + 2) * M) M (CounterPrograms.value rounds) + 1) ≤
      (E + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (hME.trans (Nat.le_succ E))
      (Nat.add_le_add_right hcontrol 1)
  exact h.trans (by simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left (402 * (factor + 1)) hprod)



/-- The original explicit hash budget is affine in its paid mass-query cost. -/
theorem polynomialBudget_affine (count depth rounds : List Bool) (B C cost : ℕ) :
    Execution.Hash.polynomialBudget count depth rounds B C cost =
      Execution.Hash.polynomialBudget count depth rounds B C 0 +
        (CounterPrograms.value rounds *
          (CounterPrograms.value count ^ CounterPrograms.value depth + 1)) * cost := by
  unfold Execution.Hash.polynomialBudget HashSelectProgram.controllerBudget
    HashSelectProgram.roundsBudget HashSelectProgram.roundBudget
    HashSelectProgram.selectBudget HashSelectProgram.loadBudget
  ring

/-- A fixed power substitution into a nonnegative linear measured cost stays
a fixed power, including a zero loop coefficient. -/
theorem linear_budget_substitute_with_input (base coeff oldCost newCost factor degree inputLength : ℕ)
    (hbase : coeff ≤ base) (hnew : newCost ≤ factor * (oldCost + inputLength + 1) ^ degree) :
    base + coeff * newCost ≤
      (factor + 1) * (base + coeff * oldCost + inputLength + 1) ^ (degree + 1) := by
  let E := base + coeff * oldCost + inputLength + 1
  change base + coeff * newCost ≤ (factor + 1) * E ^ (degree + 1)
  have hE : 1 ≤ E := by dsimp [E]; omega
  have hbE : base ≤ E := by dsimp [E]; omega
  have hcE : coeff ≤ E := hbase.trans hbE
  have hp : E ≤ E ^ (degree + 1) := Nat.le_self_pow (by omega) E
  by_cases hc : coeff = 0
  · subst coeff
    simp only [Nat.zero_mul, Nat.add_zero] at *
    nlinarith only [hbE, hp, Nat.zero_le (factor * E ^ (degree + 1))]
  have hcost : oldCost + inputLength + 1 ≤ E := by
    have h := Nat.mul_le_mul_right oldCost (show 1 ≤ coeff by omega)
    dsimp [E]
    omega
  have hnp : newCost ≤ factor * E ^ degree := hnew.trans
    (Nat.mul_le_mul_left factor (Nat.pow_le_pow_left hcost degree))
  have hterm : coeff * newCost ≤ factor * E ^ (degree + 1) := by
    have h := Nat.mul_le_mul hcE hnp
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  nlinarith only [hterm, hbE, hp]



/-- A fixed polynomial increase in the per-query measured cost can be charged
inside the original explicit hash budget without an input-dependent power. -/
theorem polynomialBudget_substitute_with_input (count depth rounds : List Bool)
    (B C oldCost newCost factor degree inputLength : ℕ)
    (hnew : newCost ≤ factor * (oldCost + inputLength + 1) ^ degree) :
    Execution.Hash.polynomialBudget count depth rounds B C newCost ≤
      (factor + 1) *
        (Execution.Hash.polynomialBudget count depth rounds B C oldCost + inputLength + 1) ^ (degree + 1) := by
  let coeff := CounterPrograms.value rounds *
    (CounterPrograms.value count ^ CounterPrograms.value depth + 1)
  have hc : coeff ≤ Execution.Hash.polynomialBudget count depth rounds B C 0 := by
    let M := CounterPrograms.value count ^ CounterPrograms.value depth
    let F := 1 + (2 * (CounterPrograms.value depth * count.length) + 2) * M
    have hs : M + 1 ≤ HashSelectProgram.selectBudget B C 0 M := by
      unfold HashSelectProgram.selectBudget
      exact Nat.le_mul_of_pos_right _ (by unfold HashSelectProgram.loadBudget; omega)
    have hr : M + 1 ≤ HashSelectProgram.roundBudget B C 0 F M := by
      unfold HashSelectProgram.roundBudget
      omega
    have hh : coeff ≤ HashSelectProgram.controllerBudget B C 0 F M
        (CounterPrograms.value rounds) := by
      unfold HashSelectProgram.controllerBudget HashSelectProgram.roundsBudget
      change CounterPrograms.value rounds * (M + 1) ≤
        CounterPrograms.value rounds * (HashSelectProgram.roundBudget B C 0 F M + 2) + 2
      exact (Nat.mul_le_mul_left _ (hr.trans (Nat.le_add_right _ 2))).trans
        (Nat.le_add_right _ 2)
    dsimp [Execution.Hash.polynomialBudget]
    exact hh.trans (Nat.le_add_left _ _)
  rw [polynomialBudget_affine count depth rounds B C newCost,
    polynomialBudget_affine count depth rounds B C oldCost]
  exact linear_budget_substitute_with_input _ coeff oldCost newCost factor degree inputLength hc hnew

/-- The actual staging and cleanup bound is linear in the retained entry
cap, so it fits the same fixed cube as the normalizer and marked mass. -/
theorem attempt_with_staging_polynomial (a : HashMassAdapter.Data) (queryCost : List Bool → ℕ)
    (n m depth D T : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    HashGreedyExecution.attemptBudget a n m depth queryCost + 95 * D + 103 ≤
      2100000 * (m + depth + (n + 1) + D + HashSelect.loopCap n m + 1) ^ 3 * (T + 1) := by
  let S := m + depth + (n + 1) + D + HashSelect.loopCap n m + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hD : D ≤ S := by dsimp [S]; omega
  have hpow : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have hmul : S ^ 3 ≤ S ^ 3 * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h := attemptBudget_polynomial a queryCost n m depth D T hm h0 h782 h769 ht
  change _ ≤ 2000000 * S ^ 3 * (T + 1) at h
  change _ ≤ 2100000 * S ^ 3 * (T + 1)
  nlinarith only [h, hS, hD, hpow, hmul]

/-- Paid staging, complete marked mass, padding and final cleanup
fit a fixed fifth power of the old explicit controller budget and input
parameters. The power is independent of every runtime input. -/
theorem staged_rounds_le_fifth_power (a : HashMassAdapter.Data)
    (count depth rounds : List Bool) (queryCost : List Bool → ℕ)
    (n m D T : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    let P := CounterPrograms.value depth
    let B := HashSelect.loopCap n m
    let S := m + P + (n + 1) + D + B + 1
    let E := Execution.Hash.polynomialBudget count depth rounds B (P * count.length) T
    HashSelectProgram.roundsBudget
      (NativeRound.roundBudget (HashGreedyExecution.attemptBudget a n m P queryCost + 95 * D + 103) B
        (HashCandidates.payloadWidth m P)) (CounterPrograms.value rounds) ≤
      1000000000 * (S + E + 1) ^ 5 := by
  intro P B S E
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hattempt := attempt_with_staging_polynomial a queryCost n m P D T hmword h0 h782 h769 ht
  have hcost : HashGreedyExecution.attemptBudget a n m P queryCost + 95 * D + 103 ≤
      (2100000 * S ^ 3) * (T + B + P * count.length + 1) :=
    hattempt.trans (Nat.mul_le_mul_left _ (by omega))
  have hr := rounds_le_polynomial count depth rounds m B T
    (HashGreedyExecution.attemptBudget a n m P queryCost + 95 * D + 103) (2100000 * S ^ 3) hm hcount hcost
  change _ ≤ 402 * (2100000 * S ^ 3 + 1) * (E + 1) ^ 2 at hr
  have hcoef : 2100000 * S ^ 3 + 1 ≤ 2100001 * S ^ 3 := by
    have h1 := Nat.one_le_pow 3 S hS
    omega
  have hp : S ^ 3 * (E + 1) ^ 2 ≤ (S + E + 1) ^ 5 := by
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left (show S ≤ S + E + 1 by omega) 3)
      (Nat.pow_le_pow_left (show E + 1 ≤ S + E + 1 by omega) 2)
    simpa only [← pow_add] using h
  calc
    _ ≤ 402 * (2100000 * S ^ 3 + 1) * (E + 1) ^ 2 := hr
    _ ≤ 402 * (2100001 * S ^ 3) * (E + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcoef)
    _ = 844200402 * (S ^ 3 * (E + 1) ^ 2) := by ring
    _ ≤ 844200402 * (S + E + 1) ^ 5 := Nat.mul_le_mul_left _ hp
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)


/-- The measured budget belongs to the actual normalize, stage, marked-mass,
cleanup and padding command, not an unstaged query service. -/
theorem named_staged_rounds_le_fifth_power (a : HashMassAdapter.Data)
    (count depth rounds : List Bool) (queryCost : List Bool → ℕ)
    (n m D T : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    let P := CounterPrograms.value depth
    let B := HashSelect.loopCap n m
    let S := m + P + (n + 1) + D + B + 1
    let E := Execution.Hash.polynomialBudget count depth rounds B (P * count.length) T
    HashSelectProgram.roundsBudget
      (NativeRound.roundBudget (HashGreedyExecution.stagedAttemptBudget a n m P queryCost D) B
        (HashCandidates.payloadWidth m P)) (CounterPrograms.value rounds) ≤
      1000000000 * (S + E + 1) ^ 5 := by
  exact staged_rounds_le_fifth_power a count depth rounds queryCost n m D T
    hm hcount hmword h0 h782 h769 ht

open SqrtLog.HashSelectProgram

/-- Every old explicit setup/controller term is a fixed polynomial of the
actual retained scalar and word bounds, candidate count, and paid query cost. -/
theorem originalBudget_le_polynomial (count depth rounds : List Bool)
    (B C cost S family : ℕ)
    (ha : CounterPrograms.value count ≤ S) (hp : CounterPrograms.value depth ≤ S)
    (hr : CounterPrograms.value rounds ≤ S)
    (hcw : count.length ≤ S) (hdw : depth.length ≤ S) (hrw : rounds.length ≤ S)
    (hB : B ≤ S) (hC : C ≤ S)
    (hf : CounterPrograms.value count ^ CounterPrograms.value depth ≤ family) :
    Execution.Hash.polynomialBudget count depth rounds B C cost ≤
      10000 * (S + family + cost + 1) ^ 7 := by
  let X := S + family + cost + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hSX : S ≤ X := by dsimp [X]; omega
  have hfX : family ≤ X := by dsimp [X]; omega
  have hcX : cost ≤ X := by dsimp [X]; omega
  have haX := ha.trans hSX
  have hpX := hp.trans hSX
  have hrX := hr.trans hSX
  have hcwX := hcw.trans hSX
  have hdwX := hdw.trans hSX
  have hrwX := hrw.trans hSX
  have hBX := hB.trans hSX
  have hCX := hC.trans hSX
  have hfamily := hf.trans hfX
  have hbound : Execution.Hash.polynomialBudget count depth rounds B C cost ≤
      ((X+1)*(60*X+60)+2*X+3+1+
       (2*X+(X+1)*(16*X+16)+2*X+6+1)+
       (2*X+(X+1)*(16*X+16)+2*X+6+1))+
      400*(X+1)*X^2*X^2*((X+1)*X+1)+15+
      (X*(7*(1+(2*(X*X)+2)*X)+5+
        (X+1)*(6*X+X+10+100*(X+X+1)+4)+5*X+2*X+10+2)+2) := by
    unfold Execution.Hash.polynomialBudget Execution.HashInputs.budget
      Execution.HashAlphabet.budget CounterConversions.coreBound
      controllerBudget roundsBudget roundBudget selectBudget loadBudget
    dsimp only
    gcongr
  apply hbound.trans
  have h2 : X^2 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h3 : X^3 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h4 : X^4 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h5 : X^5 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h6 : X^6 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h1 : X ≤ X^7 := Nat.le_self_pow (by decide) X
  have h0 : 1 ≤ X^7 := Nat.one_le_pow _ _ hX
  change _ ≤ 10000*X^7
  nlinarith only [h0,h1,h2,h3,h4,h5,h6]

/-- The candidate factor in the real explicit budget is bounded by the old
all-trial/all-mark call counter, for its exact ternary alphabet and depth. -/
theorem family_le_hashCalls (n m P : ℕ) (hm : 0 < m) :
    (3*m)^P ≤ CostAssembly.hashCalls n m P := by
  have hr : 1 ≤ HashSelect.loopCap n m := by unfold HashSelect.loopCap; omega
  have hprod := Nat.mul_le_mul hr hm
  have hh := Nat.mul_le_mul_left ((3*m)^P) hprod
  have hh' : (3*m)^P ≤ (3*m)^P*HashSelect.loopCap n m*m := by
    simpa only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] using hh
  unfold CostAssembly.hashCalls
  apply hh'.trans
  have hdouble := Nat.le_mul_of_pos_left ((3*m)^P*HashSelect.loopCap n m*m)
    (by decide : 0 < 2)
  have heq : 2*((3*m)^P*HashSelect.loopCap n m*m) =
      2*(3*m)^P*HashSelect.loopCap n m*m := by ring
  exact (hdouble.trans_eq heq).trans (Nat.le_succ _)

theorem originalBudget_le_hashCalls (count depth rounds : List Bool)
    (n m P B C cost S : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3*m)
    (hdepth : CounterPrograms.value depth = P)
    (ha : 3*m ≤ S) (hp : P ≤ S) (hr : CounterPrograms.value rounds ≤ S)
    (hcw : count.length ≤ S) (hdw : depth.length ≤ S) (hrw : rounds.length ≤ S)
    (hB : B ≤ S) (hC : C ≤ S) :
    Execution.Hash.polynomialBudget count depth rounds B C cost ≤
      10000 * (S + CostAssembly.hashCalls n m P + cost + 1)^7 := by
  apply originalBudget_le_polynomial count depth rounds B C cost S
    (CostAssembly.hashCalls n m P)
    (hcount ▸ ha) (hdepth ▸ hp) hr hcw hdw hrw hB hC
  simpa only [hcount,hdepth] using family_le_hashCalls n m P hm

/-- The numerical representative of the unary round counter is canonical
binary; its value and length are both charged, without reading the unary
word as a binary number. -/
theorem canonical_originalBudget_le (count depth : List Bool)
    (n m P L cost : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3*m)
    (hdepth : CounterPrograms.value depth = P)
    (hmL : m ≤ L) (hPL : P ≤ L) (hround : HashSelect.loopCap n m ≤ L)
    (hcw : count.length ≤ L) (hdw : depth.length ≤ L) :
    Execution.Hash.polynomialBudget count depth (countWord (HashSelect.loopCap n m))
      (HashSelect.loopCap n m) (P*count.length) cost ≤
      10000*4^7*(L+CostAssembly.hashCalls n m P+cost+1)^14 := by
  let S := 3*(L+1)^2
  have hL : L+1 ≤ S := by dsimp [S]; nlinarith
  have hP : P ≤ S := hPL.trans (by omega)
  have hroundValue : CounterPrograms.value (countWord (HashSelect.loopCap n m)) ≤ S := by
    simp only [CounterPrograms.value_eq_toNat,countWord_toNat]
    omega
  have hword : (countWord (HashSelect.loopCap n m)).length ≤ S := by
    have h := countWord_length_le ((show HashSelect.loopCap n m ≤ 2^(HashSelect.loopCap n m) from Nat.le_of_lt Nat.lt_two_pow_self))
    omega
  have hC : P*count.length ≤ S := by
    have h := Nat.mul_le_mul hPL hcw
    dsimp [S]
    nlinarith only [h, Nat.zero_le L]
  have h := originalBudget_le_hashCalls count depth (countWord (HashSelect.loopCap n m))
    n m P (HashSelect.loopCap n m) (P*count.length) cost S hm hcount hdepth
    (by dsimp [S]; nlinarith only [hmL, Nat.zero_le L]) hP hroundValue
    (hcw.trans (by omega)) (hdw.trans (by omega)) hword (by omega) hC
  let X := L+CostAssembly.hashCalls n m P+cost+1
  have hbase : L+1 ≤ X := by dsimp [X]; omega
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hx : X ≤ X^2 := Nat.le_self_pow (by decide) X
  have hS : S ≤ 3*X^2 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hbase 2)
  have hsum : S+CostAssembly.hashCalls n m P+cost+1 ≤ 4*X^2 := by
    have hrest : CostAssembly.hashCalls n m P+cost+1 ≤ X := by dsimp [X]; omega
    calc
      _ ≤ 3*X^2+X := by omega
      _ ≤ 4*X^2 := by omega
  apply h.trans
  have hb := Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hsum 7)
  simpa only [mul_pow,←pow_mul,Nat.mul_assoc] using hb
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete leaf control: prepared code history, all physically staged greedy
rounds, and a separate history-only exact count. The query execution proofs
remain explicit development seams until the native query bodies instantiate them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

/-- The numerical comparison consumes the identical staged budget used by
ready_rounds. Its round word is a canonical mathematical representative of
the actual unary round count, not a second operational counter. -/
theorem roundsTime_le_fifth_power {n m B : ℕ} {initial : List (List Bool)}
    (base : State 40 896) (hr : NativeLeafPreparation.Ready n m B initial base)
    (hm : 0 < m) (queryCost : List Bool → ℕ) (L T : ℕ)
    (ha : ∀ i, (base.stacks i).length ≤ L)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    let depth := SparseCode.distanceDenom m B
    let S := m + depth + (n + 1) + L + HashSelect.loopCap n m + 1
    let E := Execution.Hash.polynomialBudget (base.stacks 780) (base.stacks 817)
      (countWord (HashSelect.loopCap n m)) (HashSelect.loopCap n m)
      (depth * (base.stacks 780).length) T
    roundsTime base n m depth queryCost L ≤ 1000000000 * (S + E + 1) ^ 5 := by
  have hc : CounterPrograms.value (base.stacks 780) = 3 * m := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.modulus
  have hmword : CounterPrograms.value (base.stacks 782) = m := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.clauses
  have h := HashGreedyBudgets.named_staged_rounds_le_fifth_power base
    (base.stacks 780) (base.stacks 817) (countWord (HashSelect.loopCap n m)) queryCost
    n m L T hm hc hmword (ha 0) (ha 782) (ha 769) ht
  simpa only [CounterPrograms.value_eq_toNat, hr.depth, countWord_toNat, roundsTime] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafContract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform correctness and resources for the fixed native leaf. The final
contract instantiates the actual preparation, marked rounds and accepted
query; only numerical bounds produced by the outer program remain. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

/-- The ordinary size appearing in the measured staged-round budget is
bounded by the same common L that bounds its actual retained words. -/
theorem common_round_size (n m B R : ℕ) :
    m + SqrtLog.SparseCode.distanceDenom m B + (n + 1) +
      NativeLeafRun.commonBound n m B R + SqrtLog.HashSelect.loopCap n m + 1 ≤
        5 * NativeLeafRun.commonBound n m B R + 1 := by
  let S := HashQueryInputBounds.commonCap n m B R
  have hpow : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have hs : S ≤ NativeLeafRun.commonBound n m B R := by
    unfold NativeLeafRun.commonBound
    change S ≤ 16 * S ^ 3
    omega
  dsimp only [S, HashQueryInputBounds.commonCap] at hs
  omega

open SqrtLog HashGreedyProgram.NativeRound in
/-- Apply the fixed-power query replacement to the identical staged budget
used by the actual rounds. The old budget uses a canonical proof-side round
word; the actual machine retains its unary round word. Physical word factors
remain explicit in the old budget until its numerical producer bound is used. -/
theorem staged_rounds_time_substitution
    {n m B R : ℕ} {initial : List (List Bool)} (base : State 40 896)
    (hr : NativeLeafPreparation.Ready n m B initial base) (hm : 0 < m)
    (queryCost : List Bool → ℕ) (inputLength newQuery oldQuery factor power C d : ℕ)
    (ha : ∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B R)
    (hL : NativeLeafRun.commonBound n m B R ≤ C * (inputLength + 1) ^ d)
    (hq : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ newQuery)
    (hnew : newQuery ≤ factor * (oldQuery + inputLength + 1) ^ power) :
    let depth := SparseCode.distanceDenom m B
    let L := NativeLeafRun.commonBound n m B R
    let E := Execution.Hash.polynomialBudget (base.stacks 780) (base.stacks 817)
      (countWord (HashSelect.loopCap n m)) (HashSelect.loopCap n m)
      (depth * (base.stacks 780).length) oldQuery
    NativeLeafRun.roundsTime base n m depth queryCost L ≤
      1000000000 * (5 * C + factor + 3) ^ 5 *
        (E + inputLength + 1) ^ ((d + power + 1) * 5) := by
  intro depth L E
  let Enew := Execution.Hash.polynomialBudget (base.stacks 780) (base.stacks 817)
    (countWord (HashSelect.loopCap n m)) (HashSelect.loopCap n m)
    (depth * (base.stacks 780).length) newQuery
  let X := E + inputLength + 1
  let P := X ^ (d + power + 1)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hiX : inputLength + 1 ≤ X := by dsimp [X]; omega
  have hd : (inputLength + 1) ^ d ≤ P :=
    (Nat.pow_le_pow_left hiX d).trans (Nat.pow_le_pow_right hX (by omega))
  have hp : X ^ (power + 1) ≤ P := Nat.pow_le_pow_right hX (by omega)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ hX
  have hL' : L ≤ C * P := hL.trans (Nat.mul_le_mul_left C hd)
  have hE : Enew ≤ (factor + 1) * X ^ (power + 1) :=
    HashGreedyBudgets.polynomialBudget_substitute_with_input
      (base.stacks 780) (base.stacks 817) (countWord (HashSelect.loopCap n m))
      (HashSelect.loopCap n m) (depth * (base.stacks 780).length)
      oldQuery newQuery factor power inputLength hnew
  have hE' := hE.trans (Nat.mul_le_mul_left (factor + 1) hp)
  have hs := common_round_size n m B R
  have hsum : m + depth + (n + 1) + L + HashSelect.loopCap n m + 1 + Enew + 1 ≤
      (5 * C + factor + 3) * P := by
    change m + depth + (n + 1) + L + HashSelect.loopCap n m + 1 ≤ 5 * L + 1 at hs
    nlinarith only [hs, hL', hE', hP]
  have hround := NativeLeafRun.roundsTime_le_fifth_power base hr hm queryCost L newQuery ha hq
  have hpow := Nat.mul_le_mul_left 1000000000 (Nat.pow_le_pow_left hsum 5)
  apply hround.trans
  simpa only [P, X, mul_pow, ← pow_mul, Nat.mul_assoc] using hpow

open SqrtLog HashGreedyProgram.NativeRound in
/-- Uniformly charge the actual staged rounds to the original all-candidate,
all-mark call count. The actual canonical modulus and saved depth words are
bounded from preparation, including their padding, before substitution. -/
theorem staged_rounds_time_hashCalls_oai (factor power C d : ℕ) :
    ∃ A degree : ℕ, ∀ {n m B R : ℕ} {initial : List (List Bool)} (base : State 40 896),
      NativeLeafPreparation.Ready n m B initial base → 0 < m →
      ∀ (queryCost : List Bool → ℕ) (inputLength newQuery oldQuery : ℕ),
      (∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B R) →
      NativeLeafRun.commonBound n m B R ≤ C * (inputLength + 1) ^ d →
      (∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ newQuery) →
      newQuery ≤ factor * (oldQuery + inputLength + 1) ^ power →
      NativeLeafRun.roundsTime base n m (SparseCode.distanceDenom m B) queryCost
        (NativeLeafRun.commonBound n m B R) ≤
        A * (CostAssembly.hashCalls n m (SparseCode.distanceDenom m B) +
          oldQuery + inputLength + 1) ^ degree := by
  have scale (a b y z e q : ℕ) (hz : z ≤ b * y ^ e) :
      a * z ^ q ≤ a * b ^ q * y ^ (e * q) := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using
      Nat.mul_le_mul_left a (Nat.pow_le_pow_left hz q)
  let D := (d + power + 1) * 5
  let K := (10000 * 4 ^ 7 + 1) * (C + 1) ^ 14
  refine ⟨(1000000000 * (5 * C + factor + 3) ^ 5) * K ^ D,
    (14 * (d + 1)) * D, ?_⟩
  intro n m B R initial base hr hm queryCost inputLength newQuery oldQuery ha hL hq hnew
  let depth := SparseCode.distanceDenom m B
  let L := NativeLeafRun.commonBound n m B R
  let E := Execution.Hash.polynomialBudget (base.stacks 780) (base.stacks 817)
    (countWord (HashSelect.loopCap n m)) (HashSelect.loopCap n m)
    (depth * (base.stacks 780).length) oldQuery
  let Y := CostAssembly.hashCalls n m depth + oldQuery + inputLength + 1
  have hY : 1 ≤ Y := by dsimp [Y]; omega
  have hIY : inputLength + 1 ≤ Y := by dsimp [Y]; omega
  have hYpow : Y ≤ Y ^ (d + 1) := Nat.le_self_pow (by omega) Y
  have hLpow : L ≤ C * Y ^ (d + 1) :=
    hL.trans (Nat.mul_le_mul_left C
      ((Nat.pow_le_pow_left hIY d).trans (Nat.pow_le_pow_right hY (by omega))))
  have hsum : L + CostAssembly.hashCalls n m depth + oldQuery + 1 ≤
      (C + 1) * Y ^ (d + 1) := by
    have hrest : CostAssembly.hashCalls n m depth + oldQuery + 1 ≤ Y := by dsimp [Y]; omega
    nlinarith only [hLpow, hYpow, hrest]
  let S := HashQueryInputBounds.commonCap n m B R
  have hS : S ≤ L := by
    have hp : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
    change S ≤ 16 * S ^ 3
    omega
  have hdimensions : m ≤ L ∧ depth ≤ L ∧ HashSelect.loopCap n m ≤ L := by
    dsimp only [S, HashQueryInputBounds.commonCap] at hS
    dsimp only [depth]
    omega
  have hc : CounterPrograms.value (base.stacks 780) = 3 * m := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.modulus
  have hd : CounterPrograms.value (base.stacks 817) = depth := by
    rw [CounterPrograms.value_eq_toNat]
    exact hr.depth
  have he : E ≤ 10000 * 4 ^ 7 * (L + CostAssembly.hashCalls n m depth + oldQuery + 1) ^ 14 :=
    HashGreedyBudgets.canonical_originalBudget_le (base.stacks 780) (base.stacks 817)
      n m depth L oldQuery hm hc hd hdimensions.1 hdimensions.2.1 hdimensions.2.2 (ha 780) (ha 817)
  have he' : E ≤ (10000 * 4 ^ 7) * (C + 1) ^ 14 * Y ^ ((d + 1) * 14) :=
    he.trans (scale (10000 * 4 ^ 7) (C + 1) Y _ (d + 1) 14 hsum)
  have hy' : inputLength + 1 ≤ (C + 1) ^ 14 * Y ^ ((d + 1) * 14) := by
    have hcoeff : 1 ≤ (C + 1) ^ 14 := Nat.one_le_pow' _ _
    have hp : Y ≤ Y ^ ((d + 1) * 14) := Nat.le_self_pow (by omega) Y
    exact (hIY.trans hp).trans (by
      simpa only [one_mul] using Nat.mul_le_mul_right (Y ^ ((d + 1) * 14)) hcoeff)
  have heI : E + inputLength + 1 ≤ K * Y ^ (14 * (d + 1)) := by
    dsimp only [K]
    rw [Nat.mul_comm 14 (d + 1)]
    nlinarith only [he', hy']
  have hround := staged_rounds_time_substitution base hr hm queryCost
    inputLength newQuery oldQuery factor power C d ha hL hq hnew
  exact hround.trans (scale (1000000000 * (5 * C + factor + 3) ^ 5)
    K Y (E + inputLength + 1) (14 * (d + 1)) D heI)

open SqrtLog Filter
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.staged_rounds_time_hashCalls_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.staged_rounds_time_hashCalls_oai
