-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:12:20.829282+00:00
-- url     : https://prove2.me/submissions/3d0d70b4-5006-46a6-b6ee-1166b9c0f605

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_LeafPreparationBudgets_prepared_common_bound_polynomial

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Asymptotics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Numerical parameters for the disjoint counting reduction. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem sparsifySchedule_le_lambda (n : ℕ) : sparsifySchedule n ≤ sparsifyLambda n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

theorem sparsify_parameters_le_input (n : ℕ) :
    sparsifyLambda n ≤ n ∧ sparsifyNu n ≤ n ∧ sparsifySchedule n ≤ n := by
  have hLambda : sparsifyLambda n ≤ n :=
    (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp Nat.lt_two_pow_self.le
  have hNu : sparsifyNu n ≤ sparsifyLambda n :=
    (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp Nat.lt_two_pow_self.le
  exact ⟨hLambda, hNu.trans hLambda, (sparsifySchedule_le_lambda n).trans hLambda⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sharp numerical budgets for disjoint counting sparsification

The frozen counting manuscript, Appendix A, lines 1991–2054. These numerical lemmas do not assert the
existence of a sparsification tree or a primitive implementation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget

open Finset
open scoped BigOperators

open SparseCharging

theorem chooseExponent_spec (k a b : ℕ) (ha : 0 < a) :
    parameterTest k a b (chooseExponent k a b ha) = true :=
  Nat.find_spec (exists_parameter k a b ha)

theorem chooseExponent_le (k a b e : ℕ) (ha : 0 < a)
    (he : parameterTest k a b e = true) : chooseExponent k a b ha ≤ e :=
  Nat.find_min' (exists_parameter k a b ha) he

theorem chooseM_spec (k a b : ℕ) (ha : 0 < a) :
    2 ≤ chooseM k a b ha ∧ rightConstant k ≤ chooseM k a b ha ∧
      rightConstant k * Nat.clog 2 (4 * depthConstant k (chooseM k a b ha) *
        chooseM k a b ha) * b ≤ a * chooseM k a b ha := by
  simpa only [parameterTest, chooseM, decide_eq_true_eq] using chooseExponent_spec k a b ha

/-- The first successful candidate inherits the sharp witness bound. Constants
are chosen before the rational budget numerator and denominator. -/
theorem choose_bounds (k : ℕ) :
    ∃ K T : ℕ, ∀ a b (ha : 0 < a),
      chooseM k a b ha ≤ K * inverseIndex a b * (Nat.log 2 (inverseIndex a b) + 1) ∧
      chooseExponent k a b ha ≤ T + 2 * (Nat.log 2 (inverseIndex a b) + 1) := by
  let A := 4 * (k - 1) * 3 ^ (k - 2)
  let q := k - 2
  let T := 2 * (rightConstant k * (A + 2 + 4 * (q + 1) + 1) + 1)
  refine ⟨4 * 2 ^ T, T, ?_⟩
  intro a b ha
  let s := inverseIndex a b
  obtain ⟨T', e, _, hγ, hM, hbudget, hsize, hindex, hT⟩ :=
    dyadic_witness (depthConstant k) A q (rightConstant k) s
      (by exact Nat.zero_lt_succ _) (fun M hM => depthConstant_le k M hM)
  have he : parameterTest k a b e = true := by
    simp only [parameterTest, decide_eq_true_eq]
    refine ⟨hM, hγ, ?_⟩
    calc
      rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * b ≤
          rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * (a * s) :=
        Nat.mul_le_mul_left _ (inverseIndex_mul a b ha)
      _ = a * (rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * s) := by ring
      _ ≤ a * 2 ^ e := Nat.mul_le_mul_left a hbudget
  have hmin := chooseExponent_le k a b e ha he
  have hT' : T' = T := hT
  subst T'
  exact ⟨(Nat.pow_le_pow_right (by decide) hmin).trans hsize, hmin.trans hindex⟩

theorem inverseIndex_le_denominator (a b : ℕ) (hb : 0 < b) : inverseIndex a b ≤ b := by
  have := Nat.div_le_self (b - 1) a
  dsimp [inverseIndex]
  omega

/-- Search length is logarithmic in the positive rational denominator; candidate
values remain polynomial in it. This exposes the uniform parameter-size budget. -/
theorem choose_encoding_bounds (k : ℕ) :
    ∃ K T : ℕ, ∀ a b (ha : 0 < a), 0 < b →
      chooseM k a b ha ≤ K * b ^ 2 ∧
      chooseExponent k a b ha ≤ T + 2 * (Nat.log 2 b + 1) := by
  obtain ⟨K, T, h⟩ := choose_bounds k
  refine ⟨K, T, ?_⟩
  intro a b ha hb
  have hs := inverseIndex_le_denominator a b hb
  have hlog : Nat.log 2 (inverseIndex a b) + 1 ≤ inverseIndex a b :=
    Nat.succ_le_of_lt (Nat.log_lt_self 2 (by exact Nat.succ_ne_zero _))
  constructor
  · calc
      chooseM k a b ha ≤ K * inverseIndex a b * (Nat.log 2 (inverseIndex a b) + 1) :=
        (h a b ha).1
      _ ≤ K * b * b := Nat.mul_le_mul (Nat.mul_le_mul_left K hs) (hlog.trans hs)
      _ = K * b ^ 2 := by ring
  · exact (h a b ha).2.trans (by have := Nat.log_mono_right (b := 2) hs; omega)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassStagedSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical staging, all marked counts, and actual source cleanup share one
prefix bound. Cleanup only removes bits, so it does not amplify the query's
transient cap into the next boundary allowance. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter HashMassStaged

/-- The explicit staging/reference expression is bounded by one fixed cube;
the expensive query contributes only its independently proved prefix cap. -/
theorem spaceBudget_le (a : State 40 896) (m L K : ℕ)
    (hm : CounterPrograms.value (a.stacks 782) = m)
    (hL : ∀ i, (a.stacks i).length ≤ L) :
    spaceBudget a L K ≤ max K (10000 * (m + L + 1) ^ 3) := by
  let S := m + L + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hLS : L ≤ S := by dsimp [S]; omega
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
  have href := HashMassBounds.massBudget_le a (fun _ => 0) (fun _ => 0) m 0 L 0 hm
    (hL 0) (hL 782) (hL 769) (by intro; exact Nat.zero_le _) (by intro; exact Nat.zero_le _)
  have href' : LeafOuterProgram.routeCost (782,0) a +
      LeafOuterNative.References.budget (a.stacks 782) + 1 ≤ 1000 * S ^ 3 := by
    have hbase : LeafOuterProgram.routeCost (782,0) a +
        LeafOuterNative.References.budget (a.stacks 782) + 1 ≤
        massBudget a (fun _ => 0) (fun _ => 0) m := by
      unfold massBudget
      omega
    exact hbase.trans (by simpa [S] using href)
  unfold spaceBudget
  apply max_le_max le_rfl
  change _ ≤ 10000 * S ^ 3
  nlinarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace
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

/-- The actual staged selector retains polynomial space independently of all
candidate and round counts; only the separately proved query prefix cap appears. -/
theorem staged_rounds_space_le (a : StructuredCalls.State 40 896)
    (n m depth L K : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (hwords : ∀ i, (a.stacks i).length ≤ L)
    (hrounds : HashSelect.loopCap n m ≤ L)
    (hwidth : HashCandidates.payloadWidth m depth ≤ L) :
    max (HashGreedyStagedSpace.attemptSpace a n m depth L K)
      (896 * L + 100 * (HashSelect.loopCap n m + HashCandidates.payloadWidth m depth + 1) +
        7 * (2 * HashCandidates.payloadWidth m depth + 3) + 20) ≤
      max K (1000000 * (m + depth + L + 1) ^ 3) := by
  let S := m + depth + L + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hL : L ≤ S := by dsimp [S]; omega
  have hpow : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have hbase' := HashMassStagedSpace.spaceBudget_le a m L 0 hm hwords
  simp only [HashMassStagedSpace.spaceBudget, Nat.zero_le, max_eq_right] at hbase'
  have hs : m + L + 1 ≤ S := by dsimp [S]; omega
  have hbaseS := hbase'.trans (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hs 3))
  have hprep := HashCandidateProgram.Leaf.budget_polynomial m depth
  have hd : depth + 1 ≤ S := by dsimp [S]; omega
  have hw : HashCandidates.digitWidth m + 1 ≤ 3 * S := by
    have h := DyadicWidth.width_le_succ (3 * m)
    change HashCandidates.digitWidth m ≤ 3 * m + 1 at h
    dsimp [S]
    omega
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 6200 hd) (Nat.pow_le_pow_left hw 2)
  have hprepS : HashCandidateProgram.Leaf.budget m depth ≤ 55800 * S ^ 3 := by
    nlinarith only [hprep, hp]
  apply max_le
  · unfold HashGreedyStagedSpace.attemptSpace
    apply max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
    change _ ≤ 1000000 * S ^ 3
    omega
  · apply le_trans _ (le_max_right _ _)
    change _ ≤ 1000000 * S ^ 3
    omega

open SqrtLog.HashSelectProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical input bounds for all attained greedy histories and every trial,
including losing candidates. All bounds concern literal retained words and
raw slots. No execution-time or successful-query bound is used. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyCNF HashGreedyCode

theorem commonCap_bounds (n m B wordBound : ℕ) :
    1 ≤ commonCap n m B wordBound ∧ SparseCode.totalRows m B ≤ commonCap n m B wordBound ∧
      SparseCode.degreeBound m B ≤ commonCap n m B wordBound ∧
      SparseCode.distanceDenom m B ≤ commonCap n m B wordBound ∧
      HashCandidates.digitWidth m ≤ commonCap n m B wordBound ∧
      HashSelect.loopCap n m ≤ commonCap n m B wordBound ∧ wordBound ≤ commonCap n m B wordBound := by
  unfold commonCap
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ResourceBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-degree numerical closure for measured streaming costs. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open SqrtLog.Statement

/-- The native dyadic parameter program returns exactly this larger cap,
which bounds leaf occurrences and remains polynomial in the ceiling log. -/
theorem chosen_sparseBound_le_lambda (k : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ sparsifySchedule n →
      4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1) ≤
        C * sparsifyLambda n ^ (2 * (k - 1)) := by
  obtain ⟨K, T, hK⟩ := DisjointReuse.SparseBudget.choose_encoding_bounds k
  refine ⟨4 * K ^ (k - 1), ?_⟩
  intro n hs
  have hM := (hK 1 (sparsifySchedule n) (by omega) (by omega)).1
  calc
    _ ≤ 4 * (K * sparsifySchedule n ^ 2) ^ (k - 1) := by gcongr
    _ ≤ 4 * (K * sparsifyLambda n ^ 2) ^ (k - 1) := by
      gcongr
      exact sparsifySchedule_le_lambda n
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

theorem formulaBound_polynomial (n k : ℕ) :
    DisjointReuse.SparseCountProgram.formulaBound n k ≤
      (2 + (4 + 8 * k) * (k + 1) * 2 ^ k) * (n + 1) ^ (k + 1) := by
  have hbase : 1 ≤ n + 1 := by omega
  have hp : n + 1 ≤ (n + 1) ^ (k + 1) := by
    simpa using Nat.pow_le_pow_right hbase (show 1 ≤ k + 1 by omega)
  have hcoef : 4 + (8 * n + 8) * k ≤ (4 + 8 * k) * (n + 1) := by nlinarith
  have hpow : (2 * n + 1) ^ k ≤ 2 ^ k * (n + 1) ^ k := by
    simpa [mul_pow] using Nat.pow_le_pow_left (show 2 * n + 1 ≤ 2 * (n + 1) by omega) k
  unfold DisjointReuse.SparseCountProgram.formulaBound
  calc
    _ ≤ 2 * (n + 1) ^ (k + 1) +
        ((4 + 8 * k) * (n + 1)) * ((k + 1) * (2 ^ k * (n + 1) ^ k)) := by
      apply Nat.add_le_add
      · omega
      · exact Nat.mul_le_mul hcoef (Nat.mul_le_mul_left (k + 1) hpow)
    _ = _ := by rw [pow_succ]; ring


/-- The actual disjoint occurrence choice is bounded in original input
length, with coefficients and degree fixed by the width. -/
theorem chosen_sparseBound_le_input (k : ℕ) :
    ∃ K : ℕ, ∀ n inputLength : ℕ, n ≤ inputLength → 1 ≤ sparsifySchedule n →
      4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1) ≤
        K * (inputLength + 1) ^ (2 * (k - 1)) := by
  obtain ⟨K, hK⟩ := chosen_sparseBound_le_lambda k
  refine ⟨K, ?_⟩
  intro n inputLength hn hs
  apply (hK n hs).trans
  apply Nat.mul_le_mul_left K
  apply Nat.pow_le_pow_left
  exact (sparsify_parameters_le_input n).1.trans (by omega)

/-- The complete ordinary size used by native leaf preparation is a fixed
input polynomial for the actual occurrence choice and sparse leaf count.
Physical input words remain independently bounded by their proved producer. -/
theorem chosen_leaf_input_cap (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W : ℕ,
      n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      n + m + B + W + 16 ≤ C * (inputLength + 1) ^ degree := by
  obtain ⟨K, hK⟩ := chosen_sparseBound_le_input k
  refine ⟨2 * K + wordCoefficient + 17, 2 * (k - 1) + wordDegree + 1, ?_⟩
  intro n inputLength m W hn hs B hm hW
  let X := inputLength + 1
  let degree := 2 * (k - 1) + wordDegree + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hB : B ≤ K * X ^ (2 * (k - 1)) := hK n inputLength hn hs
  have hm' : m ≤ K * X ^ (2 * (k - 1) + 1) := by
    calc
      _ ≤ n * B := hm
      _ ≤ X * (K * X ^ (2 * (k - 1))) :=
        Nat.mul_le_mul (by dsimp [X]; omega) hB
      _ = _ := by rw [pow_succ']; ring
  have hB' : B ≤ K * X ^ degree := hB.trans
    (Nat.mul_le_mul_left K (Nat.pow_le_pow_right hX (by dsimp [degree]; omega)))
  have hm'' : m ≤ K * X ^ degree := hm'.trans
    (Nat.mul_le_mul_left K (Nat.pow_le_pow_right hX (by dsimp [degree]; omega)))
  have hW' : W ≤ wordCoefficient * X ^ degree := hW.trans
    (Nat.mul_le_mul_left wordCoefficient (Nat.pow_le_pow_right hX (by dsimp [degree]; omega)))
  have hlin : X ≤ X ^ degree := by
    simpa using Nat.pow_le_pow_right hX (show 1 ≤ degree by dsimp [degree]; omega)
  have h1 : 1 ≤ X ^ degree := Nat.one_le_pow _ _ hX
  change _ ≤ (2 * K + wordCoefficient + 17) * X ^ degree
  have hn' : n ≤ X := by dsimp [X]; omega
  nlinarith only [hB', hm'', hW', hlin, h1, hn']

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_LeafPreparationBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Numerical resources of the actual full leaf-preparation command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
open SqrtLog SqrtLog.LeafOuterProgram NativeLeafPreparation NativeCodeAssembly

/-- The physically expanded selector depth is polynomial in its actual
numeric parameters; its binary word length alone would not suffice. -/
theorem distanceDenom_polynomial (m B : ℕ) :
    SparseCode.distanceDenom m B ≤ 20000 * (B + m + 1) ^ 4 := by
  have hl : SparseCode.logSize m ≤ m + 1 := by
    unfold SparseCode.logSize
    exact Nat.add_le_add_right (Nat.log_le_self 2 m) 1
  have hB : B ≤ B + m + 1 := by omega
  have hlog : SparseCode.logSize m ≤ B + m + 1 := by omega
  have h := Nat.mul_le_mul (Nat.pow_le_pow_left hB 2) (Nat.pow_le_pow_left hlog 2)
  unfold SparseCode.distanceDenom
  nlinarith only [h]


/-- The actual disjoint choice and loaded input-word cap fix one polynomial
common selector boundary in original input length before all leaf calls. -/
theorem chosen_prepared_common_bound (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : StructuredCalls.State 40 896, (∀ i, (a.stacks i).length ≤ L) →
      LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (max (L + 1) (continuationSpace m B L a prepared))
        (NativeLeafRun.commonBound n m B (retainedBound m B L a prepared)) ≤
          C * (inputLength + 1) ^ degree := by
  obtain ⟨C, degree, hprep⟩ := prepared_common_bound_polynomial
  obtain ⟨K, exponent, hsize⟩ := chosen_leaf_input_cap k wordCoefficient wordDegree
  refine ⟨C * K ^ degree, exponent * degree, ?_⟩
  intro n inputLength m W hn hm hinput hs B hmb hW L a prepared ha hmeta hp
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  have h := hprep n m B W hn hm hB hmb a prepared ha hmeta hp
  have hcap := hsize n inputLength m W hinput hs hmb hW
  apply h.trans
  have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hcap degree)
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using hh


theorem common_rounds_space_le (base : StructuredCalls.State 40 896) (n m B W K : ℕ)
    (hm : CounterPrograms.value (base.stacks 782) = m)
    (ha : ∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B W) :
    NativeLeafRun.roundsSpace base n m (SparseCode.distanceDenom m B)
      (NativeLeafRun.commonBound n m B W) K ≤
      max K (1000000 * (m + SparseCode.distanceDenom m B + NativeLeafRun.commonBound n m B W + 1) ^ 3) := by
  let S := HashQueryInputBounds.commonCap n m B W
  obtain ⟨hS, _, _, hd, hw, hb, _⟩ := HashQueryInputBounds.commonCap_bounds n m B W
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have hp : HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ S ^ 2 := by
    simpa only [HashCandidates.payloadWidth, pow_two] using Nat.mul_le_mul hd hw
  exact HashGreedyBudgets.staged_rounds_space_le base n m (SparseCode.distanceDenom m B)
    (NativeLeafRun.commonBound n m B W) K hm ha
    (by change _ ≤ 16 * S ^ 3; omega) (by change _ ≤ 16 * S ^ 3; omega)

/-- The actual produced preparation boundary and full streamed selector
share a fixed input polynomial, with the independent query prefix cap kept
separate from its running time. -/
theorem prepared_selector_space_polynomial :
    ∃ C degree : ℕ, ∀ n m B W K : ℕ, 0 < n → 0 < m → 0 < B → m ≤ n * B →
      let startupBound := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared base : StructuredCalls.State 40 896,
      (∀ i, (a.stacks i).length ≤ startupBound) → LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ startupBound + NativeLeafSetup.parameterTime m B startupBound
        (a.stacks 782).length (a.stacks 786).length) →
      CounterPrograms.value (base.stacks 782) = m →
      (∀ i, (base.stacks i).length ≤ retainedBound m B startupBound a prepared) →
      let L := NativeLeafRun.commonBound n m B (retainedBound m B startupBound a prepared)
      max (max (startupBound + 1) (continuationSpace m B startupBound a prepared))
        (NativeLeafRun.roundsSpace base n m (SparseCode.distanceDenom m B) L K) ≤
          max K (C * (n + m + B + W + 16) ^ degree) := by
  obtain ⟨C, d, hprep⟩ := prepared_common_bound_polynomial
  let D := 1000000 * (C + 20001) ^ 3
  refine ⟨C + D, (d + 4) * 3, ?_⟩
  intro n m B W K hn hm hB hmb startupBound a prepared base ha hmeta hp hmword hbase L
  let X := n + m + B + W + 16
  let R := retainedBound m B startupBound a prepared
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hh := hprep n m B W hn hm hB hmb a prepared ha hmeta hp
  have hL : L ≤ C * X ^ d := (le_max_right _ _).trans hh
  have hS := HashQueryInputBounds.commonCap_bounds n m B R
  have hR : R ≤ L := by
    have hlin := Nat.le_self_pow (show 3 ≠ 0 by decide) (HashQueryInputBounds.commonCap n m B R)
    change R ≤ 16 * HashQueryInputBounds.commonCap n m B R ^ 3
    omega
  have hb : ∀ i, (base.stacks i).length ≤ L := fun i => (hbase i).trans hR
  have hround := common_rounds_space_le base n m B R K hmword hb
  have hdepth := (distanceDenom_polynomial m B).trans
    (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left (show B + m + 1 ≤ X by dsimp [X]; omega) 4))
  have hp4 : X ^ 4 ≤ X ^ (d + 4) := Nat.pow_le_pow_right hX (by omega)
  have hpd : X ^ d ≤ X ^ (d + 4) := Nat.pow_le_pow_right hX (by omega)
  have hlinear : m + 1 ≤ X ^ (d + 4) := by
    apply (show m + 1 ≤ X by dsimp [X]; omega).trans
    exact Nat.le_self_pow (by omega) X
  have hz : m + SparseCode.distanceDenom m B + L + 1 ≤ (C + 20001) * X ^ (d + 4) := by
    have hl := hL.trans (Nat.mul_le_mul_left C hpd)
    have hd := hdepth.trans (Nat.mul_le_mul_left 20000 hp4)
    nlinarith only [hl, hd, hlinear]
  have hnumeric := Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hz 3)
  have heq : 1000000 * ((C + 20001) * X ^ (d + 4)) ^ 3 = D * X ^ ((d + 4) * 3) := by
    dsimp [D]
    rw [mul_pow, ← pow_mul, Nat.mul_assoc]
  rw [heq] at hnumeric
  have htarget := hnumeric.trans (Nat.mul_le_mul_right _ (show D ≤ C + D by omega))
  apply max_le
  · apply le_trans _ (le_max_right _ _)
    have ht := (le_max_left _ _).trans hh
    exact ht.trans ((Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (by omega))).trans
      (Nat.mul_le_mul_right _ (by omega)))
  · exact hround.trans (max_le_max le_rfl htarget)


/-- The actual disjoint choice and loaded input-word cap fix one polynomial
preparation and full selector space bound in original input length before all leaf calls. -/
theorem chosen_prepared_selector_space (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W K : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared base : StructuredCalls.State 40 896, (∀ i, (a.stacks i).length ≤ L) →
      LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      CounterPrograms.value (base.stacks 782) = m →
      (∀ i, (base.stacks i).length ≤ retainedBound m B L a prepared) →
      max (max (L + 1) (continuationSpace m B L a prepared))
        (NativeLeafRun.roundsSpace base n m (SparseCode.distanceDenom m B)
          (NativeLeafRun.commonBound n m B (retainedBound m B L a prepared)) K) ≤
          max K (C * (inputLength + 1) ^ degree) := by
  obtain ⟨C, degree, hprep⟩ := prepared_selector_space_polynomial
  obtain ⟨A, exponent, hsize⟩ := chosen_leaf_input_cap k wordCoefficient wordDegree
  refine ⟨C * A ^ degree, exponent * degree, ?_⟩
  intro n inputLength m W K hn hm hinput hs B hmb hW L a prepared base ha hmeta hp hmword hbase
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  have h := hprep n m B W K hn hm hB hmb a prepared base ha hmeta hp hmword hbase
  have hcap := hsize n inputLength m W hinput hs hmb hW
  apply h.trans
  apply max_le_max le_rfl
  have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hcap degree)
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using hh

open SqrtLog.CodeSetupCost

open Filter SqrtLog.Asymptotic SqrtLog.Statement
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
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

private theorem final_cap (inputLength prepareCap roundCap K L C d A e : ℕ)
    (hmain : max prepareCap roundCap ≤ max K (A * (inputLength + 1) ^ e))
    (hL : L ≤ C * (inputLength + 1) ^ d) :
    max prepareCap (max roundCap (max K (1000 * L + 100))) ≤
      max K ((A + 1000 * C + 100) * (inputLength + 1) ^ (d + e)) := by
  let P := (inputLength + 1) ^ (d + e)
  have hbase : 1 ≤ inputLength + 1 := by omega
  have hd : (inputLength + 1) ^ d ≤ P := Nat.pow_le_pow_right hbase (by omega)
  have he : (inputLength + 1) ^ e ≤ P := Nat.pow_le_pow_right hbase (by omega)
  have hP : 1 ≤ P := Nat.one_le_pow' _ _
  have hA : A * (inputLength + 1) ^ e ≤ (A + 1000 * C + 100) * P :=
    (Nat.mul_le_mul_left A he).trans (Nat.mul_le_mul_right P (by omega))
  have hmain' := hmain.trans (max_le_max le_rfl hA)
  have hl := hL.trans (Nat.mul_le_mul_left C hd)
  have hfinish : 1000 * L + 100 ≤ (A + 1000 * C + 100) * P := by
    nlinarith only [hl, hP, Nat.zero_le (A * P)]
  exact max_le ((le_max_left _ _).trans hmain')
    (max_le ((le_max_right _ _).trans hmain')
      (max_le (le_max_left _ _) (hfinish.trans (le_max_right _ _))))

/-- The actual preparation, same common-bound selector and paid final count
staging admit one fixed polynomial in the original input length. The genuine
query prefix cap remains separate, with no query duration charged as space. -/
theorem chosen_local_space (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W K : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let startupBound := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ started prepared base : State 40 896,
      (∀ i, (started.stacks i).length ≤ startupBound) →
      SqrtLog.LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ startupBound +
        NativeLeafSetup.parameterTime m B startupBound
          (started.stacks 782).length (started.stacks 786).length) →
      CounterPrograms.value (base.stacks 782) = m →
      (∀ i, (base.stacks i).length ≤
        NativeLeafPreparation.retainedBound m B startupBound started prepared) →
      let L := NativeLeafRun.commonBound n m B
        (NativeLeafPreparation.retainedBound m B startupBound started prepared)
      max (max (startupBound + 1)
          (NativeLeafPreparation.continuationSpace m B startupBound started prepared))
        (max (NativeLeafRun.roundsSpace base n m (SqrtLog.SparseCode.distanceDenom m B) L K)
          (max K (1000 * L + 100))) ≤ max K (C * (inputLength + 1) ^ degree) := by
  obtain ⟨C, d, hcommon⟩ :=
    LeafPreparationBudgets.chosen_prepared_common_bound k wordCoefficient wordDegree
  obtain ⟨A, e, hselector⟩ :=
    LeafPreparationBudgets.chosen_prepared_selector_space k wordCoefficient wordDegree
  refine ⟨A + 1000 * C + 100, d + e, ?_⟩
  intro n inputLength m W K hn hm hnI hs B hmB hW startupBound
    started prepared base hstarted hmetadata hprepared hmword hbase L
  have hc := hcommon n inputLength m W hn hm hnI hs hmB hW
    started prepared hstarted hmetadata hprepared
  have hr := hselector n inputLength m W K hn hm hnI hs hmB hW
    started prepared base hstarted hmetadata hprepared hmword hbase
  exact final_cap inputLength _ _ K L C d A e hr ((le_max_right _ _).trans hc)

/-- The actual loader uses exactly the body, ambient word and independent
setup-parameter cap. Their sum is polynomial in the original input length,
with coefficients and degree fixed before the input is chosen. -/
theorem loaded_input_bound (k parameterCoefficient parameterDegree n inputLength parameterBound : ℕ)
    (hn : n ≤ inputLength)
    (hp : parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree) :
    SparseCountProgram.formulaBound n k + (n + 1) + parameterBound ≤
      (3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient) *
        (inputLength + 1) ^ (k + 1 + parameterDegree) := by
  let P := (inputLength + 1) ^ (k + 1 + parameterDegree)
  have hb : 1 ≤ inputLength + 1 := by omega
  have hformula := formulaBound_polynomial n k
  have hbase : (n + 1) ^ (k + 1) ≤ P :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ inputLength + 1) (k + 1)).trans
      (Nat.pow_le_pow_right hb (by omega))
  have hparameter : (inputLength + 1) ^ parameterDegree ≤ P :=
    Nat.pow_le_pow_right hb (by omega)
  have hlinear : n + 1 ≤ P := by
    apply (show n + 1 ≤ inputLength + 1 by omega).trans
    simpa only [pow_one] using Nat.pow_le_pow_right hb
      (show 1 ≤ k + 1 + parameterDegree by omega)
  have hf := hformula.trans (Nat.mul_le_mul_left _ hbase)
  have hp' := hp.trans (Nat.mul_le_mul_left parameterCoefficient hparameter)
  change _ ≤ (3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient) * P
  nlinarith only [hf, hp', hlinear]

/-- Substitute the real three-word loader cap into the actual local-space
bound. The setup parameter word is the only incoming size datum, and its
producer polynomial fixes all constants before the original input. -/
theorem chosen_loaded_local_space_oai (k parameterCoefficient parameterDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m parameterBound K : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B →
      let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
      let startupBound := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ started prepared base : State 40 896,
      (∀ i, (started.stacks i).length ≤ startupBound) →
      SqrtLog.LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ startupBound +
        NativeLeafSetup.parameterTime m B startupBound
          (started.stacks 782).length (started.stacks 786).length) →
      CounterPrograms.value (base.stacks 782) = m →
      (∀ i, (base.stacks i).length ≤
        NativeLeafPreparation.retainedBound m B startupBound started prepared) →
      let L := NativeLeafRun.commonBound n m B
        (NativeLeafPreparation.retainedBound m B startupBound started prepared)
      max (max (startupBound + 1)
          (NativeLeafPreparation.continuationSpace m B startupBound started prepared))
        (max (NativeLeafRun.roundsSpace base n m (SqrtLog.SparseCode.distanceDenom m B) L K)
          (max K (1000 * L + 100))) ≤ max K (C * (inputLength + 1) ^ degree) := by
  obtain ⟨C, degree, hcap⟩ := chosen_local_space k
    (3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient)
    (k + 1 + parameterDegree)
  refine ⟨C, degree, ?_⟩
  intro n inputLength m parameterBound K hn hm hnI hs hp B hmB W startupBound
    started prepared base hstarted hmetadata hprepared hmword hbase L
  exact hcap n inputLength m W K hn hm hnI hs hmB
    (loaded_input_bound k parameterCoefficient parameterDegree n inputLength parameterBound hnI hp)
    started prepared base hstarted hmetadata hprepared hmword hbase

open SqrtLog Filter
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space_oai
