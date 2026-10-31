-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:10:15.293449+00:00
-- url     : https://prove2.me/submissions/fa978265-d72f-4afa-86ff-6eb80e000b6a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S172
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_LeafPreparationBudgets_continuationTime_le_envelope
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafSetup_canonicalParameterTime_polynomial

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

open SqrtLog.CodeSetupCost

/-- The time bound of the actual full preparation is a fixed polynomial in
its ordinary input parameters and the original explicit worst-case code
budget. Startup, parameter arithmetic, depth expansion and suffix work are
included in the same expression. -/
theorem full_time_polynomial_envelope :
    ∃ C degree : ℕ, ∀ n m B W H wordCap : ℕ, 0 < m → 0 < B →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      SparseCode.localRows m B ≤ H → SparseCode.degree m B ≤ H →
      SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H →
      SparseCode.dimension m B ≤ H →
      (prepared.stacks 800).length ≤ wordCap →
      (prepared.stacks 801).length ≤ wordCap →
      NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared ≤
        C * (n + m + B + W + envelope 3000000000000 H wordCap + 16) ^ degree := by
  obtain ⟨Cp, dp, hparameter⟩ := NativeLeafSetup.canonicalParameterTime_polynomial
  refine ⟨30000000000000000001 * (Cp + 20001) ^ 6, (dp + 4) * 6, ?_⟩
  intro n m B W H wordCap hm hB L a prepared ha hmeta hp ht hD hd hr hq hDl
  let A := L + NativeLeafSetup.parameterTime m B L
    (a.stacks 782).length (a.stacks 786).length
  let X := n + m + B + W + envelope 3000000000000 H wordCap + 16
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hA : A + 1 ≤ Cp * X ^ dp :=
    (hparameter n m B W _ _ hm hB (ha 782) (ha 786)).trans
      (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left (by dsimp [X]; omega) dp))
  have hpowers : X ^ dp ≤ X ^ (dp + 4) := Nat.pow_le_pow_right hX (by omega)
  have hfour : X ^ 4 ≤ X ^ (dp + 4) := Nat.pow_le_pow_right hX (by omega)
  have hlinear : X ≤ X ^ (dp + 4) := Nat.le_self_pow (by omega) X
  have hdepth : SparseCode.distanceDenom m B ≤ 20000 * X ^ 4 :=
    (distanceDenom_polynomial m B).trans (Nat.mul_le_mul_left 20000
      (Nat.pow_le_pow_left (by dsimp [X]; omega) 4))
  have hE : envelope 3000000000000 H wordCap ≤ X := by dsimp [X]; omega
  have hZ : A + SparseCode.distanceDenom m B + envelope 3000000000000 H wordCap + 1 ≤
      (Cp + 20001) * X ^ (dp + 4) := by
    have hAp := hA.trans (Nat.mul_le_mul_left Cp hpowers)
    have hdep := hdepth.trans (Nat.mul_le_mul_left 20000 hfour)
    nlinarith only [hAp, hdep, hE, hlinear]
  have ht0 := continuationTime_le_envelope m B L H wordCap a prepared
    ha hmeta hp ht hD hd hr hq hDl
  have ht1 := ht0.trans (Nat.mul_le_mul_left 30000000000000000000
    (Nat.pow_le_pow_left hZ 6))
  have heq : ((Cp + 20001) * X ^ (dp + 4)) ^ 6 =
      (Cp + 20001) ^ 6 * X ^ ((dp + 4) * 6) := by rw [mul_pow, ← pow_mul]
  rw [heq] at ht1
  have hsA : NativeLeafSetup.canonicalStartTime n m W ≤ A := by dsimp [A, L]; omega
  have hcoef : Cp ≤ (Cp + 20001) ^ 6 :=
    (show Cp ≤ Cp + 20001 by omega).trans (Nat.le_self_pow (by decide) _)
  have hexp : X ^ dp ≤ X ^ ((dp + 4) * 6) := Nat.pow_le_pow_right hX (by omega)
  have hstart : NativeLeafSetup.canonicalStartTime n m W ≤
      (Cp + 20001) ^ 6 * X ^ ((dp + 4) * 6) :=
    hsA.trans ((Nat.le_of_succ_le hA).trans (Nat.mul_le_mul hcoef hexp))
  change _ ≤ 30000000000000000001 * (Cp + 20001) ^ 6 * X ^ ((dp + 4) * 6)
  nlinarith only [ht1, hstart]

/-- The actual chosen sparsification bound and an independently produced
input-word cap replace all ordinary preparation parameters by the original
input length. The old explicit code envelope remains visible. -/
theorem chosen_preparation_time_envelope_oai (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W H wordCap : ℕ,
      0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      SparseCode.localRows m B ≤ H → SparseCode.degree m B ≤ H →
      SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H →
      SparseCode.dimension m B ≤ H →
      (prepared.stacks 800).length ≤ wordCap →
      (prepared.stacks 801).length ≤ wordCap →
      NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared ≤
        C * (inputLength + envelope 3000000000000 H wordCap + 1) ^ degree := by
  obtain ⟨Cp, dp, hprep⟩ := full_time_polynomial_envelope
  obtain ⟨Cs, ds, hsize⟩ := chosen_leaf_input_cap k wordCoefficient wordDegree
  refine ⟨Cp * (Cs + 1) ^ dp, (ds + 1) * dp, ?_⟩
  intro n inputLength m W H wordCap hm hn hs B hmb hW L a prepared ha hmeta hp ht hD hd hr hq hDl
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  let X := inputLength + envelope 3000000000000 H wordCap + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hcap := hsize n inputLength m W hn hs hmb hW
  change n + m + B + W + 16 ≤ Cs * (inputLength + 1) ^ ds at hcap
  have hb : inputLength + 1 ≤ X := by dsimp [X]; omega
  have hpoly : (inputLength + 1) ^ ds ≤ X ^ (ds + 1) :=
    (Nat.pow_le_pow_left hb ds).trans (Nat.pow_le_pow_right hX (by omega))
  have hlinear : X ≤ X ^ (ds + 1) := Nat.le_self_pow (by omega) X
  have hcode : envelope 3000000000000 H wordCap ≤ X := by dsimp [X]; omega
  have htotal : n + m + B + W + envelope 3000000000000 H wordCap + 16 ≤
      (Cs + 1) * X ^ (ds + 1) := by
    have hh := hcap.trans (Nat.mul_le_mul_left Cs hpoly)
    nlinarith only [hh, hlinear, hcode]
  have hp0 := hprep n m B W H wordCap hm hB a prepared ha hmeta hp ht hD hd hr hq hDl
  have hp1 := hp0.trans (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left htotal dp))
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using hp1

open Filter SqrtLog.Asymptotic SqrtLog.Statement
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope_oai
