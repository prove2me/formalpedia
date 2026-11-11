-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery_conditional_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:16:08.717254+00:00
-- url     : https://prove2.me/submissions/2ac601c1-3e33-4341-9936-fa6ba5f0f986

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K066
import Definitions.Def_Q224R002
import Theorems.Thm_OAI_MetricKMedianRecovery_RefinedRecovery_metric_length_bound_s35

section
-- module Solutions.Q224_RR.KMedianRecovery_Encoding_Reencode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

lemma pairBits_length (p : List Bool × List Bool) :
    (pairBits p).length = 2*p.1.length+1+p.2.length := by
  rcases p with ⟨x,y⟩
  induction x with
  | nil => simp [pairBits,Nat.add_comm]
  | cons b xs ih =>
    simp only [pairBits,List.flatMap_cons,List.cons_append,List.nil_append,List.length_cons] at ih ⊢
    omega

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_CheckedInput
attribute [-simp] _root_.OAI.MetricKMedian.Instance.restrict_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery.CheckedInput

open MetricKMedian MetricKMedian.Binary MetricKMedian.Binary.Automatic
open MetricKMedian.Binary.Automatic.Poly
open MetricKMedian.InstanceProgram (Raw view)
open MetricKMedian.SparseGraph.ListOperation (Row Table setView)

lemma distance_view (I : Instance) (i j : Fin I.n) :
    distance (view I) i j = I.distance i j := by
  simp [distance, view, i.isLt, j.isLt]

lemma valid_view (I : Instance) : valid (view I) = true := by
  have hc : ((setView I.facilities).filter id).length = I.facilities.card :=
    MetricKMedian.EncodingLists.bool_card I.facilities
  change (decide (0 < I.k) && decide (I.k ≤ (setView I.facilities |>.filter id).length) &&
    metricTest (view I)) = true
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff]
  refine ⟨⟨by exact decide_eq_true (by have := I.k_pos; omega),
    by simpa only [hc, decide_eq_true_iff] using I.k_le⟩, ?_⟩
  simp only [metricTest, rows, n, view, setView, List.length_ofFn, List.all_map,
    List.all_eq_true, List.mem_range, Function.comp_apply, id_eq,
    Bool.and_eq_true_iff, beq_iff_eq]
  intro i hi j hj
  have he (a b : ℕ) (ha : a < I.n) (hb : b < I.n) :
      distance (view I) a b = I.distance ⟨a, ha⟩ ⟨b, hb⟩ := distance_view I ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply decide_eq_true
    change 0 ≤ distance (view I) i j
    rw [he i j hi hj]
    exact I.distance_nonneg _ _
  · apply _root_.decide_eq_decide.mpr
    change distance (view I) i j = 0 ↔ i = j
    rw [he i j hi hj, I.distance_eq_zero]
    simp
  · apply decide_eq_true
    change distance (view I) i j = distance (view I) j i
    rw [he i j hi hj, he j i hj hi]
    exact I.distance_symm _ _
  · intro k hk
    apply decide_eq_true
    change distance (view I) i k ≤ distance (view I) i j + distance (view I) j k
    rw [he i k hi hk, he i j hi hj, he j k hj hk]
    exact I.distance_triangle _ _ _

private lemma view_injective : Function.Injective view := by
  rintro ⟨N, d, C, F, k, h₁, h₂, h₃, h₄, h₅, h₆⟩
    ⟨M, d', C', F', k', h₁', h₂', h₃', h₄', h₅', h₆'⟩ hv
  have hn : N = M := by
    have hh := congrArg (fun x : Raw => x.1.2.length) hv
    simpa only [view, setView, List.length_ofFn] using hh
  subst M
  have hC : C = C' := by
    have hh := List.ofFn_injective (congrArg (fun x : Raw => x.1.1) hv)
    exact Finset.ext (fun i => decide_eq_decide.mp (congrFun hh i))
  have hF : F = F' := by
    have hh := List.ofFn_injective (congrArg (fun x : Raw => x.1.2) hv)
    exact Finset.ext (fun i => decide_eq_decide.mp (congrFun hh i))
  have hd : d = d' := by
    have hh := List.ofFn_injective (congrArg (fun x : Raw => x.2.2) hv)
    funext i
    exact List.ofFn_injective (congrFun hh i)
  have hk : k = k' := congrArg (fun x : Raw => x.2.1) hv
  subst C'
  subst F'
  subst d'
  subst k'
  rfl

lemma checked_view (I : Instance) : checked (view I) = I := by
  apply view_injective
  rw [checked, dite_eq_left (valid_view I), ← normalized_view (view I) (valid_view I)]
  simp [normalized, rows, n, view, setView, range_map, distance]

end MetricKMedianRecovery.RefinedRecovery.CheckedInput

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_ThresholdInput
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
attribute [-simp] _root_.OAI.MetricKMedian.Instance.restrict_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

namespace Input

lemma asInstance_bits (I : Input) :
    MetricKMedian.encodeInstance I.asInstance = I.metric.bits := by
  have hrat (q : ℚ) : MetricKMedian.encodeRat q = RationalMetricInput.rationalBits q := by
    simp only [MetricKMedian.encodeRat, RationalMetricInput.rationalBits,
      MetricKMedian.encodeNat, RationalMetricInput.natBits, Rat.num_neg]
  simp only [MetricKMedian.encodeInstance, RationalMetricInput.bits, asInstance,
    MetricKMedian.encodeNat, RationalMetricInput.natBits, hrat]

lemma asInstance_cost (I : Input) (S : Finset I.Point) :
    MetricKMedian.cost I.asInstance S = (I.metric.cost S : ℝ) := by
  rw [← MetricKMedian.Instance.cast_rationalCost]
  congr 1
  unfold MetricKMedian.rationalCost RationalMetricInput.cost
  by_cases hS : S.Nonempty
  · simp only [dite_eq_left hS]
    apply Finset.sum_congr rfl
    intro p _
    unfold MetricKMedian.rationalNearest
    rw [dite_eq_left hS]
    apply le_antisymm
    · apply Finset.le_inf'
      intro i hi
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · apply Finset.le_min'
      intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.inf'_le _ hi
  · simp [MetricKMedian.rationalNearest, hS]

lemma optimum_le_comparison (I : Input) {μ : ℚ} {L₀ : ℝ}
    (C : Certificate I μ L₀) :
    MetricKMedian.optimum I.asInstance ≤ (I.metric.cost C.centers : ℝ) := by
  have hn : C.centers.Nonempty := Finset.card_pos.mp (by
    rw [C.same_card, I.anchor_card]
    exact I.metric.budget_pos)
  rw [← I.asInstance_cost]
  exact I.asInstance.optimum_le C.centers_subset hn (C.same_card.trans I.anchor_card).le

lemma decode_mask (I : Input) (S : Finset I.Point) (hS : S ⊆ I.metric.facilities) :
    I.metric.decodeOutput (List.ofFn (fun i : I.Point => decide (i ∈ S))) = S := by
  ext i
  simp only [RationalMetricInput.decodeOutput, Finset.mem_filter,
    List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some, Fin.eta, decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi => hS hi)

end Input

end MetricKMedianRecovery.RefinedRecovery

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_Work
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

private lemma polynomial_power_bound (p : Polynomial ℕ) :
    ∃ c d : ℕ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → p.eval n ≤ c*n^d := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, d, ha, hp⟩ := hp
    obtain ⟨b, e, hb, hq⟩ := hq
    refine ⟨a+b, d+e, by omega, fun n hn => ?_⟩
    rw [Polynomial.eval_add, add_mul]
    apply Nat.add_le_add
    · exact (hp n hn).trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_right hn (by omega)))
    · exact (hq n hn).trans (Nat.mul_le_mul_left b (Nat.pow_le_pow_right hn (by omega)))
  | monomial d a =>
    refine ⟨a+1, d, by omega, fun n _ => ?_⟩
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_right _ (by omega)

lemma zero_random_polynomialWork (A : BinaryRandomizedAlgorithm)
    (hA : A.randomBits = 0) (b : Polynomial ℕ) : PolynomialWork A b := by
  let p := metricLengthPolynomial b
  let q := 2*p + 2*Polynomial.X + 2
  let w := Polynomial.X + A.computation.time.comp (2*Polynomial.X+1)
  obtain ⟨c, d, hc, hpow⟩ := polynomial_power_bound (w.comp q)
  let K : ℝ := 3 + 1/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K] <;> positivity
  refine ⟨c*K^d, by positivity, d, ?_⟩
  intro I hI ζ hζ hζ1
  let t := I.size + precision ζ + 1
  have hseed : seedLength A I ζ = 0 := by simp [seedLength, hA]
  have hlen : (queryBits I ζ).length ≤ q.eval t := by
    have hM := (metric_length_bound_s35 I b hI).trans
      (MetricKMedian.Binary.polynomial_eval_mono p (show I.size ≤ t by dsimp [t]; omega))
    have hn : I.metric.pointCount ≤ I.size := by
      calc
        _ = (I.metric.clients ∪ I.metric.facilities).card := by rw [I.metric.covered]; simp
        _ ≤ I.size := Finset.card_union_le _ _
    simp only [queryBits, BitMachine.pairBits_length, Input.anchorBits,
      List.length_append, List.length_ofFn, List.length_replicate]
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    omega
  have hw : workBound A I ζ ≤ c*t^d := by
    have hb : workBound A I ζ = w.eval (queryBits I ζ).length := by
      simp [workBound, hseed, w, BitMachine.pairBits_length]
    rw [hb]
    exact (MetricKMedian.Binary.polynomial_eval_mono w hlen).trans
      (by simpa only [Polynomial.eval_comp] using hpow t (by dsimp [t]; omega))
  have hlog : 0 ≤ Real.log (1/ζ) := Real.log_nonneg (by
    rw [le_div_iff₀ hζ]
    linarith)
  have hprec : (precision ζ : ℝ) ≤ Real.log (1/ζ)/Real.log 2 + 1 := by
    exact (Nat.ceil_lt_add_one (div_nonneg hlog hlog2.le)).le
  have ht : (t : ℝ) ≤ K*((I.size : ℝ)+1)*(1+Real.log (1/ζ)) := by
    have hN : (0 : ℝ) ≤ I.size := Nat.cast_nonneg _
    have hi : 0 ≤ 1/Real.log 2 := by positivity
    have hprec' : (precision ζ : ℝ)+1 ≤ K*(1+Real.log (1/ζ)) := by
      change (precision ζ : ℝ) ≤ Real.log (1/ζ)*(Real.log 2)⁻¹+1 at hprec
      rw [one_div] at hi
      dsimp only [K]
      rw [one_div]
      nlinarith [mul_nonneg hi hlog]
    calc
      (t : ℝ) ≤ ((I.size : ℝ)+1)*((precision ζ : ℝ)+1) := by
        dsimp [t]
        push_cast
        nlinarith [mul_nonneg hN (Nat.cast_nonneg (α := ℝ) (precision ζ))]
      _ ≤ ((I.size : ℝ)+1)*(K*(1+Real.log (1/ζ))) := by gcongr
      _ = _ := by ring
  have hwR : (workBound A I ζ : ℝ) ≤ (c : ℝ)*(t : ℝ)^d := by exact_mod_cast hw
  apply hwR.trans
  calc
    _ ≤ (c : ℝ)*(K*((I.size : ℝ)+1)*(1+Real.log (1/ζ)))^d := by gcongr
    _ = _ := by simp only [mul_pow] <;> ring

end MetricKMedianRecovery.RefinedRecovery

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_ConditionalRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

open MetricKMedian.Binary

private lemma quote_eq (xs : List Bool) :
    quote xs = xs.flatMap (fun b => [true, b]) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [quote, ih]

private lemma first_pair (x y : List Bool) : first (pairBits (x, y)) = x := by
  simpa only [first, pairBits, ← quote_eq, Bool.false_eq_true, ite_false, if_false] using
    WordTransducer.projecting_pair false x y

private lemma algorithm_run {f : MetricKMedian.Instance → List Bool}
    (P : PolyProgram MetricKMedian.InstanceProgram.encode id f) (I : Input) (ζ : ℝ)
    (s : Seed (algorithm P) I ζ) :
    (algorithm P).run (queryBits I ζ, List.ofFn s) = f I.asInstance := by
  simp only [algorithm, queryBits, first_pair, ← I.asInstance_bits,
    MetricKMedian.InputParser.raw_encoded, CheckedInput.checked_view]

theorem refined_recovery_conditional_s35_oai (H : CompanionThresholdInput) : refinedRecoveryClaim := by
  intro bound ε L₀ μ hε _ _ _ _
  obtain ⟨f, ⟨P⟩, hf⟩ := H ε hε
  refine ⟨algorithm P, zero_random_polynomialWork _ rfl bound, ?_⟩
  intro I _ ζ hζ _
  have houtput (s : Seed (algorithm P) I ζ) :
      ∃ S : Finset I.Point, I.metric.Feasible S ∧ output (algorithm P) I ζ s = S ∧
        (I.metric.cost S : ℝ) ≤ (1+2/Real.exp 1+ε)*MetricKMedian.optimum I.asInstance := by
    obtain ⟨S, hSF, hS, hk, hout, hcost⟩ := hf I.asInstance
    refine ⟨S, ⟨hSF, hk, fun _ => hS⟩, ?_, ?_⟩
    · rw [output, algorithm_run, hout, I.decode_mask S hSF]
    · rwa [I.asInstance_cost] at hcost
  refine ⟨fun s => by obtain ⟨S, hS, he, _⟩ := houtput s; exact he.symm ▸ hS, ?_⟩
  intro C
  have hall (s : Seed (algorithm P) I ζ) :
      (I.metric.cost (output (algorithm P) I ζ s) : ℝ) ≤
        (1+2/Real.exp 1+ε)*(I.metric.cost C.centers : ℝ) := by
    obtain ⟨S, _, he, hc⟩ := houtput s
    rw [he]
    exact hc.trans (mul_le_mul_of_nonneg_left (I.optimum_le_comparison C) (by positivity))
  have hprob : successProbability (algorithm P) I ζ
      ((1+2/Real.exp 1+ε)*(I.metric.cost C.centers : ℝ)) = 1 := by
    classical
    simp only [successProbability, hall, Finset.filter_true, Finset.card_univ,
      Seed, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat]
    exact div_self (show (2 : ℝ) ^ seedLength (algorithm P) I ζ ≠ 0 by positivity)
  rw [hprob]
  linarith

end MetricKMedianRecovery.RefinedRecovery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery_conditional_s35_oai := @OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery_conditional_s35_oai
