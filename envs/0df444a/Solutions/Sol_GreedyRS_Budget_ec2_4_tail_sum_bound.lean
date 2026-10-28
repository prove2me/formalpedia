-- Prove2me | solution 1 for GreedyRS.Budget.ec2_4_tail_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:42:27.863513+00:00
-- url     : https://prove2.me/submissions/de643e8b-f520-45d3-bca0-40da065ae8ce

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GRS4Aux
open GreedyRS.Greedy

instance isProb_std : IsProbabilityMeasure stdNormalSeq := by
  unfold stdNormalSeq; infer_instance

lemma coord_indep : iIndepFun (fun i (z : ℕ → ℝ) => z i) stdNormalSeq := by
  have := iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
    (X := fun _ (y : ℝ) => y) (fun _ => measurable_id)
  exact this

lemma coord_law (i : ℕ) : stdNormalSeq.map (fun z : ℕ → ℝ => z i) = gaussianReal 0 1 := by
  unfold stdNormalSeq
  exact Measure.infinitePi_map_eval _ i

lemma sum_law (N : ℕ) :
    stdNormalSeq.map (fun z : ℕ → ℝ => ∑ j ∈ Finset.range N, z j) = gaussianReal 0 (N : ℝ≥0) := by
  induction N with
  | zero => simp [gaussianReal_zero_var, stdNormalSeq]
  | succ N ih =>
    have hind : IndepFun (∑ j ∈ Finset.range N, fun z : ℕ → ℝ => z j) (fun z => z N)
        stdNormalSeq :=
      coord_indep.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i)
        (by simp)
    have hfun : (fun z : ℕ → ℝ => ∑ j ∈ Finset.range (N+1), z j) =
        (∑ j ∈ Finset.range N, fun z : ℕ → ℝ => z j) + (fun z => z N) := by
      funext z; simp [Finset.sum_range_succ]
    have hS : stdNormalSeq.map (∑ j ∈ Finset.range N, fun z : ℕ → ℝ => z j) =
        gaussianReal 0 (N : ℝ≥0) := by
      rw [← ih]; congr 1; funext z; simp
    rw [hfun, gaussianReal_add_gaussianReal_of_indepFun hind hS (coord_law N)]
    congr 1 <;> push_cast <;> ring


lemma prob_le (x : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    stdNormalSeq {z | x ≤ zbar z N} ≤ ENNReal.ofReal (1 - Phi (Real.sqrt (N : ℝ) * x)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  set a := Real.sqrt (N : ℝ) * x
  have hmeasS : Measurable (fun z : ℕ → ℝ => ∑ j ∈ Finset.range N, z j) := by fun_prop
  have h1 : {z : ℕ → ℝ | x ≤ zbar z N} =
      (fun z : ℕ → ℝ => ∑ j ∈ Finset.range N, z j) ⁻¹' {y | x ≤ y / N} := by
    ext z; simp [zbar]
  have hmeasA : MeasurableSet {y : ℝ | x ≤ y / N} := measurableSet_le measurable_const (by fun_prop)
  rw [h1, ← Measure.map_apply hmeasS hmeasA, sum_law N]
  have hG : gaussianReal 0 (N : ℝ≥0) =
      (gaussianReal 0 1).map (fun u => Real.sqrt (N : ℝ) * u) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt hNpos.le]
  rw [hG, Measure.map_apply (by fun_prop) hmeasA]
  have h2 : (fun u => Real.sqrt (N : ℝ) * u) ⁻¹' {y : ℝ | x ≤ y / N} = Set.Ici a := by
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ici, a]
    have hN' : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    rw [le_div_iff₀ hNpos]
    have e : Real.sqrt N * (Real.sqrt N * x) = x * N := by rw [← mul_assoc, hN']; ring
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_left hc hsq
      linarith
    · intro h
      have := mul_le_mul_of_nonneg_left h hsq.le
      linarith
  rw [h2]
  have h3 : ENNReal.ofReal (1 - Phi a) = gaussianReal 0 1 (Set.Ioi a) := by
    rw [Phi, ENNReal.ofReal_sub _ (cdf_nonneg _ _), ofReal_cdf, ENNReal.ofReal_one,
      ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
  rw [h3, ← Set.Ioi_insert]
  calc gaussianReal 0 1 (insert a (Set.Ioi a))
      ≤ gaussianReal 0 1 {a} + gaussianReal 0 1 (Set.Ioi a) := by
        rw [Set.insert_eq]; exact measure_union_le _ _
    _ = gaussianReal 0 1 (Set.Ioi a) := by
        rw [gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton), zero_add]

lemma pointwise (x : ℝ) (n0 : ℕ) (z : ℕ → ℝ) :
    ((crossTime x n0 z : ℕ∞) : ℝ≥0∞) ≤ (n0 : ℝ≥0∞) +
      ∑' n : ℕ, Set.indicator {z : ℕ → ℝ | x ≤ zbar z (n0 + n)} (fun _ => (1 : ℝ≥0∞)) z := by
  classical
  by_cases h : ∃ m, zbar z (n0 + m) < x
  · let m := Nat.find h
    have hm : zbar z (n0 + m) < x := Nat.find_spec h
    have hct : crossTime x n0 z ≤ ((n0 + m : ℕ) : ℕ∞) :=
      iInf₂_le (n0 + m) ⟨Nat.le_add_right _ _, hm⟩
    calc ((crossTime x n0 z : ℕ∞) : ℝ≥0∞) ≤ (((n0 + m : ℕ) : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.2 hct
      _ = (n0 : ℝ≥0∞) + ∑ n ∈ Finset.range m,
            Set.indicator {z : ℕ → ℝ | x ≤ zbar z (n0 + n)} (fun _ => (1 : ℝ≥0∞)) z := by
          rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
          · simp
          · intro n hn
            have hn' : n < m := Finset.mem_range.1 hn
            have : ¬ zbar z (n0 + n) < x := Nat.find_min h hn'
            simp [Set.indicator, not_lt.1 this]
      _ ≤ _ := by gcongr; exact ENNReal.sum_le_tsum _
  · push Not at h
    have : ∑' n : ℕ, Set.indicator {z : ℕ → ℝ | x ≤ zbar z (n0 + n)} (fun _ => (1 : ℝ≥0∞)) z = ⊤ := by
      simp [Set.indicator, h]
    rw [this]; simp

lemma tail_sum (x : ℝ) (n0 : ℕ) (hn0 : 1 ≤ n0) :
    Cn0 x n0 ≤ (n0 : ℝ≥0∞) + ∑' n : ℕ,
      ENNReal.ofReal (1 - Phi (Real.sqrt ((n0 + n : ℕ) : ℝ) * x)) := by
  have hmeas : ∀ n : ℕ, MeasurableSet {z : ℕ → ℝ | x ≤ zbar z (n0 + n)} := by
    intro n
    exact measurableSet_le measurable_const (by unfold zbar; fun_prop)
  calc Cn0 x n0 ≤ ∫⁻ z, ((n0 : ℝ≥0∞) + ∑' n : ℕ,
        Set.indicator {z : ℕ → ℝ | x ≤ zbar z (n0 + n)} (fun _ => (1 : ℝ≥0∞)) z) ∂stdNormalSeq :=
        lintegral_mono (fun z => pointwise x n0 z)
    _ = (n0 : ℝ≥0∞) + ∑' n : ℕ, stdNormalSeq {z : ℕ → ℝ | x ≤ zbar z (n0 + n)} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum (fun n =>
          (measurable_const.indicator (hmeas n)).aemeasurable)]
        congr 1
        congr 1; funext n
        rw [lintegral_indicator_const (hmeas n), one_mul]
    _ ≤ _ := by
        gcongr with n
        exact prob_le x (n0 + n) (by omega)

end GRS4Aux

theorem solution (x : ℝ) (_hx : 0 < x) (n0 : ℕ) (hn0 : 1 ≤ n0) :
    GreedyRS.Greedy.Cn0 x n0 ≤ (n0 : ℝ≥0∞) + ∑' n : ℕ, ENNReal.ofReal (1 - GreedyRS.Greedy.Phi (Real.sqrt ((n0 + n : ℕ) : ℝ) * x)) :=
  GRS4Aux.tail_sum x n0 hn0
