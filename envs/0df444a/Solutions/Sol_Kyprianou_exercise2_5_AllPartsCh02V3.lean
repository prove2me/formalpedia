-- Prove2me | solution 1 for Kyprianou.exercise2_5_AllPartsCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T18:00:24.828805+00:00
-- url     : https://prove2.me/submissions/98498496-bf31-4cf1-8ff5-f67795e18a4c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Exercise25Helpers

/-! ### Part (i): Cantor staircase via uniform contraction series -/

private noncomputable def cantorStep (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 1 / 3 then (1 / 2 : ℝ) * h (3 * x)
  else if x ≤ 2 / 3 then (1 / 2 : ℝ)
  else (1 / 2 : ℝ) + (1 / 2 : ℝ) * h (3 * x - 2)

private noncomputable def cantorSeq : ℕ → ℝ → ℝ
  | 0, x => max 0 (min 1 x)
  | n + 1, x => cantorStep (cantorSeq n) x

private lemma cantorSeq_bounds (n : ℕ) (x : ℝ) :
    0 ≤ cantorSeq n x ∧ cantorSeq n x ≤ 1 := by
  induction n generalizing x with
  | zero =>
    simp only [cantorSeq]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  | succ n ih =>
    simp only [cantorSeq, cantorStep]
    split_ifs
    · obtain ⟨h0, h1⟩ := ih (3 * x); constructor <;> linarith
    · constructor <;> norm_num
    · obtain ⟨h0, h1⟩ := ih (3 * x - 2); constructor <;> linarith

private lemma cantorSeq_eq_zero_of_le (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    cantorSeq n x = 0 := by
  induction n generalizing x with
  | zero =>
    simp only [cantorSeq]
    rw [min_eq_right (by linarith), max_eq_left hx]
  | succ n ih =>
    simp only [cantorSeq, cantorStep, if_pos (by linarith : x ≤ 1 / 3)]
    rw [ih (by linarith : 3 * x ≤ 0), mul_zero]

private lemma cantorSeq_eq_one_of_ge (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    cantorSeq n x = 1 := by
  induction n generalizing x with
  | zero =>
    simp only [cantorSeq]
    rw [min_eq_left hx, max_eq_right (by norm_num)]
  | succ n ih =>
    simp only [cantorSeq, cantorStep,
      if_neg (by linarith : ¬ x ≤ 1 / 3),
      if_neg (by linarith : ¬ x ≤ 2 / 3)]
    rw [ih (by linarith : 1 ≤ 3 * x - 2)]
    norm_num

private lemma cantorSeq_mono (n : ℕ) : Monotone (cantorSeq n) := by
  induction n with
  | zero =>
    intro x y hxy
    simp only [cantorSeq]
    exact max_le_max le_rfl (min_le_min le_rfl hxy)
  | succ n ih =>
    intro x y hxy
    simp only [cantorSeq, cantorStep]
    by_cases hx1 : x ≤ 1 / 3
    · rw [if_pos hx1]
      by_cases hy1 : y ≤ 1 / 3
      · rw [if_pos hy1]; linarith [ih (by linarith : 3 * x ≤ 3 * y)]
      · rw [if_neg hy1]
        have hx_le := (cantorSeq_bounds n (3 * x)).2
        split_ifs
        · linarith
        · have hy_ge := (cantorSeq_bounds n (3 * y - 2)).1; linarith
    · rw [if_neg hx1]
      have hy1 : ¬ y ≤ 1 / 3 := by linarith
      rw [if_neg hy1]
      by_cases hx2 : x ≤ 2 / 3
      · rw [if_pos hx2]
        split_ifs
        · exact le_rfl
        · have hy_ge := (cantorSeq_bounds n (3 * y - 2)).1; linarith
      · rw [if_neg hx2, if_neg (by linarith : ¬ y ≤ 2 / 3)]
        linarith [ih (by linarith : 3 * x - 2 ≤ 3 * y - 2)]

private lemma cantorSeq_continuous (n : ℕ) : Continuous (cantorSeq n) := by
  induction n with
  | zero =>
    exact continuous_const.max (continuous_const.min continuous_id)
  | succ n ih =>
    have hpiece1 : Continuous (fun x : ℝ => (1 / 2 : ℝ) * cantorSeq n (3 * x)) :=
      continuous_const.mul (ih.comp (continuous_const.mul continuous_id))
    have hpiece3 : Continuous (fun x : ℝ => (1 / 2 : ℝ) + (1 / 2 : ℝ) * cantorSeq n (3 * x - 2)) :=
      continuous_const.add (continuous_const.mul (ih.comp ((continuous_const.mul continuous_id).sub continuous_const)))
    have hright : Continuous (fun x : ℝ =>
        if x ≤ 2 / 3 then (1 / 2 : ℝ) else (1 / 2 : ℝ) + (1 / 2 : ℝ) * cantorSeq n (3 * x - 2)) := by
      refine Continuous.if_le continuous_const hpiece3 continuous_id continuous_const ?_
      intro x hx
      have h0 : 3 * x - 2 = 0 := by linarith
      rw [h0, cantorSeq_eq_zero_of_le n le_rfl]; norm_num
    refine Continuous.if_le hpiece1 hright continuous_id continuous_const ?_
    intro x hx
    rw [if_pos (by linarith : x ≤ 2 / 3)]
    have h1 : 3 * x = 1 := by linarith
    rw [h1, cantorSeq_eq_one_of_ge n le_rfl]; norm_num

private lemma cantorSeq_step_diff (n : ℕ) (x : ℝ) :
    |cantorSeq (n + 1) x - cantorSeq n x| ≤ (1 / 2 : ℝ) ^ n := by
  induction n generalizing x with
  | zero =>
    have h0 := cantorSeq_bounds 0 x
    have h1 := cantorSeq_bounds 1 x
    rw [pow_zero, abs_le]
    constructor <;> linarith
  | succ n ih =>
    change |cantorStep (cantorSeq (n + 1)) x - cantorStep (cantorSeq n) x| ≤ (1 / 2 : ℝ) ^ (n + 1)
    unfold cantorStep
    split_ifs
    · have : (1 / 2 : ℝ) * cantorSeq (n + 1) (3 * x) - (1 / 2 : ℝ) * cantorSeq n (3 * x) =
          (1 / 2 : ℝ) * (cantorSeq (n + 1) (3 * x) - cantorSeq n (3 * x)) := by ring
      rw [this, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), pow_succ']
      exact mul_le_mul_of_nonneg_left (ih (3 * x)) (by norm_num)
    · rw [sub_self, abs_zero]; positivity
    · have : ((1 / 2 : ℝ) + (1 / 2 : ℝ) * cantorSeq (n + 1) (3 * x - 2)) -
          ((1 / 2 : ℝ) + (1 / 2 : ℝ) * cantorSeq n (3 * x - 2)) =
          (1 / 2 : ℝ) * (cantorSeq (n + 1) (3 * x - 2) - cantorSeq n (3 * x - 2)) := by ring
      rw [this, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), pow_succ']
      exact mul_le_mul_of_nonneg_left (ih (3 * x - 2)) (by norm_num)

private noncomputable def cantorF (x : ℝ) : ℝ :=
  cantorSeq 0 x + ∑' n : ℕ, (cantorSeq (n + 1) x - cantorSeq n x)

private lemma cantorSeq_tendsto_cantorF (x : ℝ) :
    Tendsto (fun n => cantorSeq n x) atTop (nhds (cantorF x)) := by
  have hsum : Summable (fun n : ℕ => cantorSeq (n + 1) x - cantorSeq n x) :=
    Summable.of_norm_bounded (g := fun n : ℕ => (1 / 2 : ℝ) ^ n)
      summable_geometric_two (fun n => by simpa [Real.norm_eq_abs] using cantorSeq_step_diff n x)
  have hhas := hsum.hasSum.tendsto_sum_nat
  have hteles : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (cantorSeq (k + 1) x - cantorSeq k x)) =
        cantorSeq n x - cantorSeq 0 x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  simp_rw [hteles] at hhas
  have hadd := (tendsto_const_nhds (x := cantorSeq 0 x)).add hhas
  simpa only [cantorF, add_sub_cancel] using hadd

private lemma cantorF_continuous : Continuous cantorF := by
  refine (cantorSeq_continuous 0).add ?_
  exact continuous_tsum
    (fun n => (cantorSeq_continuous (n + 1)).sub (cantorSeq_continuous n))
    summable_geometric_two
    (fun n x => by simpa [Real.norm_eq_abs] using cantorSeq_step_diff n x)

private lemma cantorF_mono : Monotone cantorF := fun x y hxy =>
  le_of_tendsto_of_tendsto (cantorSeq_tendsto_cantorF x) (cantorSeq_tendsto_cantorF y)
    (Eventually.of_forall fun n => cantorSeq_mono n hxy)

private lemma cantorF_zero : cantorF 0 = 0 :=
  tendsto_nhds_unique (cantorSeq_tendsto_cantorF 0)
    (by simpa only [cantorSeq_eq_zero_of_le _ le_rfl] using (tendsto_const_nhds (x := (0 : ℝ))))

private lemma cantorF_one : cantorF 1 = 1 :=
  tendsto_nhds_unique (cantorSeq_tendsto_cantorF 1)
    (by simpa only [cantorSeq_eq_one_of_ge _ le_rfl] using (tendsto_const_nhds (x := (1 : ℝ))))

private lemma cantorF_left {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 3)) :
    cantorF x = (1 / 2 : ℝ) * cantorF (3 * x) := by
  have h1 : Tendsto (fun n => cantorSeq (n + 1) x) atTop (nhds (cantorF x)) :=
    (cantorSeq_tendsto_cantorF x).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => (1 / 2 : ℝ) * cantorSeq n (3 * x)) atTop
      (nhds ((1 / 2 : ℝ) * cantorF (3 * x))) :=
    tendsto_const_nhds.mul (cantorSeq_tendsto_cantorF (3 * x))
  have heq : (fun n => cantorSeq (n + 1) x) = fun n => (1 / 2 : ℝ) * cantorSeq n (3 * x) := by
    funext n; simp only [cantorSeq, cantorStep, if_pos hx.2]
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

private lemma cantorF_mid {x : ℝ} (hx : x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3)) :
    cantorF x = (1 / 2 : ℝ) := by
  have h1 : Tendsto (fun n => cantorSeq (n + 1) x) atTop (nhds (cantorF x)) :=
    (cantorSeq_tendsto_cantorF x).comp (tendsto_add_atTop_nat 1)
  have heq : ∀ n : ℕ, cantorSeq (n + 1) x = 1 / 2 := by
    intro n
    simp only [cantorSeq, cantorStep]
    by_cases hle : x ≤ 1 / 3
    · rw [if_pos hle]
      have hx1 : 3 * x = 1 := by linarith [hx.1]
      rw [hx1, cantorSeq_eq_one_of_ge n le_rfl]; norm_num
    · rw [if_neg hle, if_pos hx.2]
  simp_rw [heq] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

private lemma cantorF_right {x : ℝ} (hx : x ∈ Set.Icc (2 / 3 : ℝ) 1) :
    cantorF x = (1 / 2 : ℝ) + (1 / 2 : ℝ) * cantorF (3 * x - 2) := by
  have h1 : Tendsto (fun n => cantorSeq (n + 1) x) atTop (nhds (cantorF x)) :=
    (cantorSeq_tendsto_cantorF x).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => (1 / 2 : ℝ) + (1 / 2 : ℝ) * cantorSeq n (3 * x - 2)) atTop
      (nhds ((1 / 2 : ℝ) + (1 / 2 : ℝ) * cantorF (3 * x - 2))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (cantorSeq_tendsto_cantorF (3 * x - 2)))
  have heq : ∀ n : ℕ, cantorSeq (n + 1) x = (1 / 2 : ℝ) + (1 / 2 : ℝ) * cantorSeq n (3 * x - 2) := by
    intro n
    simp only [cantorSeq, cantorStep, if_neg (by linarith [hx.1] : ¬ x ≤ 1 / 3)]
    by_cases hle : x ≤ 2 / 3
    · rw [if_pos hle]
      have hx0 : 3 * x - 2 = 0 := by linarith [hx.1]
      rw [hx0, cantorSeq_eq_zero_of_le n le_rfl]; norm_num
    · rw [if_neg hle]
  simp_rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

private lemma cantorF_pow_three (n : ℕ) :
    cantorF (1 / (3 : ℝ) ^ n) = 1 / (2 : ℝ) ^ n := by
  induction n with
  | zero => simpa using cantorF_one
  | succ n ih =>
    have hmem : (1 / (3 : ℝ) ^ (n + 1)) ∈ Set.Icc (0 : ℝ) (1 / 3) := by
      constructor
      · positivity
      · rw [pow_succ, one_div_le_one_div (by positivity) (by norm_num)]
        have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        linarith
    rw [cantorF_left hmem]
    have hmul : 3 * (1 / (3 : ℝ) ^ (n + 1)) = 1 / (3 : ℝ) ^ n := by
      rw [pow_succ]; field_simp
    rw [hmul, ih, pow_succ]; ring

private lemma cantorF_dyadic_plateau :
    ∀ (n : ℕ), 1 ≤ n → ∀ (k : ℕ), 1 ≤ k → k < 2 ^ n →
      ∃ u v : ℝ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
        cantorF u = (k : ℝ) / (2 : ℝ) ^ n ∧ cantorF v = (k : ℝ) / (2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _ k hk1 hkn
    by_cases hn0 : n = 0
    · subst hn0
      have hk_eq : k = 1 := by omega
      subst hk_eq
      refine ⟨1 / 3, 2 / 3, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
      · simpa using cantorF_mid (x := 1 / 3) (by constructor <;> norm_num)
      · simpa using cantorF_mid (x := 2 / 3) (by constructor <;> norm_num)
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      rcases lt_trichotomy k (2 ^ n) with hlt | heq | hgt
      · obtain ⟨u, v, hu0, huv, hv1, hFu, hFv⟩ := ih hn1 k hk1 hlt
        refine ⟨u / 3, v / 3, by linarith, by linarith, by linarith, ?_, ?_⟩
        · rw [cantorF_left ⟨by linarith, by linarith⟩,
            show 3 * (u / 3) = u by ring, hFu, pow_succ]; ring
        · rw [cantorF_left ⟨by linarith, by linarith⟩,
            show 3 * (v / 3) = v by ring, hFv, pow_succ]; ring
      · subst heq
        refine ⟨1 / 3, 2 / 3, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
        · rw [cantorF_mid (by constructor <;> norm_num), pow_succ]; push_cast; field_simp
        · rw [cantorF_mid (by constructor <;> norm_num), pow_succ]; push_cast; field_simp
      · have hk'1 : 1 ≤ k - 2 ^ n := by omega
        have hk'lt : k - 2 ^ n < 2 ^ n := by
          have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
          omega
        obtain ⟨u, v, hu0, huv, hv1, hFu, hFv⟩ := ih hn1 (k - 2 ^ n) hk'1 hk'lt
        have hcast : ((k - 2 ^ n : ℕ) : ℝ) = (k : ℝ) - (2 : ℝ) ^ n := by
          rw [Nat.cast_sub (le_of_lt hgt)]; push_cast; rfl
        refine ⟨(2 + u) / 3, (2 + v) / 3, by linarith, by linarith, by linarith, ?_, ?_⟩
        · rw [cantorF_right ⟨by linarith, by linarith⟩,
            show 3 * ((2 + u) / 3) - 2 = u by ring, hFu, hcast, pow_succ]; field_simp; ring
        · rw [cantorF_right ⟨by linarith, by linarith⟩,
            show 3 * ((2 + v) / 3) - 2 = v by ring, hFv, hcast, pow_succ]; field_simp; ring

private lemma boundedVariationOn_sub_linear
    {f : ℝ → ℝ} {s : Set ℝ} (hf : BoundedVariationOn f s) (a : ℝ) (hbd : Bornology.IsBounded s) :
    BoundedVariationOn (fun x => f x - a * x) s := by
  obtain ⟨M0, hM0⟩ := hbd.subset_closedBall (0 : ℝ)
  let M : ℝ := max M0 0
  have hM : s ⊆ Metric.closedBall (0 : ℝ) M :=
    hM0.trans (Metric.closedBall_subset_closedBall (le_max_left M0 0))
  have hMnn : 0 ≤ M := le_max_right M0 0
  have hlin_edist : ∀ x y : ℝ, edist (a * y) (a * x) = ENNReal.ofReal (|a| * |y - x|) := by
    intro x y
    rw [edist_dist, Real.dist_eq, ← mul_sub, abs_mul]
  have hlin_bv : eVariationOn (fun x => a * x) s ≤ ENNReal.ofReal (|a| * (2 * M)) := by
    rw [eVariationOn]
    refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
    calc ∑ i ∈ Finset.range n, edist (a * u (i + 1)) (a * u i)
        = ∑ i ∈ Finset.range n, ENNReal.ofReal (|a| * (u (i + 1) - u i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hlin_edist, abs_of_nonneg (sub_nonneg.mpr (hu (Nat.le_succ i)))]
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n, |a| * (u (i + 1) - u i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _; exact mul_nonneg (abs_nonneg a) (sub_nonneg.mpr (hu (Nat.le_succ i)))
      _ = ENNReal.ofReal (|a| * (u n - u 0)) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub u n]
      _ ≤ ENNReal.ofReal (|a| * (2 * M)) := by
          apply ENNReal.ofReal_le_ofReal
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
          have h0 := hM (hus 0)
          have hn := hM (hus n)
          simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h0 hn
          linarith [(abs_le.mp h0).1, (abs_le.mp hn).2]
  have hsub_le : eVariationOn (fun x => f x - a * x) s ≤
      eVariationOn f s + eVariationOn (fun x => a * x) s := by
    rw [eVariationOn]
    refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
    have htri : ∀ i : ℕ, edist (f (u (i + 1)) - a * u (i + 1)) (f (u i) - a * u i) ≤
        edist (f (u (i + 1))) (f (u i)) + edist (a * u (i + 1)) (a * u i) := by
      intro i
      rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
      apply ENNReal.ofReal_le_ofReal
      simp only [Real.dist_eq]
      have : (f (u (i + 1)) - a * u (i + 1)) - (f (u i) - a * u i) =
          (f (u (i + 1)) - f (u i)) - (a * u (i + 1) - a * u i) := by ring
      rw [this]
      exact abs_sub _ _
    calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) - a * u (i + 1)) (f (u i) - a * u i)
        ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) + edist (a * u (i + 1)) (a * u i)) :=
          Finset.sum_le_sum fun i _ => htri i
      _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          (∑ i ∈ Finset.range n, edist (a * u (i + 1)) (a * u i)) := Finset.sum_add_distrib
      _ ≤ eVariationOn f s + eVariationOn (fun x => a * x) s :=
          add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)
  exact ne_of_lt (lt_of_le_of_lt hsub_le (ENNReal.add_lt_top.mpr
    ⟨lt_top_iff_ne_top.mpr hf, lt_of_le_of_lt hlin_bv ENNReal.ofReal_lt_top⟩))

/-! ### Part (ii): Bounded alternating dyadic-jump series with infinite variation -/

private noncomputable def dyadTerm (n : ℕ) (x : ℝ) : ℝ :=
  if Int.floor ((2 : ℝ) ^ n * x) % 4 = 1 ∨ Int.floor ((2 : ℝ) ^ n * x) % 4 = 2
  then (1 : ℝ) / (2 : ℝ) ^ n else 0

private noncomputable def dyadTermLeft (n : ℕ) (x : ℝ) : ℝ :=
  if (Int.ceil ((2 : ℝ) ^ n * x) - 1) % 4 = 1 ∨ (Int.ceil ((2 : ℝ) ^ n * x) - 1) % 4 = 2
  then (1 : ℝ) / (2 : ℝ) ^ n else 0

private noncomputable def dyadF (x : ℝ) : ℝ :=
  ∑' m : ℕ, dyadTerm (m + 1) x

private noncomputable def dyadFLeft (x : ℝ) : ℝ :=
  ∑' m : ℕ, dyadTermLeft (m + 1) x

private lemma dyadTerm_nonneg (n : ℕ) (x : ℝ) : 0 ≤ dyadTerm n x := by
  unfold dyadTerm; split_ifs <;> positivity

private lemma dyadTerm_le (n : ℕ) (x : ℝ) : dyadTerm n x ≤ (1 / 2 : ℝ) ^ n := by
  unfold dyadTerm; split_ifs
  · rw [one_div_pow]
  · positivity

private lemma dyadTermLeft_nonneg (n : ℕ) (x : ℝ) : 0 ≤ dyadTermLeft n x := by
  unfold dyadTermLeft; split_ifs <;> positivity

private lemma dyadTermLeft_le (n : ℕ) (x : ℝ) : dyadTermLeft n x ≤ (1 / 2 : ℝ) ^ n := by
  unfold dyadTermLeft; split_ifs
  · rw [one_div_pow]
  · positivity

private lemma summable_half_succ : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) := by
  have : (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) = fun m => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m := by
    funext m; rw [pow_succ']
  rw [this]
  exact summable_geometric_two.mul_left _

private lemma tsum_half_succ : (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 1)) = 1 := by
  have : (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) = fun m => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m := by
    funext m; rw [pow_succ']
  rw [this, tsum_mul_left, tsum_geometric_two]
  norm_num

private lemma summable_dyadTerm (x : ℝ) : Summable (fun m : ℕ => dyadTerm (m + 1) x) :=
  Summable.of_nonneg_of_le (fun m => dyadTerm_nonneg (m + 1) x)
    (fun m => dyadTerm_le (m + 1) x) summable_half_succ

private lemma summable_dyadTermLeft (x : ℝ) : Summable (fun m : ℕ => dyadTermLeft (m + 1) x) :=
  Summable.of_nonneg_of_le (fun m => dyadTermLeft_nonneg (m + 1) x)
    (fun m => dyadTermLeft_le (m + 1) x) summable_half_succ

private lemma dyadF_abs_le_one (x : ℝ) : |dyadF x| ≤ 1 := by
  have h0 : 0 ≤ dyadF x := tsum_nonneg fun m => dyadTerm_nonneg (m + 1) x
  have h1 : dyadF x ≤ 1 := by
    calc dyadF x ≤ ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 1) :=
          (summable_dyadTerm x).tsum_le_tsum (fun m => dyadTerm_le (m + 1) x) summable_half_succ
      _ = 1 := tsum_half_succ
  rw [abs_of_nonneg h0]; exact h1

private lemma dyadTerm_ev_eq_right (n : ℕ) (x : ℝ) :
    ∀ᶠ y in nhdsWithin x (Set.Ici x), dyadTerm n y = dyadTerm n x := by
  let q : ℤ := Int.floor ((2 : ℝ) ^ n * x)
  have hq_le : (q : ℝ) ≤ (2 : ℝ) ^ n * x := Int.floor_le _
  have hq_lt : (2 : ℝ) ^ n * x < (q : ℝ) + 1 := Int.lt_floor_add_one _
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  let δ : ℝ := ((q : ℝ) + 1 - (2 : ℝ) ^ n * x) / (2 : ℝ) ^ n
  have hδ : 0 < δ := div_pos (by linarith) hpos
  have hmem : Set.Ico x (x + δ) ∈ nhdsWithin x (Set.Ici x) :=
    Ico_mem_nhdsGE (by linarith : x < x + δ)
  filter_upwards [hmem] with y hy
  have hy_ge : (q : ℝ) ≤ (2 : ℝ) ^ n * y := by nlinarith [hy.1]
  have hy_lt : (2 : ℝ) ^ n * y < (q : ℝ) + 1 := by
    have : (2 : ℝ) ^ n * y < (2 : ℝ) ^ n * (x + δ) := mul_lt_mul_of_pos_left hy.2 hpos
    have hmul : (2 : ℝ) ^ n * δ = (q : ℝ) + 1 - (2 : ℝ) ^ n * x := by
      dsimp [δ]; field_simp
    linarith
  have hfl : Int.floor ((2 : ℝ) ^ n * y) = q :=
    Int.floor_eq_iff.mpr ⟨hy_ge, hy_lt⟩
  simp only [dyadTerm, hfl]; rfl

private lemma dyadTerm_ev_eq_left (n : ℕ) (x : ℝ) :
    ∀ᶠ y in nhdsWithin x (Set.Iio x), dyadTerm n y = dyadTermLeft n x := by
  let m : ℤ := Int.ceil ((2 : ℝ) ^ n * x) - 1
  have hm_lt : (m : ℝ) < (2 : ℝ) ^ n * x := by
    push_cast [m]; linarith [Int.ceil_lt_add_one ((2 : ℝ) ^ n * x)]
  have hm_le : (2 : ℝ) ^ n * x ≤ (m : ℝ) + 1 := by
    push_cast [m]; linarith [Int.le_ceil ((2 : ℝ) ^ n * x)]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  let δ : ℝ := ((2 : ℝ) ^ n * x - (m : ℝ)) / (2 : ℝ) ^ n
  have hδ : 0 < δ := div_pos (by linarith) hpos
  have hmem : Set.Ioo (x - δ) x ∈ nhdsWithin x (Set.Iio x) :=
    Ioo_mem_nhdsLT (by linarith : x - δ < x)
  filter_upwards [hmem] with y hy
  have hy_ge : (m : ℝ) ≤ (2 : ℝ) ^ n * y := by
    have : (2 : ℝ) ^ n * (x - δ) < (2 : ℝ) ^ n * y := mul_lt_mul_of_pos_left hy.1 hpos
    have hmul : (2 : ℝ) ^ n * δ = (2 : ℝ) ^ n * x - (m : ℝ) := by
      dsimp [δ]; field_simp
    linarith
  have hy_lt : (2 : ℝ) ^ n * y < (m : ℝ) + 1 := by
    have : (2 : ℝ) ^ n * y < (2 : ℝ) ^ n * x := mul_lt_mul_of_pos_left hy.2 hpos
    linarith
  have hfl : Int.floor ((2 : ℝ) ^ n * y) = m :=
    Int.floor_eq_iff.mpr ⟨hy_ge, hy_lt⟩
  simp only [dyadTerm, dyadTermLeft, hfl]; rfl

private lemma tail_bound_half (N : ℕ) :
    (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + N + 1)) = (1 / 2 : ℝ) ^ N := by
  have : (fun m : ℕ => (1 / 2 : ℝ) ^ (m + N + 1)) =
      fun m => (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ (m + 1) := by
    funext m; rw [← pow_add]; congr 1; omega
  rw [this, tsum_mul_left, tsum_half_succ, mul_one]

private lemma dyadF_tail_bound (N : ℕ) (y : ℝ) :
    |dyadF y - ∑ m ∈ Finset.range N, dyadTerm (m + 1) y| ≤ (1 / 2 : ℝ) ^ N := by
  have hsplit := (summable_dyadTerm y).sum_add_tsum_nat_add N
  have hdiff : dyadF y - ∑ m ∈ Finset.range N, dyadTerm (m + 1) y =
      ∑' m : ℕ, dyadTerm (m + N + 1) y := by
    unfold dyadF; linarith
  rw [hdiff]
  have hnn : 0 ≤ ∑' m : ℕ, dyadTerm (m + N + 1) y := tsum_nonneg fun m => dyadTerm_nonneg _ y
  rw [abs_of_nonneg hnn]
  have hs1 : Summable (fun m : ℕ => dyadTerm (m + N + 1) y) :=
    (summable_dyadTerm y).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hs2 : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ (m + N + 1)) :=
    summable_half_succ.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  calc ∑' m : ℕ, dyadTerm (m + N + 1) y
      ≤ ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + N + 1) :=
        hs1.tsum_le_tsum (fun m => dyadTerm_le _ y) hs2
    _ = (1 / 2 : ℝ) ^ N := tail_bound_half N

private lemma dyadFLeft_tail_bound (N : ℕ) (x : ℝ) :
    |dyadFLeft x - ∑ m ∈ Finset.range N, dyadTermLeft (m + 1) x| ≤ (1 / 2 : ℝ) ^ N := by
  have hsplit := (summable_dyadTermLeft x).sum_add_tsum_nat_add N
  have hdiff : dyadFLeft x - ∑ m ∈ Finset.range N, dyadTermLeft (m + 1) x =
      ∑' m : ℕ, dyadTermLeft (m + N + 1) x := by
    unfold dyadFLeft; linarith
  rw [hdiff]
  have hnn : 0 ≤ ∑' m : ℕ, dyadTermLeft (m + N + 1) x := tsum_nonneg fun m => dyadTermLeft_nonneg _ x
  rw [abs_of_nonneg hnn]
  have hs1 : Summable (fun m : ℕ => dyadTermLeft (m + N + 1) x) :=
    (summable_dyadTermLeft x).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hs2 : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ (m + N + 1)) :=
    summable_half_succ.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  calc ∑' m : ℕ, dyadTermLeft (m + N + 1) x
      ≤ ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + N + 1) :=
        hs1.tsum_le_tsum (fun m => dyadTermLeft_le _ x) hs2
    _ = (1 / 2 : ℝ) ^ N := tail_bound_half N

private lemma eventually_all_range {α : Type*} {l : Filter α} {P : ℕ → α → Prop} (N : ℕ)
    (h : ∀ m < N, ∀ᶠ y in l, P m y) : ∀ᶠ y in l, ∀ m ∈ Finset.range N, P m y := by
  induction N with
  | zero => exact Eventually.of_forall fun _ _ hm => by simp at hm
  | succ N ih =>
    have h1 := ih (fun m hm => h m (Nat.lt_succ_of_lt hm))
    have h2 := h N (Nat.lt_succ_self N)
    filter_upwards [h1, h2] with y hy1 hy2 m hm
    rcases Finset.mem_range.mp hm with hm'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hlt | rfl
    · exact hy1 m (Finset.mem_range.mpr hlt)
    · exact hy2

private lemma dyadF_continuousRight (x : ℝ) :
    ContinuousWithinAt dyadF (Set.Ici x) x := by
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε / 3 := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    exact (ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).exists
  have hev : ∀ᶠ y in nhdsWithin x (Set.Ici x),
      ∀ m ∈ Finset.range N, dyadTerm (m + 1) y = dyadTerm (m + 1) x :=
    eventually_all_range N fun m _ => dyadTerm_ev_eq_right (m + 1) x
  filter_upwards [hev] with y hy
  have heq : ∑ m ∈ Finset.range N, dyadTerm (m + 1) y =
      ∑ m ∈ Finset.range N, dyadTerm (m + 1) x :=
    Finset.sum_congr rfl fun m hm => hy m hm
  rw [Real.dist_eq]
  have h1 := dyadF_tail_bound N y
  have h2 := dyadF_tail_bound N x
  have : dyadF y - dyadF x =
      (dyadF y - ∑ m ∈ Finset.range N, dyadTerm (m + 1) y) -
      (dyadF x - ∑ m ∈ Finset.range N, dyadTerm (m + 1) x) := by linarith
  rw [this]
  linarith [abs_sub (dyadF y - ∑ m ∈ Finset.range N, dyadTerm (m + 1) y)
    (dyadF x - ∑ m ∈ Finset.range N, dyadTerm (m + 1) x)]

private lemma dyadF_tendsto_left (x : ℝ) :
    Tendsto dyadF (nhdsWithin x (Set.Iio x)) (nhds (dyadFLeft x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε / 3 := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    exact (ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).exists
  have hev : ∀ᶠ y in nhdsWithin x (Set.Iio x),
      ∀ m ∈ Finset.range N, dyadTerm (m + 1) y = dyadTermLeft (m + 1) x :=
    eventually_all_range N fun m _ => dyadTerm_ev_eq_left (m + 1) x
  filter_upwards [hev] with y hy
  have heq : ∑ m ∈ Finset.range N, dyadTerm (m + 1) y =
      ∑ m ∈ Finset.range N, dyadTermLeft (m + 1) x :=
    Finset.sum_congr rfl fun m hm => hy m hm
  rw [Real.dist_eq]
  have h1 := dyadF_tail_bound N y
  have h2 := dyadFLeft_tail_bound N x
  have : dyadF y - dyadFLeft x =
      (dyadF y - ∑ m ∈ Finset.range N, dyadTerm (m + 1) y) -
      (dyadFLeft x - ∑ m ∈ Finset.range N, dyadTermLeft (m + 1) x) := by linarith
  rw [this]
  linarith [abs_sub (dyadF y - ∑ m ∈ Finset.range N, dyadTerm (m + 1) y)
    (dyadFLeft x - ∑ m ∈ Finset.range N, dyadTermLeft (m + 1) x)]

private lemma dyadTerm_jump_dyadic {n k : ℕ} (_hn : 0 < n) (hk : Odd k) (r : ℕ) :
    dyadTerm (r + 1) ((k : ℝ) / (2 : ℝ) ^ n) - dyadTermLeft (r + 1) ((k : ℝ) / (2 : ℝ) ^ n) =
      if r + 1 = n then
        (if k % 4 = 1 then (1 : ℝ) / (2 : ℝ) ^ n else -(1 : ℝ) / (2 : ℝ) ^ n)
      else 0 := by
  let x : ℝ := (k : ℝ) / (2 : ℝ) ^ n
  change dyadTerm (r + 1) x - dyadTermLeft (r + 1) x = _
  rcases lt_trichotomy (r + 1) n with hlt | heq | hgt
  · rw [if_neg (ne_of_lt hlt)]
    -- (2^(r+1)) * x = k / 2^(n - (r+1)) is not an integer since k is odd and n - (r+1) >= 1
    have hnotint : ∀ z : ℤ, (2 : ℝ) ^ (r + 1) * x ≠ (z : ℝ) := by
      intro z hz
      have hmul : (k : ℝ) = (z : ℝ) * (2 : ℝ) ^ (n - (r + 1)) := by
        have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (r + 1) * (2 : ℝ) ^ (n - (r + 1)) := by
          rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (r + 1) := by positivity
        dsimp [x] at hz
        rw [hpow] at hz
        have h1 : (k : ℝ) / (2 : ℝ) ^ (n - (r + 1)) = (z : ℝ) := by
          have : (2 : ℝ) ^ (r + 1) * ((k : ℝ) / ((2 : ℝ) ^ (r + 1) * (2 : ℝ) ^ (n - (r + 1)))) =
              (k : ℝ) / (2 : ℝ) ^ (n - (r + 1)) := by field_simp
          linarith
        have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (n - (r + 1)) := by positivity
        field_simp at h1; linarith
      have hcast : (k : ℤ) = z * (2 : ℤ) ^ (n - (r + 1)) := by exact_mod_cast hmul
      have hdvd : (2 : ℤ) ∣ (k : ℤ) := by
        have hge : 1 ≤ n - (r + 1) := by omega
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hge
        rw [hcast, hd, pow_succ]
        exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
      obtain ⟨m, rfl⟩ := hk
      omega
    have hfl_lt : (Int.floor ((2 : ℝ) ^ (r + 1) * x) : ℝ) < (2 : ℝ) ^ (r + 1) * x :=
      lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hnotint _))
    have hceil_eq : Int.ceil ((2 : ℝ) ^ (r + 1) * x) = Int.floor ((2 : ℝ) ^ (r + 1) * x) + 1 := by
      rw [Int.ceil_eq_iff]
      refine ⟨?_, le_of_lt (by push_cast; exact Int.lt_floor_add_one _)⟩
      push_cast; linarith
    simp only [dyadTerm, dyadTermLeft, hceil_eq, add_sub_cancel_right, sub_self]
  · rw [if_pos heq, heq]
    have hmul : (2 : ℝ) ^ n * x = ((k : ℤ) : ℝ) := by
      dsimp [x]; push_cast; field_simp
    have hfl : Int.floor ((2 : ℝ) ^ n * x) = (k : ℤ) := by
      rw [hmul, Int.floor_intCast]
    have hcl : Int.ceil ((2 : ℝ) ^ n * x) = (k : ℤ) := by
      rw [hmul, Int.ceil_intCast]
    simp only [dyadTerm, dyadTermLeft, hfl, hcl]
    obtain ⟨m, rfl⟩ := hk
    have hcases : (2 * m + 1) % 4 = 1 ∨ (2 * m + 1) % 4 = 3 := by omega
    rcases hcases with h1 | h3
    · rw [if_pos h1]
      have hz1 : ((2 * m + 1 : ℕ) : ℤ) % 4 = 1 := by omega
      have hz0 : (((2 * m + 1 : ℕ) : ℤ) - 1) % 4 = 0 := by omega
      rw [if_pos (Or.inl hz1), if_neg (by omega), sub_zero]
    · rw [if_neg (by omega : (2 * m + 1) % 4 ≠ 1)]
      have hz3 : ((2 * m + 1 : ℕ) : ℤ) % 4 = 3 := by omega
      have hz2 : (((2 * m + 1 : ℕ) : ℤ) - 1) % 4 = 2 := by omega
      rw [if_neg (by omega), if_pos (Or.inr hz2), zero_sub, neg_div]
  · rw [if_neg (ne_of_gt hgt)]
    have hmul : (2 : ℝ) ^ (r + 1) * x = (((2 ^ (r + 1 - n) * k : ℕ) : ℤ) : ℝ) := by
      have hpow : (2 : ℝ) ^ (r + 1) = (2 : ℝ) ^ n * (2 : ℝ) ^ (r + 1 - n) := by
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hgt)]
      dsimp [x]; rw [hpow]; push_cast; field_simp
    have hfl : Int.floor ((2 : ℝ) ^ (r + 1) * x) = ((2 ^ (r + 1 - n) * k : ℕ) : ℤ) := by
      rw [hmul, Int.floor_intCast]
    have hcl : Int.ceil ((2 : ℝ) ^ (r + 1) * x) = ((2 ^ (r + 1 - n) * k : ℕ) : ℤ) := by
      rw [hmul, Int.ceil_intCast]
    simp only [dyadTerm, dyadTermLeft, hfl, hcl]
    by_cases h1 : r + 1 - n = 1
    · rw [h1, pow_one]
      obtain ⟨m, rfl⟩ := hk
      have ha : ((2 * (2 * m + 1) : ℕ) : ℤ) % 4 = 2 := by omega
      have hb : (((2 * (2 * m + 1) : ℕ) : ℤ) - 1) % 4 = 1 := by omega
      rw [if_pos (Or.inr ha), if_pos (Or.inl hb), sub_self]
    · have hge2 : 2 ≤ r + 1 - n := by omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hge2
      have hmul4 : (4 : ℤ) ∣ ((2 ^ (r + 1 - n) * k : ℕ) : ℤ) := by
        rw [hd, pow_add]
        push_cast
        exact ⟨(2 : ℤ) ^ d * (k : ℤ), by ring⟩
      obtain ⟨q, hq⟩ := hmul4
      rw [hq, if_neg (by omega), if_neg (by omega), sub_self]

private lemma dyadF_jump_dyadic {n k : ℕ} (hn : 0 < n) (hk : Odd k) :
    dyadF ((k : ℝ) / (2 : ℝ) ^ n) - dyadFLeft ((k : ℝ) / (2 : ℝ) ^ n) =
      if k % 4 = 1 then (1 : ℝ) / (2 : ℝ) ^ n else -(1 : ℝ) / (2 : ℝ) ^ n := by
  unfold dyadF dyadFLeft
  rw [← (summable_dyadTerm ((k : ℝ) / (2 : ℝ) ^ n)).tsum_sub
    (summable_dyadTermLeft ((k : ℝ) / (2 : ℝ) ^ n))]
  simp_rw [dyadTerm_jump_dyadic hn hk]
  rw [tsum_eq_single (n - 1)]
  · rw [Nat.sub_add_cancel hn, if_pos rfl]
  · intro r hr
    have hne : r + 1 ≠ n := by omega
    rw [if_neg hne]

private lemma dyad_jump_abs_sum (N : ℕ) :
    (∑ j ∈ Finset.Ico (1 : ℕ) (2 ^ N),
      |dyadF ((j : ℝ) / (2 : ℝ) ^ N) - dyadFLeft ((j : ℝ) / (2 : ℝ) ^ N)|) = (N : ℝ) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico (1 : ℕ) (2 ^ (N + 1))) (fun j => Odd j)]
    have hodd_sum :
        (∑ j ∈ (Finset.Ico (1 : ℕ) (2 ^ (N + 1))).filter (fun j => Odd j),
          |dyadF ((j : ℝ) / (2 : ℝ) ^ (N + 1)) - dyadFLeft ((j : ℝ) / (2 : ℝ) ^ (N + 1))|) = 1 / 2 := by
      have hterm : ∀ j ∈ (Finset.Ico (1 : ℕ) (2 ^ (N + 1))).filter (fun j => Odd j),
          |dyadF ((j : ℝ) / (2 : ℝ) ^ (N + 1)) - dyadFLeft ((j : ℝ) / (2 : ℝ) ^ (N + 1))| =
            1 / (2 : ℝ) ^ (N + 1) := by
        intro j hj
        rw [dyadF_jump_dyadic (Nat.succ_pos N) (Finset.mem_filter.mp hj).2]
        split_ifs
        · rw [abs_of_pos (by positivity)]
        · rw [neg_div, abs_neg, abs_of_pos (by positivity)]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Ico (1 : ℕ) (2 ^ (N + 1))).filter (fun j => Odd j)).card = 2 ^ N := by
        refine (Finset.card_bij (fun m _ => 2 * m + 1) ?_ ?_ ?_).symm.trans (Finset.card_range (2 ^ N))
        · intro m hm
          rw [Finset.mem_range] at hm
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, by rw [pow_succ]; omega⟩, ⟨m, rfl⟩⟩
        · intro a _ b _ h; omega
        · intro j hj
          rw [Finset.mem_filter, Finset.mem_Ico] at hj
          obtain ⟨m, rfl⟩ := hj.2
          refine ⟨m, Finset.mem_range.mpr ?_, rfl⟩
          rw [pow_succ] at hj; omega
      rw [hcard, pow_succ]; push_cast; field_simp
    have heven_sum :
        (∑ j ∈ (Finset.Ico (1 : ℕ) (2 ^ (N + 1))).filter (fun j => ¬ Odd j),
          |dyadF ((j : ℝ) / (2 : ℝ) ^ (N + 1)) - dyadFLeft ((j : ℝ) / (2 : ℝ) ^ (N + 1))|) = (N : ℝ) / 2 := by
      rw [← ih]
      refine (Finset.sum_bij (fun m _ => 2 * m) ?_ ?_ ?_ ?_).symm
      · intro m hm
        rw [Finset.mem_Ico] at hm
        rw [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, by rw [pow_succ]; omega⟩, ?_⟩
        rintro ⟨k, hk⟩; omega
      · intro a _ b _ h; omega
      · intro j hj
        rw [Finset.mem_filter, Finset.mem_Ico] at hj
        have hev : Even j := Nat.not_odd_iff_even.mp hj.2
        obtain ⟨m, rfl⟩ := hev
        refine ⟨m, Finset.mem_Ico.mpr ⟨by omega, by rw [pow_succ] at hj; omega⟩, by omega⟩
      · intro m _
        have hfrac : (((2 * m : ℕ) : ℝ) / (2 : ℝ) ^ (N + 1)) = (m : ℝ) / (2 : ℝ) ^ N := by
          rw [pow_succ]; push_cast; field_simp
        rw [hfrac]
    rw [hodd_sum, heven_sum]; push_cast; ring

private lemma dyadF_not_locallyBoundedVariation :
    ¬ LocallyBoundedVariationOn dyadF (Set.Icc (0 : ℝ) 1) := by
  intro hloc
  have hbv : BoundedVariationOn dyadF (Set.Icc (0 : ℝ) 1) := by
    have h := hloc 0 1 (by simp) (by simp)
    simpa only [Set.inter_self] using h
  have hlt : eVariationOn dyadF (Set.Icc (0 : ℝ) 1) < ⊤ := lt_top_iff_ne_top.mpr hbv
  let M : ℝ := (eVariationOn dyadF (Set.Icc (0 : ℝ) 1)).toReal
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * M + 4)
  have hNpos : 1 ≤ N := by
    have hMnn : 0 ≤ M := ENNReal.toReal_nonneg
    have : (4 : ℝ) < N := by linarith
    exact_mod_cast (by linarith : (1 : ℝ) ≤ N)
  -- For each j ∈ Ico 1 (2^N), pick δ_j > 0 so |dyadF(j/2^N) - dyadF(y)| ≥ (1/2) * jump on (j/2^N - δ_j, j/2^N)
  have hex : ∀ j ∈ Finset.Ico (1 : ℕ) (2 ^ N), ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, (j : ℝ) / (2 : ℝ) ^ N - δ < y → y < (j : ℝ) / (2 : ℝ) ^ N →
        |dyadF ((j : ℝ) / (2 : ℝ) ^ N) - dyadFLeft ((j : ℝ) / (2 : ℝ) ^ N)| / 2 ≤
          |dyadF ((j : ℝ) / (2 : ℝ) ^ N) - dyadF y| := by
    intro j hj
    let x : ℝ := (j : ℝ) / (2 : ℝ) ^ N
    let J : ℝ := |dyadF x - dyadFLeft x|
    by_cases hJ : J = 0
    · refine ⟨1, one_pos, fun y _ _ => ?_⟩
      change J / 2 ≤ _
      rw [hJ, zero_div]; exact abs_nonneg _
    · have hJpos : 0 < J := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hJ)
      have ht := Metric.tendsto_nhds.mp (dyadF_tendsto_left x) (J / 2) (by linarith)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at ht
      obtain ⟨δ, hδ, hball⟩ := ht
      refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
      have hdist : dist y x < δ := by
        rw [Real.dist_eq, abs_of_neg (by linarith : y - x < 0)]; linarith
      have hy_close : |dyadF y - dyadFLeft x| < J / 2 := by
        simpa [Real.dist_eq] using hball hdist hy2
      have htri : J ≤ |dyadF x - dyadF y| + |dyadF y - dyadFLeft x| := by
        have : dyadF x - dyadFLeft x = (dyadF x - dyadF y) + (dyadF y - dyadFLeft x) := by ring
        simpa only [J, this] using abs_add_le (dyadF x - dyadF y) (dyadF y - dyadFLeft x)
      linarith
  -- Choose a single uniform δ < 1 / 2^(N + 1) smaller than all δ_j
  classical
  have hIco_ne : (Finset.Ico (1 : ℕ) (2 ^ N)).Nonempty :=
    ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, one_lt_pow₀ (by norm_num) (by omega)⟩⟩
  let δfun : ℕ → ℝ := fun j =>
    if hj : j ∈ Finset.Ico (1 : ℕ) (2 ^ N) then (hex j hj).choose else 1
  let δ : ℝ := min (1 / (2 : ℝ) ^ (N + 1))
    ((Finset.Ico (1 : ℕ) (2 ^ N)).inf' hIco_ne δfun) / 2
  have hδpos : 0 < δ := by
    apply div_pos _ (by norm_num)
    apply lt_min (by positivity)
    rw [Finset.lt_inf'_iff]
    intro j hj
    simp only [δfun, dif_pos hj]
    exact (hex j hj).choose_spec.1
  have hδ_lt_half : δ < 1 / (2 : ℝ) ^ (N + 1) := by
    have hmin : min (1 / (2 : ℝ) ^ (N + 1)) ((Finset.Ico (1 : ℕ) (2 ^ N)).inf' hIco_ne δfun) ≤
        1 / (2 : ℝ) ^ (N + 1) := min_le_left _ _
    have hpos : (0 : ℝ) < 1 / (2 : ℝ) ^ (N + 1) := by positivity
    dsimp only [δ]
    linarith
  have hδ_lt_j : ∀ j (hj : j ∈ Finset.Ico (1 : ℕ) (2 ^ N)), δ < (hex j hj).choose := by
    intro j hj
    have hle : min (1 / (2 : ℝ) ^ (N + 1))
        ((Finset.Ico (1 : ℕ) (2 ^ N)).inf' hIco_ne δfun) ≤ (hex j hj).choose :=
      calc min (1 / (2 : ℝ) ^ (N + 1)) ((Finset.Ico (1 : ℕ) (2 ^ N)).inf' hIco_ne δfun)
          ≤ (Finset.Ico (1 : ℕ) (2 ^ N)).inf' hIco_ne δfun := min_le_right _ _
        _ ≤ δfun j := Finset.inf'_le δfun hj
        _ = (hex j hj).choose := dif_pos hj
    have hpos := (hex j hj).choose_spec.1
    dsimp only [δ]
    linarith
  -- Define monotone sequence u : ℕ → ℝ interleaving (j+1)/2^N - δ and (j+1)/2^N for j < 2^N - 1
  let K : ℕ := 2 ^ N - 1
  let u : ℕ → ℝ := fun i =>
    if i < 2 * K then
      if i % 2 = 0 then ((i / 2 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N - δ
      else ((i / 2 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N
    else 1
  have hu_step : ∀ i : ℕ, u i ≤ u (i + 1) := by
    intro i
    dsimp [u]
    by_cases hi : i < 2 * K
    · rw [if_pos hi]
      by_cases hi1 : i + 1 < 2 * K
      · rw [if_pos hi1]
        by_cases hev : i % 2 = 0
        · rw [if_pos hev, if_neg (by omega : (i + 1) % 2 ≠ 0)]
          have hdiv : (i + 1) / 2 = i / 2 := by omega
          rw [hdiv]; linarith
        · rw [if_neg hev, if_pos (by omega : (i + 1) % 2 = 0)]
          have hdiv : (i + 1) / 2 = i / 2 + 1 := by omega
          rw [hdiv]
          have hgap : (1 : ℝ) / (2 : ℝ) ^ (N + 1) < (1 : ℝ) / (2 : ℝ) ^ N := by
            rw [pow_succ]
            have : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
            field_simp; linarith
          have hsub : (((i / 2 + 1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N) -
              (((i / 2 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N) = 1 / (2 : ℝ) ^ N := by
            push_cast; ring
          linarith
      · rw [if_neg hi1]
        have hdiv : i / 2 + 1 ≤ 2 ^ N := by
          have : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by norm_num)
          omega
        have hle1 : ((i / 2 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N ≤ 1 := by
          rw [div_le_one (by positivity)]; exact_mod_cast hdiv
        split_ifs <;> linarith
    · rw [if_neg hi, if_neg (by omega)]
  have hu_mono : Monotone u := monotone_nat_of_le_succ hu_step
  have hu_mem : ∀ i : ℕ, u i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    dsimp [u]
    split_ifs with hi hev
    · have hdiv_le : i / 2 + 1 ≤ 2 ^ N := by
        have : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by norm_num)
        omega
      have h1 : (1 : ℝ) / (2 : ℝ) ^ N ≤ ((i / 2 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
      have h2 : ((i / 2 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast hdiv_le
      have hgap : (1 : ℝ) / (2 : ℝ) ^ (N + 1) < (1 : ℝ) / (2 : ℝ) ^ N := by
        rw [pow_succ]
        have : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
        field_simp; linarith
      constructor <;> linarith
    · have hdiv_le : i / 2 + 1 ≤ 2 ^ N := by
        have : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by norm_num)
        omega
      constructor
      · positivity
      · rw [div_le_one (by positivity)]; exact_mod_cast hdiv_le
    · constructor <;> norm_num
  have hvar_ge : ENNReal.ofReal ((N : ℝ) / 4) ≤ eVariationOn dyadF (Set.Icc (0 : ℝ) 1) := by
    have hsum_le := eVariationOn.sum_le (f := dyadF) (n := 2 * K) hu_mono hu_mem
    have hreal_bound :
        (N : ℝ) / 4 ≤ ∑ j ∈ Finset.range K, |dyadF (u (2 * j + 1)) - dyadF (u (2 * j))| := by
      have hrewrite :
          (∑ j ∈ Finset.range K, |dyadF (u (2 * j + 1)) - dyadF (u (2 * j))|) ≥
            ∑ j ∈ Finset.Ico (1 : ℕ) (2 ^ N),
              |dyadF ((j : ℝ) / (2 : ℝ) ^ N) - dyadFLeft ((j : ℝ) / (2 : ℝ) ^ N)| / 2 := by
        have hKeq : K = 2 ^ N - 1 := rfl
        have hbij :
            (∑ j ∈ Finset.Ico (1 : ℕ) (2 ^ N),
              |dyadF ((j : ℝ) / (2 : ℝ) ^ N) - dyadFLeft ((j : ℝ) / (2 : ℝ) ^ N)| / 2) =
            ∑ m ∈ Finset.range K,
              |dyadF (((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N) - dyadFLeft (((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N)| / 2 := by
          refine (Finset.sum_bij (fun m _ => m + 1) ?_ ?_ ?_ ?_).symm
          · intro m hm
            rw [Finset.mem_range] at hm
            rw [Finset.mem_Ico]
            have : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by norm_num)
            omega
          · intro a _ b _ h; omega
          · intro j hj
            rw [Finset.mem_Ico] at hj
            refine ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
          · intro m _; rfl
        rw [hbij]
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_range] at hm
        have hm_ico : m + 1 ∈ Finset.Ico (1 : ℕ) (2 ^ N) := by
          rw [Finset.mem_Ico]
          have : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by norm_num)
          omega
        have hu0 : u (2 * m) = ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N - δ := by
          dsimp [u]
          rw [if_pos (by omega), if_pos (by omega), show 2 * m / 2 = m by omega]
        have hu1 : u (2 * m + 1) = ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N := by
          dsimp [u]
          rw [if_pos (by omega), if_neg (by omega), show (2 * m + 1) / 2 = m by omega]
        rw [hu0, hu1]
        exact (hex (m + 1) hm_ico).choose_spec.2 _ (by linarith [hδ_lt_j (m + 1) hm_ico]) (by linarith)
      have hhalf :
          (∑ j ∈ Finset.Ico (1 : ℕ) (2 ^ N),
            |dyadF ((j : ℝ) / (2 : ℝ) ^ N) - dyadFLeft ((j : ℝ) / (2 : ℝ) ^ N)| / 2) = (N : ℝ) / 4 := by
        rw [← Finset.sum_div, dyad_jump_abs_sum N]; ring
      linarith
    have hsub_sum :
        (∑ m ∈ Finset.range K, edist (dyadF (u (2 * m + 1))) (dyadF (u (2 * m)))) ≤
          ∑ i ∈ Finset.range (2 * K), edist (dyadF (u (i + 1))) (dyadF (u i)) := by
      have hmaps : Finset.image (fun m => 2 * m) (Finset.range K) ⊆ Finset.range (2 * K) := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨m, hm, rfl⟩
        rw [Finset.mem_range] at hm ⊢; omega
      calc ∑ m ∈ Finset.range K, edist (dyadF (u (2 * m + 1))) (dyadF (u (2 * m)))
          = ∑ i ∈ Finset.image (fun m => 2 * m) (Finset.range K), edist (dyadF (u (i + 1))) (dyadF (u i)) := by
            rw [Finset.sum_image (fun a _ b _ h => by omega)]
        _ ≤ ∑ i ∈ Finset.range (2 * K), edist (dyadF (u (i + 1))) (dyadF (u i)) :=
            Finset.sum_le_sum_of_subset hmaps
    calc ENNReal.ofReal ((N : ℝ) / 4)
        ≤ ENNReal.ofReal (∑ m ∈ Finset.range K, |dyadF (u (2 * m + 1)) - dyadF (u (2 * m))|) :=
          ENNReal.ofReal_le_ofReal hreal_bound
      _ = ∑ m ∈ Finset.range K, edist (dyadF (u (2 * m + 1))) (dyadF (u (2 * m))) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [edist_dist, Real.dist_eq]
      _ ≤ ∑ i ∈ Finset.range (2 * K), edist (dyadF (u (i + 1))) (dyadF (u i)) := hsub_sum
      _ ≤ eVariationOn dyadF (Set.Icc (0 : ℝ) 1) := hsum_le
  have hle_M : (N : ℝ) / 4 ≤ M := by
    have := ENNReal.toReal_mono hlt.ne hvar_ge
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  linarith

end Exercise25Helpers

theorem solution :
    (∃ (F : ℝ → ℝ),
      ContinuousOn F (Set.Icc (0 : ℝ) 1) ∧
      MonotoneOn F (Set.Icc (0 : ℝ) 1) ∧
      F 0 = 0 ∧ F 1 = 1 ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / 3),
        F x = (1 / 2 : ℝ) * F (3 * x)) ∧
      (∀ x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3),
        F x = (1 / 2 : ℝ)) ∧
      (∀ x ∈ Set.Icc (2 / 3 : ℝ) 1,
        F x = (1 / 2 : ℝ) + (1 / 2 : ℝ) * F (3 * x - 2)) ∧
      let inverse : ℝ → ℝ := fun x =>
        if x < 1 then sInf
          {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ x < F θ}
        else 1
      ∀ (a : ℝ),
        let g : ℝ → ℝ := fun x => inverse x - a * x
        (MonotoneOn g (Set.Icc (0 : ℝ) 1) ↔ a ≤ 0) ∧
        LocallyBoundedVariationOn g (Set.Icc (0 : ℝ) 1) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1,
          ContinuousWithinAt g (Set.Icc x 1) x) ∧
        (∀ x ∈ Set.Ioc (0 : ℝ) 1, ∃ l : ℝ,
          Tendsto g (nhdsWithin x (Set.Iio x)) (nhds l) ∧
          l ≤ g x) ∧
        closure {x : ℝ |
          x ∈ Set.Icc (0 : ℝ) 1 ∧
          ∃ l : ℝ,
            Tendsto g (nhdsWithin x (Set.Iio x)) (nhds l) ∧
            l < g x} = Set.Icc (0 : ℝ) 1) ∧
    (∃ f : ℝ → ℝ,
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        ContinuousWithinAt f (Set.Icc x 1) x) ∧
      (∀ x ∈ Set.Ioc (0 : ℝ) 1,
        ∃ l : ℝ,
          Tendsto f (nhdsWithin x (Set.Iio x)) (nhds l)) ∧
      ¬ LocallyBoundedVariationOn f (Set.Icc (0 : ℝ) 1) ∧
      (∀ (n k : ℕ), 0 < n → Odd k →
        (k : ℝ) / (2 : ℝ) ^ n ≤ 1 →
        ∃ l : ℝ,
          Tendsto f
            (nhdsWithin ((k : ℝ) / (2 : ℝ) ^ n)
              (Set.Iio ((k : ℝ) / (2 : ℝ) ^ n)))
            (nhds l) ∧
          f ((k : ℝ) / (2 : ℝ) ^ n) - l =
          (if k % 4 = 1 then (1 : ℝ) / (2 : ℝ) ^ n
            else -(1 : ℝ) / (2 : ℝ) ^ n))) := by
  constructor
  · -- Part (i): Cantor staircase F and generalized inverse
    refine ⟨Exercise25Helpers.cantorF,
      Exercise25Helpers.cantorF_continuous.continuousOn,
      Exercise25Helpers.cantorF_mono.monotoneOn _,
      Exercise25Helpers.cantorF_zero,
      Exercise25Helpers.cantorF_one,
      fun x hx => Exercise25Helpers.cantorF_left hx,
      fun x hx => Exercise25Helpers.cantorF_mid hx,
      fun x hx => Exercise25Helpers.cantorF_right hx, ?_⟩
    dsimp only
    let F := Exercise25Helpers.cantorF
    let S : ℝ → Set ℝ := fun x => {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ x < F θ}
    let inverse : ℝ → ℝ := fun x => if x < 1 then sInf (S x) else 1
    have hS_bdd : ∀ x : ℝ, BddBelow (S x) := fun x => ⟨0, fun θ hθ => hθ.1.1⟩
    have hS_ne : ∀ {x : ℝ}, x < 1 → (S x).Nonempty := fun {x} hx =>
      ⟨1, ⟨⟨by norm_num, le_rfl⟩, by simpa [F, Exercise25Helpers.cantorF_one] using hx⟩⟩
    have hinv_mem : ∀ x ∈ Set.Icc (0 : ℝ) 1, inverse x ∈ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      dsimp only [inverse]
      split_ifs with hx1
      · refine ⟨le_csInf (hS_ne hx1) (fun θ hθ => hθ.1.1),
          csInf_le (hS_bdd x) ⟨⟨by norm_num, le_rfl⟩, by simpa [F, Exercise25Helpers.cantorF_one] using hx1⟩⟩
      · exact ⟨by norm_num, le_rfl⟩
    have hinv_mono : MonotoneOn inverse (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      dsimp only [inverse]
      by_cases hy1 : y < 1
      · have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
        rw [if_pos hx1, if_pos hy1]
        exact csInf_le_csInf (hS_bdd x) (hS_ne hy1) fun θ hθ => ⟨hθ.1, lt_of_le_of_lt hxy hθ.2⟩
      · rw [if_neg hy1]
        split_ifs with hx1
        · exact csInf_le (hS_bdd x) ⟨⟨by norm_num, le_rfl⟩, by simpa [F, Exercise25Helpers.cantorF_one] using hx1⟩
        · exact le_rfl
    have hinv_zero : inverse 0 = 0 := by
      dsimp only [inverse]
      rw [if_pos (by norm_num : (0 : ℝ) < 1)]
      apply le_antisymm
      · apply le_of_forall_pos_le_add
        intro ε hε
        rw [zero_add]
        have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
        obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
        have hpow_mem : (1 / (3 : ℝ) ^ n) ∈ S 0 := by
          refine ⟨⟨by positivity, ?_⟩, ?_⟩
          · rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
          · change (0 : ℝ) < Exercise25Helpers.cantorF (1 / (3 : ℝ) ^ n)
            rw [Exercise25Helpers.cantorF_pow_three]; positivity
        calc sInf (S 0) ≤ 1 / (3 : ℝ) ^ n := csInf_le (hS_bdd 0) hpow_mem
          _ = (1 / 3 : ℝ) ^ n := by rw [one_div_pow]
          _ ≤ ε := le_of_lt hn
      · exact le_csInf (hS_ne (by norm_num)) (fun θ hθ => hθ.1.1)
    have hinv_rc' : ∀ x ∈ Set.Icc (0 : ℝ) 1, ContinuousWithinAt inverse (Set.Icc x 1) x := by
      intro x hx
      by_cases hx1 : x = 1
      · subst hx1; rw [Set.Icc_self]; exact continuousWithinAt_singleton
      · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
        rw [Metric.continuousWithinAt_iff]
        intro ε hε
        by_cases htop : 1 ≤ inverse x + ε / 2
        · refine ⟨1, one_pos, fun y hy _ => ?_⟩
          have hy_ge : inverse x ≤ inverse y := hinv_mono hx ⟨le_trans hx.1 hy.1, hy.2⟩ hy.1
          have hy_le : inverse y ≤ 1 := (hinv_mem y ⟨le_trans hx.1 hy.1, hy.2⟩).2
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy_ge)]
          linarith
        · push Not at htop
          set θ₁ : ℝ := inverse x + ε / 2 with hθ₁_def
          have hθ₁_gt : sInf (S x) < θ₁ := by
            have : inverse x = sInf (S x) := if_pos hxlt
            linarith
          obtain ⟨θ₀, hθ₀S, hθ₀_lt⟩ := (csInf_lt_iff (hS_bdd x) (hS_ne hxlt)).mp hθ₁_gt
          have hθ₁_mem : θ₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [(hinv_mem x hx).1], le_of_lt htop⟩
          have hFθ₁ : x < F θ₁ := lt_of_lt_of_le hθ₀S.2 (Exercise25Helpers.cantorF_mono (le_of_lt hθ₀_lt))
          have hFθ₁_le1 : F θ₁ ≤ 1 := by
            simpa [F, Exercise25Helpers.cantorF_one] using Exercise25Helpers.cantorF_mono hθ₁_mem.2
          refine ⟨F θ₁ - x, sub_pos.mpr hFθ₁, fun y hy hdist => ?_⟩
          have hy_ge : inverse x ≤ inverse y := hinv_mono hx ⟨le_trans hx.1 hy.1, hy.2⟩ hy.1
          have hy_lt : y < F θ₁ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)] at hdist
            linarith
          have hy_lt1 : y < 1 := lt_of_lt_of_le hy_lt hFθ₁_le1
          have hinv_y_le : inverse y ≤ θ₁ := by
            dsimp only [inverse]; rw [if_pos hy_lt1]
            exact csInf_le (hS_bdd y) ⟨hθ₁_mem, hy_lt⟩
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy_ge)]
          linarith
    have hinv_left : ∀ x ∈ Set.Ioc (0 : ℝ) 1, ∃ l : ℝ,
        Tendsto inverse (nhdsWithin x (Set.Iio x)) (nhds l) ∧ l ≤ inverse x := by
      intro x hx
      let l : ℝ := sSup (inverse '' Set.Ico 0 x)
      have hne : (inverse '' Set.Ico 0 x).Nonempty := ⟨inverse 0, 0, ⟨le_rfl, hx.1⟩, rfl⟩
      have hbdd : BddAbove (inverse '' Set.Ico 0 x) :=
        ⟨inverse x, by rintro _ ⟨y, hy, rfl⟩; exact hinv_mono ⟨hy.1, le_trans (le_of_lt hy.2) hx.2⟩ ⟨le_of_lt hx.1, hx.2⟩ (le_of_lt hy.2)⟩
      have hl_le : l ≤ inverse x := csSup_le hne fun _ ⟨y, hy, hyEq⟩ => by
        rw [← hyEq]
        exact hinv_mono ⟨hy.1, le_trans (le_of_lt hy.2) hx.2⟩ ⟨le_of_lt hx.1, hx.2⟩ (le_of_lt hy.2)
      refine ⟨l, ?_, hl_le⟩
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨_, ⟨y₀, hy₀, rfl⟩, hy₀_gt⟩ := (lt_csSup_iff hbdd hne).mp (by linarith : l - ε < l)
      have hmem : Set.Ioo y₀ x ∈ nhdsWithin x (Set.Iio x) := Ioo_mem_nhdsLT hy₀.2
      filter_upwards [hmem] with y hy
      have hy_ico : y ∈ Set.Ico 0 x := ⟨le_trans hy₀.1 (le_of_lt hy.1), hy.2⟩
      have h1 : inverse y₀ ≤ inverse y :=
        hinv_mono ⟨hy₀.1, le_trans (le_of_lt hy₀.2) hx.2⟩ ⟨hy_ico.1, le_trans (le_of_lt hy.2) hx.2⟩ (le_of_lt hy.1)
      have h2 : inverse y ≤ l := le_csSup hbdd ⟨y, hy_ico, rfl⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    intro a
    let g : ℝ → ℝ := fun x => inverse x - a * x
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- MonotoneOn g (Icc 0 1) ↔ a ≤ 0
      constructor
      · intro hmon
        by_contra hpos
        push Not at hpos
        have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num)
        obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < a / 2))).exists
        let x₀ : ℝ := 1 / (2 : ℝ) ^ (n + 1)
        have hx₀_mem : x₀ ∈ Set.Icc (0 : ℝ) 1 := by
          refine ⟨by positivity, ?_⟩
          rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
        have hx₀_lt1 : x₀ < 1 := by
          dsimp [x₀]; rw [div_lt_one (by positivity)]
          exact one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)
        have hpow_mem : (1 / (3 : ℝ) ^ n) ∈ S x₀ := by
          refine ⟨⟨by positivity, ?_⟩, ?_⟩
          · rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
          · change x₀ < Exercise25Helpers.cantorF (1 / (3 : ℝ) ^ n)
            rw [Exercise25Helpers.cantorF_pow_three]
            dsimp [x₀]; rw [pow_succ]
            have : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
            field_simp; linarith
        have hinv_le : inverse x₀ ≤ 1 / (3 : ℝ) ^ n := by
          dsimp only [inverse]; rw [if_pos hx₀_lt1]
          exact csInf_le (hS_bdd x₀) hpow_mem
        have hg_le : g 0 ≤ g x₀ := hmon ⟨le_rfl, by norm_num⟩ hx₀_mem hx₀_mem.1
        have hg0 : g 0 = 0 := by simp [g, hinv_zero]
        rw [hg0] at hg_le
        have hstep : a * x₀ ≤ 1 / (3 : ℝ) ^ n := by dsimp [g] at hg_le; linarith
        have hcontra : a / 2 ≤ (2 / 3 : ℝ) ^ n := by
          dsimp [x₀] at hstep
          rw [pow_succ] at hstep
          rw [div_pow]
          have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
          have h3pos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
          have h1 : a / 2 * (3 : ℝ) ^ n ≤ (2 : ℝ) ^ n := by
            have := mul_le_mul_of_nonneg_right hstep (mul_nonneg (le_of_lt h2pos) (le_of_lt h3pos))
            field_simp at this ⊢; linarith
          rw [le_div_iff₀ h3pos]; linarith
        linarith
      · intro ha x hx y hy hxy
        dsimp only [g]
        have h1 := hinv_mono hx hy hxy
        have h2 : a * y ≤ a * x := mul_le_mul_of_nonpos_left hxy ha
        linarith
    · -- LocallyBoundedVariationOn g (Icc 0 1)
      have hinv_bv : BoundedVariationOn inverse (Set.Icc (0 : ℝ) 1) :=
        hinv_mono.boundedVariationOn (C := 1) fun x hx => by
          rw [abs_of_nonneg (hinv_mem x hx).1]; exact (hinv_mem x hx).2
      exact (Exercise25Helpers.boundedVariationOn_sub_linear hinv_bv a (Metric.isBounded_Icc 0 1)).locallyBoundedVariationOn
    · -- Right continuity of g on [0, 1]
      intro x hx
      exact (hinv_rc' x hx).sub (continuous_const.mul continuous_id).continuousWithinAt
    · -- Left limits of g on (0, 1] with l ≤ g x
      intro x hx
      obtain ⟨l, hl, hle⟩ := hinv_left x hx
      refine ⟨l - a * x, hl.sub ((continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds), ?_⟩
      change l - a * x ≤ inverse x - a * x; linarith
    · -- Dense jump set of g in [0, 1]
      let J : Set ℝ := {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ l : ℝ, Tendsto g (nhdsWithin x (Set.Iio x)) (nhds l) ∧ l < g x}
      apply Set.Subset.antisymm
      · exact closure_minimal (fun x hx => hx.1) isClosed_Icc
      · intro z hz
        rw [Metric.mem_closure_iff]
        intro ε hε
        have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        obtain ⟨n0, hn0⟩ := (ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))).exists
        let n : ℕ := max 2 n0
        have hn1 : 1 ≤ n := by omega
        have hn_lt : (1 : ℝ) / (2 : ℝ) ^ n < ε / 2 := by
          calc (1 : ℝ) / (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by rw [one_div_pow]
            _ ≤ (1 / 2 : ℝ) ^ n0 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right 2 n0)
            _ < ε / 2 := hn0
        let raw : ℕ := Nat.floor ((2 : ℝ) ^ n * z)
        let k : ℕ := max 1 (min (2 ^ n - 1) raw)
        have h2ge2 : 2 ≤ 2 ^ n := by
          have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
          simpa using this
        have hk1 : 1 ≤ k := le_max_left _ _
        have hkn : k < 2 ^ n := by
          dsimp [k]; omega
        let x : ℝ := (k : ℝ) / (2 : ℝ) ^ n
        have hx_mem : x ∈ Set.Icc (0 : ℝ) 1 := by
          refine ⟨by positivity, ?_⟩
          rw [div_le_one (by positivity)]; exact_mod_cast le_of_lt hkn
        have hx_pos : 0 < x := by positivity
        have hx_lt1 : x < 1 := by
          dsimp [x]; rw [div_lt_one (by positivity)]; exact_mod_cast hkn
        -- Show x ∈ J using the Cantor plateau at x = k / 2^n
        have hxJ : x ∈ J := by
          obtain ⟨u, v, hu0, huv, hv1, hFu, hFv⟩ := Exercise25Helpers.cantorF_dyadic_plateau n hn1 k hk1 hkn
          obtain ⟨l, hl, _⟩ := hinv_left x ⟨hx_pos, hx_mem.2⟩
          have hl_le_u : l ≤ u := by
            have hev : ∀ᶠ y in nhdsWithin x (Set.Iio x), inverse y ≤ u := by
              have hmem : Set.Ioo 0 x ∈ nhdsWithin x (Set.Iio x) := Ioo_mem_nhdsLT hx_pos
              filter_upwards [hmem] with y hy
              have hy1 : y < 1 := lt_trans hy.2 hx_lt1
              dsimp only [inverse]; rw [if_pos hy1]
              exact csInf_le (hS_bdd y) ⟨⟨hu0, le_trans (le_of_lt huv) hv1⟩, by change y < Exercise25Helpers.cantorF u; rw [hFu]; exact hy.2⟩
            exact le_of_tendsto hl hev
          have hv_le_inv : v ≤ inverse x := by
            dsimp only [inverse]; rw [if_pos hx_lt1]
            refine le_csInf (hS_ne hx_lt1) fun θ hθ => ?_
            by_contra hlt
            push Not at hlt
            have hleF : F θ ≤ F v := Exercise25Helpers.cantorF_mono (le_of_lt hlt)
            change Exercise25Helpers.cantorF θ ≤ Exercise25Helpers.cantorF v at hleF
            rw [hFv] at hleF
            exact not_lt_of_ge hleF hθ.2
          refine ⟨hx_mem, l - a * x,
            hl.sub ((continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds), ?_⟩
          dsimp only [g]; linarith
        refine ⟨x, hxJ, ?_⟩
        -- Bound |z - x| < ε
        have hraw_le : (raw : ℝ) ≤ (2 : ℝ) ^ n * z := Nat.floor_le (mul_nonneg (by positivity) hz.1)
        have hraw_gt : (2 : ℝ) ^ n * z < (raw : ℝ) + 1 := Nat.lt_floor_add_one _
        have hraw_le_pow : raw ≤ 2 ^ n := by
          have : (2 : ℝ) ^ n * z ≤ (2 : ℝ) ^ n := by nlinarith [hz.2, show (0 : ℝ) < (2 : ℝ) ^ n by positivity]
          have : (raw : ℝ) ≤ (2 : ℝ) ^ n := le_trans hraw_le this
          exact_mod_cast this
        have hk_diff : |(k : ℝ) - (2 : ℝ) ^ n * z| ≤ 1 := by
          by_cases hraw0 : raw = 0
          · have hk_eq : k = 1 := by dsimp [k]; rw [hraw0]; omega
            rw [hk_eq]; push_cast
            rw [hraw0] at hraw_gt; push_cast at hraw_gt
            rw [abs_le]; constructor <;> nlinarith [hz.1, show (0 : ℝ) < (2 : ℝ) ^ n by positivity]
          · by_cases hraw_top : raw = 2 ^ n
            · have hk_eq : k = 2 ^ n - 1 := by dsimp [k]; rw [hraw_top]; omega
              have hcast_k : (k : ℝ) = (2 : ℝ) ^ n - 1 := by
                rw [hk_eq, Nat.cast_sub (by omega)]; push_cast; rfl
              have hpow_le_z : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ n * z := by
                have := hraw_le
                rw [hraw_top] at this
                push_cast at this
                exact this
              have hz1 : (2 : ℝ) ^ n * z ≤ (2 : ℝ) ^ n := by
                nlinarith [hz.2, show (0 : ℝ) < (2 : ℝ) ^ n by positivity]
              rw [hcast_k, abs_le]; constructor <;> linarith
            · have hk_eq : k = raw := by dsimp [k]; omega
              rw [hk_eq, abs_le]; constructor <;> linarith
        rw [Real.dist_eq, abs_sub_comm]
        have hdiv_eq : x - z = ((k : ℝ) - (2 : ℝ) ^ n * z) / (2 : ℝ) ^ n := by
          dsimp [x]; field_simp
        rw [hdiv_eq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
        have : |(k : ℝ) - (2 : ℝ) ^ n * z| / (2 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ n :=
          div_le_div_of_nonneg_right hk_diff (by positivity)
        linarith
  · -- Part (ii): Bounded alternating dyadic-jump series with infinite variation
    refine ⟨Exercise25Helpers.dyadF,
      fun x _ => Exercise25Helpers.dyadF_abs_le_one x,
      fun x _ => (Exercise25Helpers.dyadF_continuousRight x).mono (fun _ hy => hy.1),
      fun x _ => ⟨Exercise25Helpers.dyadFLeft x, Exercise25Helpers.dyadF_tendsto_left x⟩,
      Exercise25Helpers.dyadF_not_locallyBoundedVariation,
      fun n k hn hk _ => ⟨Exercise25Helpers.dyadFLeft ((k : ℝ) / (2 : ℝ) ^ n),
        Exercise25Helpers.dyadF_tendsto_left _,
        Exercise25Helpers.dyadF_jump_dyadic hn hk⟩⟩
