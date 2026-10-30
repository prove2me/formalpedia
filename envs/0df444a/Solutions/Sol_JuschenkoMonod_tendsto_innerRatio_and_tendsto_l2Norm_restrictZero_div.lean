-- Prove2me | solution 1 for JuschenkoMonod.tendsto_innerRatio_and_tendsto_l2Norm_restrictZero_div
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:03:47.210977+00:00
-- url     : https://prove2.me/submissions/1638abdb-8fce-4c0c-aa8a-a38947968488

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod
import Theorems.Thm_JuschenkoMonod_tendsto_innerRatio_of_tendsto_F
import Theorems.Thm_JuschenkoMonod_tendsto_F

namespace JuschenkoMonod

open MeasureTheory

instance : IsProbabilityMeasure (bernoulli ℤ) := by
  unfold bernoulli; infer_instance

lemma integral_unif (φ : Fin 2 → ℝ) :
    ∫ b, φ b ∂(PMF.uniformOfFintype (Fin 2)).toMeasure = (φ 0 + φ 1) / 2 := by
  rw [PMF.integral_eq_sum]
  rw [Fin.sum_univ_two]
  simp [PMF.uniformOfFintype_apply]
  ring

lemma integral_prod_coord (s : Finset ℤ) (φ : ℤ → Fin 2 → ℝ) :
    ∫ x, ∏ j ∈ s, φ j (x j) ∂bernoulli ℤ = ∏ j ∈ s, (φ j 0 + φ j 1) / 2 := by
  classical
  unfold bernoulli
  have := integral_restrict_infinitePi (μ := fun _ : ℤ => (PMF.uniformOfFintype (Fin 2)).toMeasure)
    (s := s) (f := fun y : (j : s) → Fin 2 => ∏ j : s, φ j (y j))
    (by exact (Measurable.aestronglyMeasurable (by fun_prop)))
  have h2 : (fun x : ℤ → Fin 2 => ∏ j ∈ s, φ j (x j)) =
      fun x => (fun y : (j : s) → Fin 2 => ∏ j : s, φ j (y j)) (s.restrict x) := by
    ext x; rw [← Finset.prod_coe_sort s (fun j => φ j (x j))]; rfl
  rw [h2, this]
  rw [MeasureTheory.integral_fintype_prod_eq_prod (fun j : s => fun b : Fin 2 => φ j b)]
  rw [← Finset.prod_coe_sort s (fun j => (φ j 0 + φ j 1) / 2)]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact integral_unif _



lemma tendsto_Icc_atTop :
    Filter.Tendsto (fun N : ℕ => Finset.Icc (-(N:ℤ)) N) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro a b hab
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · intro x
    refine ⟨x.natAbs, ?_⟩
    simp only [Finset.mem_Icc]
    omega

lemma summable_coord (w : ℤ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w) (x : ℤ → Fin 2) :
    Summable fun j : ℤ => ((x j : ℕ) : ℝ) * w j := by
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (Nat.cast_nonneg _) (hw0 j)) (fun j => ?_) hw
  have : ((x j : ℕ) : ℝ) ≤ 1 := by
    have : (x j : ℕ) ≤ 1 := by have := (x j).2; omega
    exact_mod_cast this
  nlinarith [hw0 j]

lemma pw_tendsto (w : ℤ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w) (x : ℤ → Fin 2) :
    Filter.Tendsto (fun N : ℕ => ∏ j ∈ Finset.Icc (-(N:ℤ)) N, Real.exp (-(((x j : ℕ) : ℝ) * w j)))
      Filter.atTop (nhds (Real.exp (-∑' j : ℤ, ((x j : ℕ) : ℝ) * w j))) := by
  have := ((summable_coord w hw0 hw x).hasSum.comp tendsto_Icc_atTop)
  have h2 := (Real.continuous_exp.tendsto _).comp (this.neg)
  refine h2.congr fun N => ?_
  simp only [Function.comp]
  rw [← Finset.sum_neg_distrib, Real.exp_sum]

lemma prod_coord_bound (w : ℤ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (N : ℕ) (x : ℤ → Fin 2) :
    |∏ j ∈ Finset.Icc (-(N:ℤ)) N, Real.exp (-(((x j : ℕ) : ℝ) * w j))| ≤ 1 := by
  rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)]
  apply Finset.prod_le_one (fun j _ => (Real.exp_pos _).le)
  intro j _
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg (Nat.cast_nonneg _) (hw0 j)

lemma measurable_prod_coord (w : ℤ → ℝ) (N : ℕ) :
    Measurable fun x : ℤ → Fin 2 =>
      ∏ j ∈ Finset.Icc (-(N:ℤ)) N, Real.exp (-(((x j : ℕ) : ℝ) * w j)) := by
  apply Finset.measurable_prod
  intro j _
  have : Measurable fun b : Fin 2 => Real.exp (-(((b : ℕ) : ℝ) * w j)) := measurable_of_finite _
  exact this.comp (measurable_pi_apply j)

lemma measurable_exp_tsum (w : ℤ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w) :
    Measurable fun x : ℤ → Fin 2 => Real.exp (-∑' j : ℤ, ((x j : ℕ) : ℝ) * w j) :=
  measurable_of_tendsto_metrizable (measurable_prod_coord w) (tendsto_pi_nhds.mpr (pw_tendsto w hw0 hw))

/-- Dominated-convergence form of the product integral. -/
lemma tendsto_integral_prod_coord (w : ℤ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w) :
    Filter.Tendsto (fun N : ℕ => ∏ j ∈ Finset.Icc (-(N:ℤ)) N, (1 + Real.exp (-w j)) / 2)
      Filter.atTop
      (nhds (∫ x, Real.exp (-∑' j : ℤ, ((x j : ℕ) : ℝ) * w j) ∂bernoulli ℤ)) := by
  have hint : ∀ N : ℕ, ∫ x, ∏ j ∈ Finset.Icc (-(N:ℤ)) N,
      Real.exp (-(((x j : ℕ) : ℝ) * w j)) ∂bernoulli ℤ =
      ∏ j ∈ Finset.Icc (-(N:ℤ)) N, (1 + Real.exp (-w j)) / 2 := by
    intro N
    rw [integral_prod_coord (Finset.Icc (-(N:ℤ)) N) (fun j b => Real.exp (-(((b : ℕ) : ℝ) * w j)))]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp
  simp_rw [← hint]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
  · exact fun N => (measurable_prod_coord w N).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact prod_coord_bound w hw0 N x
  · exact Filter.Eventually.of_forall fun x => pw_tendsto w hw0 hw x


lemma l2Norm_sq_eq {X : Type*} (F : (X → Fin 2) → ℝ) (hm : Measurable F) :
    l2Norm F ^ 2 = ∫ x, F x ^ 2 ∂bernoulli X := by
  unfold l2Norm
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := bernoulli X) (p := 2) (by norm_num)
  have h2 : eLpNorm F 2 (bernoulli X) ^ (2:ℕ) = ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂bernoulli X := by
    have : (((2:NNReal):ℝ)) = ((2:ℕ):ℝ) := by norm_num
    simp only [this, ENNReal.rpow_natCast] at h
    simp only [ENNReal.coe_ofNat] at h
    rw [h]
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [← ENNReal.toReal_pow, h2, integral_eq_lintegral_of_nonneg_ae]
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _
  · exact (hm.pow_const 2).aestronglyMeasurable


/-! ### The functions `f_n` -/

lemma summable_c (n : ℕ) (hn : 0 < n) :
    Summable fun j : ℤ => Real.exp (-(|j| : ℝ) / n) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set r := Real.exp (-1 / n) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr]
    calc Real.exp (-1 / n) < Real.exp 0 := Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by norm_num) hn')
      _ = 1 := Real.exp_zero
  have key : ∀ j : ℤ, Real.exp (-(|j| : ℝ) / n) = r ^ j.natAbs := by
    intro j
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    have : (|(j:ℝ)|) = (j.natAbs : ℝ) := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
    rw [this]; ring
  simp_rw [key]
  have hs : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0 hr1
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨?_, ?_⟩
  · simpa using hs
  · simpa using hs

lemma fn_eq (n : ℕ) (x : ℤ → Fin 2) :
    fn n x = Real.exp (-∑' j : ℤ, ((x j : ℕ) : ℝ) * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n))) := by
  unfold fn
  congr 1
  rw [neg_mul]
  congr 1
  rw [← tsum_mul_left]
  congr 1; ext j; ring

lemma fn_sq_eq (n : ℕ) (x : ℤ → Fin 2) :
    fn n x ^ 2 = Real.exp (-∑' j : ℤ, ((x j : ℕ) : ℝ) * (2 * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n)))) := by
  rw [fn_eq, ← Real.exp_nat_mul]
  congr 1
  have : (fun j : ℤ => ((x j : ℕ) : ℝ) * (2 * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n)))) =
      fun j => 2 * (((x j : ℕ) : ℝ) * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n))) := by
    ext j; ring
  rw [this, tsum_mul_left]
  push_cast
  ring


lemma a_eq (n : ℕ) (j : ℤ) : a n j = Real.exp (-((n:ℝ) * Real.exp (-(|j| : ℝ) / n))) := by
  unfold a; rw [neg_mul]

lemma measurable_fn (n : ℕ) (hn : 0 < n) : Measurable (fn n) := by
  have : fn n = fun x => Real.exp (-∑' j : ℤ, ((x j : ℕ) : ℝ) * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n))) :=
    funext (fn_eq n)
  rw [this]
  exact measurable_exp_tsum _ (fun j => by positivity) ((summable_c n hn).mul_left _)

lemma den_tendsto (n : ℕ) (hn : 0 < n) :
    Filter.Tendsto (fun N : ℕ => ∏ j ∈ Finset.Icc (-(N:ℤ)) N,
      (1 + Real.exp (-(2 * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n))))) / 2) Filter.atTop
      (nhds (l2Norm (fn n) ^ 2)) := by
  rw [l2Norm_sq_eq _ (measurable_fn n hn)]
  simp_rw [fn_sq_eq]
  exact tendsto_integral_prod_coord (fun j => 2 * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n)))
    (fun j => by positivity) (((summable_c n hn).mul_left _).mul_left _)

lemma l2Norm_sq_pos (n : ℕ) (hn : 0 < n) : 0 < l2Norm (fn n) ^ 2 := by
  rw [l2Norm_sq_eq _ (measurable_fn n hn)]
  have hpos : ∀ x, 0 < fn n x := fun x => by unfold fn; exact Real.exp_pos _
  have hle : ∀ x, fn n x ≤ 1 := by
    intro x
    rw [fn_eq, Real.exp_le_one_iff, neg_nonpos]
    exact tsum_nonneg fun j => by positivity
  have hint : Integrable (fun x => fn n x ^ 2) (bernoulli ℤ) := by
    refine Integrable.of_bound ((measurable_fn n hn).pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hpos x, hle x]
  rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
  have : Function.support (fun x => fn n x ^ 2) = Set.univ := by
    ext x; simp [(hpos x).ne']
  rw [this]; simp


lemma restrict_phi_prod (n : ℕ) (hn : 0 < n) (N : ℕ) (x : ℤ → Fin 2) :
    ∏ j ∈ Finset.Icc (-(N:ℤ)) N,
      ((if j = 0 ∧ x j ≠ 0 then (0:ℝ) else 1) *
        Real.exp (-(((x j : ℕ) : ℝ) * (2 * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n)))))) =
    (if x 0 = 0 then 1 else 0) *
      ∏ j ∈ Finset.Icc (-(N:ℤ)) N,
        Real.exp (-(((x j : ℕ) : ℝ) * (2 * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n))))) := by
  rw [Finset.prod_mul_distrib]
  congr 1
  have h0 : (0:ℤ) ∈ Finset.Icc (-(N:ℤ)) N := by simp
  rw [Finset.prod_eq_single_of_mem 0 h0]
  · by_cases hx : x 0 = 0 <;> simp [hx]
  · intro j _ hj
    simp [hj]

lemma l2Norm_restrictZero_sq (n : ℕ) (hn : 0 < n) :
    l2Norm (restrictZero 0 (fn n)) ^ 2 = l2Norm (fn n) ^ 2 / (1 + a n 0 ^ 2) := by
  set w : ℤ → ℝ := fun j => 2 * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n)) with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => by positivity
  have hws : Summable w := ((summable_c n hn).mul_left _).mul_left _
  have hmeas : Measurable (restrictZero 0 (fn n) : (ℤ → Fin 2) → ℝ) := by
    unfold restrictZero
    exact (measurable_fn n hn).indicator
      (measurableSet_eq_fun (measurable_pi_apply (0:ℤ)) measurable_const)
  rw [l2Norm_sq_eq _ hmeas]
  set φ : ℤ → Fin 2 → ℝ := fun j b =>
    (if j = 0 ∧ b ≠ 0 then (0:ℝ) else 1) * Real.exp (-(((b : ℕ) : ℝ) * w j)) with hφ
  have hint : ∀ N : ℕ, ∫ x, ∏ j ∈ Finset.Icc (-(N:ℤ)) N, φ j (x j) ∂bernoulli ℤ =
      (∏ j ∈ Finset.Icc (-(N:ℤ)) N, (1 + Real.exp (-w j)) / 2) / (1 + a n 0 ^ 2) := by
    intro N
    rw [integral_prod_coord]
    have h0 : (0:ℤ) ∈ Finset.Icc (-(N:ℤ)) N := by simp
    rw [← Finset.mul_prod_erase _ _ h0, ← Finset.mul_prod_erase _ (fun j => (1 + Real.exp (-w j)) / 2) h0]
    have e1 : (φ 0 0 + φ 0 1) / 2 = 1 / 2 := by simp [hφ]
    have e2 : a n 0 ^ 2 = Real.exp (-w 0) := by
      rw [a_eq, sq, ← Real.exp_add, hw]; simp only [Int.cast_zero, abs_zero, neg_zero, zero_div,
        Real.exp_zero, mul_one]; congr 1; ring
    have e3 : ∏ j ∈ (Finset.Icc (-(N:ℤ)) N).erase 0, (φ j 0 + φ j 1) / 2 =
        ∏ j ∈ (Finset.Icc (-(N:ℤ)) N).erase 0, (1 + Real.exp (-w j)) / 2 := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have : j ≠ 0 := Finset.ne_of_mem_erase hj
      simp [hφ, this]
    rw [e1, e3, e2]
    have : (0:ℝ) < 1 + Real.exp (-w 0) := by positivity
    field_simp
  have hlim : Filter.Tendsto (fun N : ℕ => ∫ x, ∏ j ∈ Finset.Icc (-(N:ℤ)) N, φ j (x j) ∂bernoulli ℤ)
      Filter.atTop (nhds (∫ x, (restrictZero 0 (fn n) x) ^ 2 ∂bernoulli ℤ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    · intro N
      apply Measurable.aestronglyMeasurable
      apply Finset.measurable_prod
      intro j _
      have : Measurable (φ j) := measurable_of_finite _
      exact this.comp (measurable_pi_apply j)
    · exact integrable_const _
    · intro N
      refine Filter.Eventually.of_forall fun x => ?_
      have := restrict_phi_prod n hn N x
      have hb := prod_coord_bound w hw0 N x
      simp only [hφ, hw] at this ⊢
      rw [this, Real.norm_eq_abs, abs_mul]
      have : |(if x 0 = 0 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      calc _ ≤ 1 * 1 := mul_le_mul this hb (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · refine Filter.Eventually.of_forall fun x => ?_
      have h := (pw_tendsto w hw0 hws x).const_mul (if x 0 = 0 then (1:ℝ) else 0)
      have e : ∀ N : ℕ, ∏ j ∈ Finset.Icc (-(N:ℤ)) N, φ j (x j) =
          (if x 0 = 0 then (1:ℝ) else 0) * ∏ j ∈ Finset.Icc (-(N:ℤ)) N,
            Real.exp (-(((x j : ℕ) : ℝ) * w j)) := fun N => restrict_phi_prod n hn N x
      simp_rw [e]
      have e2 : (restrictZero 0 (fn n) x) ^ 2 = (if x 0 = 0 then (1:ℝ) else 0) *
          Real.exp (-∑' j : ℤ, ((x j : ℕ) : ℝ) * w j) := by
        unfold restrictZero
        by_cases hx : x 0 = 0
        · simp only [Set.indicator, Set.mem_setOf_eq, hx, if_true, one_mul]
          exact fn_sq_eq n x
        · simp [Set.indicator, hx]
      rw [e2]; exact h
  simp_rw [hint] at hlim
  have h2 := (den_tendsto n hn).div_const (1 + a n 0 ^ 2)
  have := tendsto_nhds_unique hlim h2
  rw [this]


lemma ratio_sq (n : ℕ) (hn : 0 < n) :
    (l2Norm (restrictZero 0 (fn n)) / l2Norm (fn n)) ^ 2 = 1 / (1 + a n 0 ^ 2) := by
  rw [div_pow, l2Norm_restrictZero_sq n hn]
  have := (l2Norm_sq_pos n hn).ne'
  rw [div_div, mul_comm, ← div_div, div_self this]

lemma tendsto_restrict :
    Filter.Tendsto (fun n : ℕ => l2Norm (restrictZero 0 (fn n)) / l2Norm (fn n)) Filter.atTop (nhds 1) := by
  have ha : Filter.Tendsto (fun n : ℕ => a n 0) Filter.atTop (nhds 0) := by
    have : (fun n : ℕ => a n 0) = fun n : ℕ => Real.exp (-(n:ℝ)) := by
      ext n; simp [a]
    rw [this]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun n : ℕ => Real.sqrt (1 / (1 + a n 0 ^ 2))) Filter.atTop (nhds 1) := by
    have := ((tendsto_const_nhds (x := (1:ℝ))).div (tendsto_const_nhds.add (ha.pow 2))
      (by norm_num : (1:ℝ) + 0 ^ 2 ≠ 0))
    have h3 := (Real.continuous_sqrt.tendsto _).comp this
    have h4 : Filter.Tendsto (fun n : ℕ => Real.sqrt (1 / (1 + a n 0 ^ 2))) Filter.atTop
        (nhds (Real.sqrt (1 / (1 + (0:ℝ) ^ 2)))) := h3
    rw [show Real.sqrt (1 / (1 + (0:ℝ) ^ 2)) = 1 by norm_num] at h4
    exact h4
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [← ratio_sq n hn, Real.sqrt_sq]
  exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

end JuschenkoMonod

theorem solution : ∀ (g : Equiv.Perm ℤ) (_ : g ∈ IntervalExchange.wobbling ℤ),
    Filter.Tendsto (fun n => JuschenkoMonod.innerRatio g n) Filter.atTop (nhds 1) ∧
      Filter.Tendsto (fun n => JuschenkoMonod.l2Norm (JuschenkoMonod.restrictZero 0 (JuschenkoMonod.fn n)) /
        JuschenkoMonod.l2Norm (JuschenkoMonod.fn n)) Filter.atTop (nhds 1) :=
  fun g hg => ⟨JuschenkoMonod.tendsto_innerRatio_of_tendsto_F g hg (JuschenkoMonod.tendsto_F g hg),
    JuschenkoMonod.tendsto_restrict⟩
