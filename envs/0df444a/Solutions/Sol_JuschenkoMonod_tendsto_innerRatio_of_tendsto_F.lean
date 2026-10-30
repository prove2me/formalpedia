-- Prove2me | solution 1 for JuschenkoMonod.tendsto_innerRatio_of_tendsto_F
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:59:14.552223+00:00
-- url     : https://prove2.me/submissions/2549972a-aa49-4e96-bd4a-2a6567fdeaf7

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod
import Theorems.Thm_JuschenkoMonod_log_one_add_two_sided_bound
import Theorems.Thm_JuschenkoMonod_tsum_a_mul_exp_le_three_and_tsum_a_sq_mul_exp_le_inv
import Theorems.Thm_JuschenkoMonod_a_apply_div_a_expansion

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


lemma lip_exp_aux (s t : ℝ) (h : s ≤ t) : |Real.exp s - Real.exp t| ≤ |s - t| * Real.exp t := by
  have h1 := Real.add_one_le_exp (s - t)
  have h2 : Real.exp s = Real.exp t * Real.exp (s - t) := by rw [← Real.exp_add]; congr 1; ring
  have h3 : 0 ≤ Real.exp t - Real.exp s := by
    have := Real.exp_le_exp.mpr h; linarith
  rw [abs_sub_comm, abs_of_nonneg h3, abs_sub_comm s t, abs_of_nonneg (by linarith : 0 ≤ t - s)]
  rw [h2]
  have := Real.exp_pos t
  nlinarith

lemma lip_exp (s t : ℝ) : |Real.exp s - Real.exp t| ≤ |s - t| * Real.exp (max s t) := by
  rcases le_total s t with h | h
  · rw [max_eq_right h]; exact lip_exp_aux s t h
  · rw [max_eq_left h, abs_sub_comm, abs_sub_comm s t]; exact lip_exp_aux t s h

lemma abs_log_div_le (p r : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r) :
    |Real.log ((1 + p) / (1 + r))| ≤ |p - r| := by
  have h1 : (0:ℝ) < 1 + p := by linarith
  have h2 : (0:ℝ) < 1 + r := by linarith
  rw [abs_le]
  constructor
  · have := Real.log_le_sub_one_of_pos (div_pos h2 h1)
    rw [Real.log_div h2.ne' h1.ne'] at this
    rw [Real.log_div h1.ne' h2.ne']
    have h3 : (1 + r) / (1 + p) - 1 = (r - p) / (1 + p) := by field_simp; ring
    have h4 : (r - p) / (1 + p) ≤ |p - r| := by
      calc (r - p) / (1 + p) ≤ |r - p| / (1 + p) := by gcongr; exact le_abs_self _
        _ ≤ |r - p| / 1 := by gcongr; linarith
        _ = |p - r| := by rw [div_one, abs_sub_comm]
    linarith
  · have := Real.log_le_sub_one_of_pos (div_pos h1 h2)
    have h3 : (1 + p) / (1 + r) - 1 = (p - r) / (1 + r) := by field_simp; ring
    have h4 : (p - r) / (1 + r) ≤ |p - r| := by
      calc (p - r) / (1 + r) ≤ |p - r| / (1 + r) := by gcongr; exact le_abs_self _
        _ ≤ |p - r| / 1 := by gcongr; linarith
        _ = |p - r| := by rw [div_one]
    linarith


lemma a_eq (n : ℕ) (j : ℤ) : a n j = Real.exp (-((n:ℝ) * Real.exp (-(|j| : ℝ) / n))) := by
  unfold a; rw [neg_mul]

lemma num_eq (g : Equiv.Perm ℤ) (n : ℕ) (hn : 0 < n) (x : ℤ → Fin 2) :
    translate g (fn n) x * fn n x = Real.exp (-∑' i : ℤ, ((x i : ℕ) : ℝ) *
      ((n:ℝ) * Real.exp (-(|i| : ℝ) / n) + (n:ℝ) * Real.exp (-(|((g⁻¹ i : ℤ) : ℝ)| : ℝ) / n))) := by
  have hc := summable_c n hn
  have hw1 : Summable fun i : ℤ => (n:ℝ) * Real.exp (-(|i| : ℝ) / n) := hc.mul_left _
  have hw2 : Summable fun i : ℤ => (n:ℝ) * Real.exp (-(|((g⁻¹ i : ℤ) : ℝ)| : ℝ) / n) :=
    ((Equiv.summable_iff g⁻¹).mpr hc).mul_left _
  have h1 : translate g (fn n) x = Real.exp (-∑' j : ℤ, ((x (g j) : ℕ) : ℝ) *
      ((n:ℝ) * Real.exp (-(|j| : ℝ) / n))) := by
    unfold translate; rw [fn_eq]; rfl
  have h2 : ∑' j : ℤ, ((x (g j) : ℕ) : ℝ) * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n)) =
      ∑' i : ℤ, ((x i : ℕ) : ℝ) * ((n:ℝ) * Real.exp (-(|((g⁻¹ i : ℤ) : ℝ)| : ℝ) / n)) := by
    rw [← Equiv.tsum_eq g (fun i => ((x i : ℕ) : ℝ) * ((n:ℝ) * Real.exp (-(|((g⁻¹ i : ℤ) : ℝ)| : ℝ) / n)))]
    congr 1; ext j; simp
  have s1 := summable_coord _ (fun j => by positivity) hw1 x
  have s2 := summable_coord _ (fun j => by positivity) hw2 x
  rw [h1, fn_eq, ← Real.exp_add, h2, ← neg_add,
    add_comm (∑' i : ℤ, ((x i : ℕ) : ℝ) * ((n:ℝ) * Real.exp (-(|((g⁻¹ i : ℤ) : ℝ)| : ℝ) / n))),
    ← s1.tsum_add s2]
  congr 2
  exact tsum_congr fun i => by ring

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

lemma num_tendsto (g : Equiv.Perm ℤ) (n : ℕ) (hn : 0 < n) :
    Filter.Tendsto (fun N : ℕ => ∏ j ∈ Finset.Icc (-(N:ℤ)) N,
      (1 + Real.exp (-((n:ℝ) * Real.exp (-(|j| : ℝ) / n) +
        (n:ℝ) * Real.exp (-(|((g⁻¹ j : ℤ) : ℝ)| : ℝ) / n)))) / 2) Filter.atTop
      (nhds (∫ x, translate g (fn n) x * fn n x ∂bernoulli ℤ)) := by
  have hc := summable_c n hn
  have hw1 : Summable fun i : ℤ => (n:ℝ) * Real.exp (-(|i| : ℝ) / n) := hc.mul_left _
  have hw2 : Summable fun i : ℤ => (n:ℝ) * Real.exp (-(|((g⁻¹ i : ℤ) : ℝ)| : ℝ) / n) :=
    ((Equiv.summable_iff g⁻¹).mpr hc).mul_left _
  have := tendsto_integral_prod_coord
    (fun j => (n:ℝ) * Real.exp (-(|j| : ℝ) / n) + (n:ℝ) * Real.exp (-(|((g⁻¹ j : ℤ) : ℝ)| : ℝ) / n))
    (fun j => by positivity) (hw1.add hw2)
  have e : (∫ x, translate g (fn n) x * fn n x ∂bernoulli ℤ) =
      ∫ x, Real.exp (-∑' i : ℤ, ((x i : ℕ) : ℝ) *
      ((n:ℝ) * Real.exp (-(|i| : ℝ) / n) + (n:ℝ) * Real.exp (-(|((g⁻¹ i : ℤ) : ℝ)| : ℝ) / n))) ∂bernoulli ℤ :=
    integral_congr_ae (Filter.Eventually.of_forall (num_eq g n hn))
  rw [e]; exact this

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


lemma u_summable (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ) (n : ℕ) (hn : 0 < n) :
    Summable fun i : ℤ => Real.log ((1 + a n i * a n (g⁻¹ i)) / (1 + a n i ^ 2)) := by
  obtain ⟨k, hk⟩ := (inv_mem hg : g⁻¹ ∈ IntervalExchange.wobbling ℤ)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hk' : ∀ i : ℤ, |((g⁻¹ i : ℤ) : ℝ) - i| ≤ k := by
    intro i; have := hk i; rwa [Int.dist_eq] at this
  have hk0 : 0 ≤ k := (abs_nonneg _).trans (hk' 0)
  refine Summable.of_norm_bounded (((summable_c n hn).mul_left (k * Real.exp (k / n)))) fun i => ?_
  rw [Real.norm_eq_abs]
  set A := |((g⁻¹ i : ℤ) : ℝ)| with hA
  set I := |(i : ℝ)| with hI
  set c := Real.exp (-I / n) with hc
  set c' := Real.exp (-A / n) with hc'
  have hc0 : 0 < c := Real.exp_pos _
  have hc'0 : 0 < c' := Real.exp_pos _
  have hAI : |A - I| ≤ k := (abs_abs_sub_abs_le_abs_sub _ _).trans (hk' i)
  have hcc : |c' - c| ≤ (k / n) * (Real.exp (k / n) * c) := by
    refine (lip_exp _ _).trans ?_
    have h1 : |(-A / n) - (-I / n)| ≤ k / n := by
      have : (-A / n) - (-I / n) = -((A - I) / n) := by ring
      rw [this, abs_neg, abs_div, abs_of_pos hn']
      gcongr
    have h2 : Real.exp (max (-A / n) (-I / n)) ≤ Real.exp (k / n) * c := by
      rw [hc, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hAI' := abs_le.mp hAI
      refine max_le ?_ ?_
      · rw [← add_div]; apply div_le_div_of_nonneg_right _ hn'.le; linarith
      · rw [← add_div]; apply div_le_div_of_nonneg_right _ hn'.le; linarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  have ha_eq : a n i = Real.exp (-((n:ℝ) * c)) := a_eq n i
  have ha'_eq : a n (g⁻¹ i) = Real.exp (-((n:ℝ) * c')) := a_eq n (g⁻¹ i)
  have ha0 : 0 < a n i := by unfold a; exact Real.exp_pos _
  have ha1 : a n i ≤ 1 := by
    rw [ha_eq, Real.exp_le_one_iff, neg_nonpos]; positivity
  have haa : |a n (g⁻¹ i) - a n i| ≤ n * |c' - c| := by
    rw [ha_eq, ha'_eq]
    refine (lip_exp _ _).trans ?_
    have h1 : |(-((n:ℝ) * c')) - (-((n:ℝ) * c))| = n * |c' - c| := by
      have : (-((n:ℝ) * c')) - (-((n:ℝ) * c)) = -((n:ℝ) * (c' - c)) := by ring
      rw [this, abs_neg, abs_mul, abs_of_pos hn']
    have h2 : Real.exp (max (-((n:ℝ) * c')) (-((n:ℝ) * c))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact max_le (by nlinarith) (by nlinarith)
    rw [h1]
    nlinarith [abs_nonneg (c' - c), mul_nonneg hn'.le (abs_nonneg (c' - c)), Real.exp_pos (max (-((n:ℝ) * c')) (-((n:ℝ) * c)))]
  have hpr : |a n i * a n (g⁻¹ i) - a n i ^ 2| ≤ |a n (g⁻¹ i) - a n i| := by
    have : a n i * a n (g⁻¹ i) - a n i ^ 2 = a n i * (a n (g⁻¹ i) - a n i) := by ring
    rw [this, abs_mul, abs_of_pos ha0]
    nlinarith [abs_nonneg (a n (g⁻¹ i) - a n i)]
  have hlog := abs_log_div_le (a n i * a n (g⁻¹ i)) (a n i ^ 2)
    (mul_nonneg ha0.le (by unfold a; exact (Real.exp_pos _).le)) (sq_nonneg _)
  calc |Real.log ((1 + a n i * a n (g⁻¹ i)) / (1 + a n i ^ 2))|
      ≤ n * ((k / n) * (Real.exp (k / n) * c)) := by
        refine hlog.trans (hpr.trans (haa.trans ?_))
        gcongr
    _ = k * Real.exp (k / n) * c := by field_simp


lemma inner_eq_exp (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ) (n : ℕ) (hn : 0 < n) :
    ∃ L : ℝ, HasSum (fun i : ℤ => Real.log ((1 + a n i * a n (g⁻¹ i)) / (1 + a n i ^ 2))) L ∧
      innerRatio g n = Real.exp L := by
  have hu := u_summable g hg n hn
  refine ⟨_, hu.hasSum, ?_⟩
  have hlim1 := (num_tendsto g n hn).div (den_tendsto n hn) (l2Norm_sq_pos n hn).ne'
  have hlim2 := (Real.continuous_exp.tendsto _).comp (hu.hasSum.comp tendsto_Icc_atTop)
  have heq : ∀ N : ℕ, (∏ j ∈ Finset.Icc (-(N:ℤ)) N,
      (1 + Real.exp (-((n:ℝ) * Real.exp (-(|j| : ℝ) / n) +
        (n:ℝ) * Real.exp (-(|((g⁻¹ j : ℤ) : ℝ)| : ℝ) / n)))) / 2) /
      (∏ j ∈ Finset.Icc (-(N:ℤ)) N, (1 + Real.exp (-(2 * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n))))) / 2)
      = (Real.exp ∘ (fun s : Finset ℤ => ∑ b ∈ s, Real.log ((1 + a n b * a n (g⁻¹ b)) / (1 + a n b ^ 2))) ∘
          fun N : ℕ => Finset.Icc (-(N:ℤ)) N) N := by
    intro N
    simp only [Function.comp]
    rw [Real.exp_sum, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hX : Real.exp (-((n:ℝ) * Real.exp (-(|j| : ℝ) / n) +
        (n:ℝ) * Real.exp (-(|((g⁻¹ j : ℤ) : ℝ)| : ℝ) / n))) = a n j * a n (g⁻¹ j) := by
      rw [a_eq, a_eq, ← Real.exp_add]; congr 1; ring
    have hY : Real.exp (-(2 * ((n:ℝ) * Real.exp (-(|j| : ℝ) / n)))) = a n j ^ 2 := by
      rw [a_eq, sq, ← Real.exp_add]; congr 1; ring
    rw [hX, hY]
    have hp : 0 < a n j * a n (g⁻¹ j) := by
      apply mul_pos <;> (unfold a; exact Real.exp_pos _)
    have hq : 0 < 1 + a n j ^ 2 := by positivity
    rw [Real.exp_log (div_pos (by linarith) hq)]
    field_simp
  have hlim3 := hlim1.congr heq
  have := tendsto_nhds_unique hlim3 hlim2
  unfold innerRatio
  exact this


lemma integral_inner_symm (g : Equiv.Perm ℤ) (n : ℕ) :
    ∫ x, translate g (fn n) x * fn n x ∂bernoulli ℤ =
      ∫ x, translate g⁻¹ (fn n) x * fn n x ∂bernoulli ℤ := by
  let T : (ℤ → Fin 2) ≃ᵐ (ℤ → Fin 2) := MeasurableEquiv.piCongrLeft (fun _ : ℤ => Fin 2) g⁻¹
  have hT : MeasurePreserving T (bernoulli ℤ) (bernoulli ℤ) := by
    refine ⟨T.measurable, ?_⟩
    unfold bernoulli
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : ℤ => (PMF.uniformOfFintype (Fin 2)).toMeasure)
      (X := fun _ : ℤ => Fin 2) g⁻¹
  have hTx : ∀ x j, T x j = x (g j) := by
    intro x j
    have : j = g⁻¹ (g j) := by simp
    show Equiv.piCongrLeft (fun _ : ℤ => Fin 2) g⁻¹ x j = x (g j)
    conv_lhs => rw [this]
    rw [Equiv.piCongrLeft_apply_apply]
  rw [← hT.integral_comp' (fun x => translate g⁻¹ (fn n) x * fn n x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [translate]
  have h1 : (fun j => T x (g⁻¹ • j)) = x := by
    funext j; rw [hTx]; simp
  have h2 : T x = fun j => x (g j) := funext (hTx x)
  rw [h1, h2]
  show fn n (fun j => x (g • j)) * fn n x = _
  rw [mul_comm]
  rfl


lemma core_inner (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ) (n : ℕ) (hn : 0 < n) :
    ∃ L : ℝ, HasSum (fun j : ℤ => Real.log ((1 + a n j * a n (g j)) / (1 + a n j ^ 2))) L ∧
      innerRatio g n = Real.exp L := by
  obtain ⟨L, hL, he⟩ := inner_eq_exp g⁻¹ (inv_mem hg) n hn
  refine ⟨L, by simpa using hL, ?_⟩
  rw [← he]
  unfold innerRatio
  rw [integral_inner_symm]


lemma a_pos' (n : ℕ) (j : ℤ) : 0 < a n j := Real.exp_pos _

lemma a_le_one' (n : ℕ) (j : ℤ) : a n j ≤ 1 := by
  unfold a
  rw [Real.exp_le_one_iff]
  have : 0 ≤ (n : ℝ) * Real.exp (-(|j| : ℝ) / n) := by positivity
  linarith

lemma exp_two_mul_eq_sq (n : ℕ) (j : ℤ) :
    Real.exp (-2 * (|j| : ℝ) / n) = Real.exp (-(|j| : ℝ) / n) ^ 2 := by
  rw [sq, ← Real.exp_add]; ring_nf

/-- The per-term estimate, stated for plain real numbers. -/
lemma term_bound (Cl a0 a1 e d η ϑ q C' C'' : ℝ) (ha0 : 0 < a0) (ha0' : a0 ≤ 1) (ha1 : 0 < a1)
    (he : 0 ≤ e)
    (hlog : ∀ z : ℝ, -1 / 2 ≤ z → z - Cl * z ^ 2 ≤ Real.log (1 + z) ∧ Real.log (1 + z) ≤ z)
    (hexp : a1 / a0 - 1 = e * d + η * e + ϑ) (hη : |η| ≤ q) (hϑ : |ϑ| ≤ C' * e ^ 2)
    (hr : |a1 / a0 - 1| ≤ C'' * e) (hCl : 0 < Cl) :
    |Real.log ((1 + a0 * a1) / (1 + a0 ^ 2)) - a0 ^ 2 / (1 + a0 ^ 2) * e * d| ≤
      (Cl * C'' ^ 2 + |C'|) * (a0 ^ 2 * e ^ 2) + q * (a0 * e) := by
  set w := a0 ^ 2 / (1 + a0 ^ 2) with hw
  set r := a1 / a0 - 1 with hrdef
  have hpos : 0 < 1 + a0 ^ 2 := by positivity
  have hw0 : 0 ≤ w := by positivity
  have hwa2 : w ≤ a0 ^ 2 := div_le_self (by positivity) (by nlinarith)
  have hwhalf : w ≤ 1 / 2 := by
    rw [hw, div_le_iff₀ hpos]; nlinarith
  have hwa : w ≤ a0 := le_trans hwa2 (by nlinarith)
  have hr1 : -1 ≤ r := by
    have : 0 < a1 / a0 := div_pos ha1 ha0
    linarith
  have hfac : (1 + a0 * a1) / (1 + a0 ^ 2) = 1 + w * r := by
    rw [hw, hrdef]; field_simp; ring
  set z := w * r with hz
  have hz2 : -1 / 2 ≤ z := by
    have : -w ≤ w * r := by nlinarith
    linarith
  obtain ⟨hl1, hl2⟩ := hlog z hz2
  rw [hfac]
  have hz_sq : z ^ 2 ≤ C'' ^ 2 * (a0 ^ 2 * e ^ 2) := by
    have h1 : z ^ 2 = w ^ 2 * |r| ^ 2 := by rw [hz, mul_pow, sq_abs]
    have hCe : 0 ≤ C'' * e := le_trans (abs_nonneg _) hr
    have h2 : |r| ^ 2 ≤ (C'' * e) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hr 2
    have h3 : w ^ 2 ≤ a0 ^ 2 := by nlinarith
    rw [h1]
    calc w ^ 2 * |r| ^ 2 ≤ a0 ^ 2 * (C'' * e) ^ 2 :=
          mul_le_mul h3 h2 (sq_nonneg _) (sq_nonneg _)
      _ = C'' ^ 2 * (a0 ^ 2 * e ^ 2) := by ring
  have hzexp : z - w * e * d = w * η * e + w * ϑ := by
    rw [hz, show r = e * d + η * e + ϑ from hexp]; ring
  have hA : |Real.log (1 + z) - z| ≤ Cl * C'' ^ 2 * (a0 ^ 2 * e ^ 2) := by
    rw [abs_le]
    have : Cl * z ^ 2 ≤ Cl * (C'' ^ 2 * (a0 ^ 2 * e ^ 2)) := mul_le_mul_of_nonneg_left hz_sq hCl.le
    have hz0 : 0 ≤ Cl * z ^ 2 := by positivity
    constructor <;> nlinarith
  have hB : |w * η * e| ≤ q * (a0 * e) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg he]
    have hq : 0 ≤ q := le_trans (abs_nonneg _) hη
    calc w * |η| * e ≤ a0 * q * e := by gcongr
      _ = q * (a0 * e) := by ring
  have hC : |w * ϑ| ≤ |C'| * (a0 ^ 2 * e ^ 2) := by
    rw [abs_mul, abs_of_nonneg hw0]
    have : |ϑ| ≤ |C'| * e ^ 2 := le_trans hϑ (by gcongr; exact le_abs_self _)
    calc w * |ϑ| ≤ a0 ^ 2 * (|C'| * e ^ 2) := mul_le_mul hwa2 this (abs_nonneg _) (sq_nonneg _)
      _ = |C'| * (a0 ^ 2 * e ^ 2) := by ring
  have : Real.log (1 + z) - w * e * d = (Real.log (1 + z) - z) + (w * η * e + w * ϑ) := by
    rw [← hzexp]; ring
  rw [this]
  calc |(Real.log (1 + z) - z) + (w * η * e + w * ϑ)|
      ≤ |Real.log (1 + z) - z| + (|w * η * e| + |w * ϑ|) :=
        le_trans (abs_add_le _ _) (by gcongr; exact abs_add_le _ _)
    _ ≤ Cl * C'' ^ 2 * (a0 ^ 2 * e ^ 2) + (q * (a0 * e) + |C'| * (a0 ^ 2 * e ^ 2)) := by
        gcongr
    _ = (Cl * C'' ^ 2 + |C'|) * (a0 ^ 2 * e ^ 2) + q * (a0 * e) := by ring

lemma abs_sub_le_wobblingNorm (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ) (j : ℤ) :
    |((|g j| : ℝ) - |j|)| ≤ wobblingNorm g := by
  obtain ⟨C0, hC0⟩ := hg
  have hbdd : BddAbove (Set.range fun j : ℤ => (|g j - j| : ℝ)) := by
    refine ⟨C0, ?_⟩
    rintro _ ⟨k, rfl⟩
    have := hC0 k
    rw [Int.dist_eq] at this
    simpa using this
  have h1 : (|g j - j| : ℝ) ≤ wobblingNorm g := le_ciSup hbdd j
  refine le_trans ?_ h1
  push_cast
  exact abs_abs_sub_abs_le_abs_sub _ _

/-- The key estimate: `|L_n - F_n(g)| ≤ K / n`. -/
lemma log_sum_close (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ) :
    ∃ K : ℝ, ∀ n : ℕ, 0 < n → ∃ L : ℝ, innerRatio g n = Real.exp L ∧ |L - F n g| ≤ K / n := by
  obtain ⟨hCl, hlog⟩ := log_one_add_two_sided_bound
  obtain ⟨C, C', C'', hexp⟩ := a_apply_div_a_expansion (wobblingNorm g)
  refine ⟨(4 * Real.log 2 - 2) * C'' ^ 2 + |C'| + 3 * |C|, fun n hn => ?_⟩
  obtain ⟨L, hL, hLe⟩ := core_inner g hg n hn
  refine ⟨L, hLe, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hs1, hs1le, hs2, hs2le⟩ := tsum_a_mul_exp_le_three_and_tsum_a_sq_mul_exp_le_inv n hn
  have hs2' : Summable fun j : ℤ => a n j ^ 2 * Real.exp (-(|j| : ℝ) / n) ^ 2 := by
    simp_rw [exp_two_mul_eq_sq] at hs2; exact hs2
  have hs2le' : ∑' j : ℤ, a n j ^ 2 * Real.exp (-(|j| : ℝ) / n) ^ 2 ≤ 1 / n := by
    simp_rw [exp_two_mul_eq_sq] at hs2le; exact hs2le
  -- summability of the `F` terms
  set fF : ℤ → ℝ := fun j => a n j ^ 2 / (1 + a n j ^ 2) * Real.exp (-(|j| : ℝ) / n) *
    ((|g j| : ℝ) - |j|) with hfF
  have hFs : Summable fF := by
    refine Summable.of_norm_bounded (hs1.mul_left (wobblingNorm g)) fun j => ?_
    have ha := a_pos' n j
    have ha1 := a_le_one' n j
    have hw0 : 0 ≤ a n j ^ 2 / (1 + a n j ^ 2) := by positivity
    have hwa : a n j ^ 2 / (1 + a n j ^ 2) ≤ a n j :=
      le_trans (div_le_self (by positivity) (by nlinarith)) (by nlinarith)
    rw [Real.norm_eq_abs, hfF]
    simp only
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (Real.exp_pos _).le]
    have := abs_sub_le_wobblingNorm g hg j
    have he := (Real.exp_pos (-(|j| : ℝ) / n)).le
    calc a n j ^ 2 / (1 + a n j ^ 2) * Real.exp (-(|j| : ℝ) / n) * abs ((|g j| : ℝ) - |j|)
        ≤ a n j * Real.exp (-(|j| : ℝ) / n) * wobblingNorm g := by gcongr
      _ = wobblingNorm g * (a n j * Real.exp (-(|j| : ℝ) / n)) := by ring
  have hFsum : HasSum fF (F n g) := hFs.hasSum
  have hdiff := hL.sub hFsum
  -- the majorant
  set M : ℤ → ℝ := fun j => ((4 * Real.log 2 - 2) * C'' ^ 2 + |C'|) *
      (a n j ^ 2 * Real.exp (-(|j| : ℝ) / n) ^ 2) +
      |C| / n * (a n j * Real.exp (-(|j| : ℝ) / n)) with hM
  have hMs : Summable M := (hs2'.mul_left _).add (hs1.mul_left _)
  have hMsum : ∑' j, M j ≤ ((4 * Real.log 2 - 2) * C'' ^ 2 + |C'| + 3 * |C|) / n := by
    rw [hM, (hs2'.mul_left _).tsum_add (hs1.mul_left _), tsum_mul_left, tsum_mul_left]
    have hK0 : 0 ≤ (4 * Real.log 2 - 2) * C'' ^ 2 + |C'| := by positivity
    have hC0 : 0 ≤ |C| / n := by positivity
    calc ((4 * Real.log 2 - 2) * C'' ^ 2 + |C'|) *
          (∑' j : ℤ, a n j ^ 2 * Real.exp (-(|j| : ℝ) / n) ^ 2) +
          |C| / n * (∑' j : ℤ, a n j * Real.exp (-(|j| : ℝ) / n))
        ≤ ((4 * Real.log 2 - 2) * C'' ^ 2 + |C'|) * (1 / n) + |C| / n * 3 := by gcongr
      _ = _ := by field_simp
  have hpt : ∀ j : ℤ, |Real.log ((1 + a n j * a n (g j)) / (1 + a n j ^ 2)) - fF j| ≤ M j := by
    intro j
    obtain ⟨η, ϑ, -, hη, hexp2, hϑ, hr⟩ := hexp g hg rfl n hn j
    have hq : |η| ≤ |C| / n := le_trans hη (by gcongr; exact le_abs_self _)
    rw [exp_two_mul_eq_sq] at hϑ
    exact term_bound _ _ _ _ _ η ϑ _ C' C'' (a_pos' n j) (a_le_one' n j) (a_pos' n (g j))
      (Real.exp_pos _).le hlog hexp2 hq hϑ hr hCl
  have hup : L - F n g ≤ ∑' j, M j :=
    hasSum_le (fun j => (abs_le.mp (hpt j)).2) hdiff hMs.hasSum
  have hlo : -∑' j, M j ≤ L - F n g :=
    hasSum_le (fun j => (abs_le.mp (hpt j)).1) hMs.hasSum.neg hdiff
  rw [abs_le]
  constructor <;> linarith

theorem tendsto_innerRatio_aux (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ)
    (hF : Filter.Tendsto (fun n => F n g) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => innerRatio g n) Filter.atTop (nhds 1) := by
  obtain ⟨K, hK⟩ := log_sum_close g hg
  have hev : ∀ᶠ n : ℕ in Filter.atTop, innerRatio g n = Real.exp (Real.log (innerRatio g n)) ∧
      |Real.log (innerRatio g n) - F n g| ≤ K / n := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    obtain ⟨L, hL, hb⟩ := hK n hn
    rw [hL, Real.log_exp]
    exact ⟨rfl, hb⟩
  have hlog : Filter.Tendsto (fun n => Real.log (innerRatio g n)) Filter.atTop (nhds 0) := by
    have hKn : Filter.Tendsto (fun n : ℕ => K / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat K
    have h2 : Filter.Tendsto (fun n => Real.log (innerRatio g n) - F n g) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ hKn
      filter_upwards [hev] with n hn
      exact hn.2
    simpa using h2.add hF
  have := (Real.continuous_exp.tendsto 0).comp hlog
  rw [Real.exp_zero] at this
  refine this.congr' ?_
  filter_upwards [hev] with n hn
  exact hn.1.symm

end JuschenkoMonod

theorem solution : ∀ (g : Equiv.Perm ℤ) (_ : g ∈ IntervalExchange.wobbling ℤ) (_ : Filter.Tendsto (fun n => JuschenkoMonod.F n g) Filter.atTop (nhds 0)), Filter.Tendsto (fun n => JuschenkoMonod.innerRatio g n) Filter.atTop (nhds 1) := fun g hg hF => JuschenkoMonod.tendsto_innerRatio_aux g hg hF
