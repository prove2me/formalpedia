-- Prove2me | solution 1 for ModernConvex.Relaxations.asin_matrix_ge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:21:38.967002+00:00
-- url     : https://prove2.me/submissions/bd62fe41-9d15-42fc-8972-606c1a0a1064

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

theorem g70mc2_choose_nonneg (n : ℕ) : 0 ≤ Ring.choose ((1 / 2 : ℝ) + n - 1) n := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose ((1 / 2 : ℝ) + n - 1) n
  rw [← Polynomial.aeval_eq_smeval, ← Polynomial.eval_map_algebraMap, descPochhammer_map,
    descPochhammer_eval_eq_prod_range] at h
  have hp : 0 ≤ ∏ j ∈ Finset.range n, ((1 / 2 : ℝ) + n - 1 - j) := by
    apply Finset.prod_nonneg
    intro j hj
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hj
    linarith
  rw [h, nsmul_eq_mul] at hp
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact nonneg_of_mul_nonneg_right (by linarith) hf |> fun h' => by nlinarith

noncomputable def g70mc2_e (n : ℕ) : ℝ := Ring.choose ((1 / 2 : ℝ) + n - 1) n

theorem g70mc2_hasSum_inv_sqrt (u : ℝ) (hu : |u| < 1) :
    HasSum (fun n => g70mc2_e n * u ^ n) (1 / Real.sqrt (1 - u)) := by
  have hf := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)
  have hmem : u ∈ EMetric.ball (0 : ℝ) 1 := by
    show edist u 0 < 1
    rw [edist_dist, dist_zero_right, Real.norm_eq_abs]
    exact ENNReal.ofReal_lt_one.mpr hu
  have := hf.hasSum hmem
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at this
  rw [Real.sqrt_eq_rpow]
  exact this

theorem g70mc2_arcsin_hasSum (t : ℝ) (ht : |t| < 1) :
    HasSum (fun n : ℕ => g70mc2_e n * t ^ (2 * n + 1) / (2 * n + 1)) (Real.arcsin t) := by
  set r : ℝ := (|t| + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have htr : |t| < r := by rw [hr]; linarith
  have hr2 : |r ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg r)]; nlinarith
  have hsumr := (g70mc2_hasSum_inv_sqrt (r ^ 2) hr2).summable
  set g : ℕ → ℝ → ℝ := fun n y => g70mc2_e n * y ^ (2 * n + 1) / (2 * n + 1)
  set g' : ℕ → ℝ → ℝ := fun n y => g70mc2_e n * y ^ (2 * n)
  set s := Metric.ball (0 : ℝ) r
  have hderiv : ∀ n y, HasDerivAt (g n) (g' n y) y := by
    intro n y
    have := ((hasDerivAt_pow (2 * n + 1) y).const_mul (g70mc2_e n)).div_const ((2 * n + 1 : ℝ))
    refine this.congr_deriv ?_
    rw [Nat.add_sub_cancel]
    simp only [g']
    push_cast
    field_simp
  have hbound : ∀ n y, y ∈ s → ‖g' n y‖ ≤ g70mc2_e n * (r ^ 2) ^ n := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    have he : 0 ≤ g70mc2_e n := g70mc2_choose_nonneg n
    simp only [g', Real.norm_eq_abs, abs_mul, abs_of_nonneg he, ← pow_mul]
    apply mul_le_mul_of_nonneg_left _ he
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hy.le _
  have hsum0 : Summable fun n => g n 0 := by
    simp only [g]; simp
  have hF : ∀ y ∈ s, HasDerivAt (fun z => ∑' n, g n z) (1 / Real.sqrt (1 - y ^ 2)) y := by
    intro y hy
    have h1 := hasDerivAt_tsum_of_isPreconnected hsumr Metric.isOpen_ball
      (convex_ball (0 : ℝ) r).isPreconnected (fun n y _ => hderiv n y) hbound
      (Metric.mem_ball_self hr0) hsum0 hy
    have hy1 : |y ^ 2| < 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
      rw [abs_of_nonneg (sq_nonneg y)]
      have : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
      nlinarith [abs_nonneg y]
    have h2 := (g70mc2_hasSum_inv_sqrt (y ^ 2) hy1).tsum_eq
    simp only [g', ← pow_mul] at h1 h2 ⊢
    rw [h2] at h1
    exact h1
  have hA : ∀ y ∈ s, HasDerivAt Real.arcsin (1 / Real.sqrt (1 - y ^ 2)) y := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    have := abs_lt.mp (hy.trans hr1)
    exact Real.hasDerivAt_arcsin (by linarith) (by linarith)
  have heq := Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℝ) r).isPreconnected
    (fun y hy => (hF y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hA y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => by simp only [(hF y hy).deriv, (hA y hy).deriv])
    (Metric.mem_ball_self hr0) (by
      show (∑' n, g n 0) = Real.arcsin 0
      rw [Real.arcsin_zero]
      simp [g])
  have hts : t ∈ s := by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact htr
  have hsumt : Summable fun n => g n t := by
    refine Summable.of_norm_bounded hsumr fun n => ?_
    have he0 : 0 ≤ g70mc2_e n := g70mc2_choose_nonneg n
    simp only [g, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg he0, abs_pow]
    rw [abs_of_pos (by positivity : (0:ℝ) < 2 * n + 1)]
    rw [div_le_iff₀ (by positivity)]
    have h1 : |t| ^ (2 * n + 1) ≤ (r ^ 2) ^ n := by
      rw [← pow_mul, pow_succ]
      calc |t| ^ (2 * n) * |t| ≤ r ^ (2 * n) * 1 := mul_le_mul
            (pow_le_pow_left₀ (abs_nonneg _) htr.le _) (by linarith) (abs_nonneg _) (by positivity)
        _ = r ^ (2 * n) := mul_one _
    have h2 : (r ^ 2) ^ n ≤ (r ^ 2) ^ n * (2 * n + 1) := by
      have : 0 ≤ (r ^ 2) ^ n := by positivity
      nlinarith
    have he := g70mc2_choose_nonneg n
    calc g70mc2_e n * |t| ^ (2 * n + 1) ≤ g70mc2_e n * (r ^ 2) ^ n :=
          mul_le_mul_of_nonneg_left h1 he
      _ ≤ g70mc2_e n * ((r ^ 2) ^ n * (2 * n + 1)) := mul_le_mul_of_nonneg_left h2 he
      _ = _ := by ring
  have := hsumt.hasSum
  have h := heq hts
  simp only at h
  rw [h] at this
  exact this

open Matrix

open ModernConvex.Relaxations

def g70mc2_hpow {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Y i j ^ m

theorem g70mc2_hpow_psd {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Y.PosSemidef) :
    ∀ m, 1 ≤ m → (g70mc2_hpow Y m).PosSemidef := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have : g70mc2_hpow Y 1 = Y := by ext i j; simp [g70mc2_hpow]
    rw [this]; exact hY
  | succ m _ ih =>
    have : g70mc2_hpow Y (m + 1) = g70mc2_hpow Y m ⊙ Y := by
      ext i j; simp [g70mc2_hpow, pow_succ]
    rw [this]; exact ih.hadamard hY

theorem g70mc2_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    star v ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, v i * M i j * v j := by
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

theorem g70mc2_strict {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Y.PosSemidef)
    (hY1 : ∀ i j, |Y i j| < 1) (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * (Real.arcsin (Y i j) - Y i j) * v j := by
  set c : ℕ → ℝ := fun m => g70mc2_e m / (2 * m + 1)
  have he0 : g70mc2_e 0 = 1 := by simp [g70mc2_e]
  have hent : ∀ i j, HasSum (fun m : ℕ => c m * Y i j ^ (2 * m + 1) - (if m = 0 then Y i j else 0))
      (Real.arcsin (Y i j) - Y i j) := by
    intro i j
    have h1 := g70mc2_arcsin_hasSum (Y i j) (hY1 i j)
    have h2 := hasSum_ite_eq 0 (Y i j)
    have := h1.sub h2
    have e : (fun m : ℕ => c m * Y i j ^ (2 * m + 1) - (if m = 0 then Y i j else 0)) =
        (fun b : ℕ => g70mc2_e b * Y i j ^ (2 * b + 1) / (2 * b + 1) -
          (if b = 0 then Y i j else 0)) := by
      funext m; simp only [c]; ring
    rw [e]; exact this
  have hq : HasSum (fun m : ℕ => ∑ i, ∑ j, v i *
      (c m * Y i j ^ (2 * m + 1) - (if m = 0 then Y i j else 0)) * v j)
      (∑ i, ∑ j, v i * (Real.arcsin (Y i j) - Y i j) * v j) := by
    apply hasSum_sum; intro i _
    apply hasSum_sum; intro j _
    exact ((hent i j).mul_left (v i)).mul_right (v j)
  refine hq.nonneg fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [c, he0]
  · have hpsd := g70mc2_hpow_psd Y hY (2 * m + 1) (by omega)
    have h1 := hpsd.dotProduct_mulVec_nonneg v
    rw [g70mc2_quad] at h1
    have hcm : 0 ≤ c m := div_nonneg (g70mc2_choose_nonneg m) (by positivity)
    have : ∑ i, ∑ j, v i * (c m * Y i j ^ (2 * m + 1) - (if m = 0 then Y i j else 0)) * v j =
        c m * ∑ i, ∑ j, v i * g70mc2_hpow Y (2 * m + 1) i j * v j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [g70mc2_hpow, hm.ne']; ring
    rw [this]
    exact mul_nonneg hcm h1

theorem solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hX1 : ∀ i j, |X i j| ≤ 1) :
    (asinMatrix X - X).PosSemidef := by
  have hsym : ∀ i j, X j i = X i j := fun i j => by
    have := congrFun (congrFun hX.isHermitian.eq i) j; simpa using this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · ext i j
    simp [asinMatrix, hsym]
  rw [g70mc2_quad]
  set f : ℝ → ℝ := fun r => ∑ i, ∑ j, v i * (Real.arcsin (r * X i j) - r * X i j) * v j
  have hf : Continuous f := by
    simp only [f]; fun_prop
  have hlim : Filter.Tendsto (fun k : ℕ => 1 - 1 / ((k : ℝ) + 2)) Filter.atTop (nhds 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub this
    simp only [sub_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply]; push_cast; ring
  have hlim2 := (hf.tendsto 1).comp hlim
  have hval : f 1 = ∑ i, ∑ j, v i * (asinMatrix X - X) i j * v j := by
    simp [f, asinMatrix]
  rw [← hval]
  refine ge_of_tendsto hlim2 (Filter.Eventually.of_forall fun k => ?_)
  simp only [Function.comp_apply]
  set r : ℝ := 1 - 1 / ((k : ℝ) + 2)
  have hr0 : 0 ≤ r := by
    simp only [r]; rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have hr1 : r < 1 := by
    have : 0 < 1 / ((k : ℝ) + 2) := by positivity
    simp only [r]; linarith
  have hY : (r • X).PosSemidef := hX.smul hr0
  have := g70mc2_strict (r • X) hY (fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hr0]
    calc r * |X i j| ≤ r * 1 := mul_le_mul_of_nonneg_left (hX1 i j) hr0
      _ < 1 := by linarith) v
  simpa [f] using this
