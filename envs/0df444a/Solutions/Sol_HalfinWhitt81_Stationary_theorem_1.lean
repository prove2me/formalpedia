-- Prove2me | solution 1 for HalfinWhitt81.Stationary.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T21:19:06.727488+00:00
-- url     : https://prove2.me/submissions/04fe92f0-1139-4774-8719-9bf258baa910

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang
import Definitions.Def_HalfinWhitt81_Stationary_Basic

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace HW81c

open QueueingFundamentals.BirthDeath HalfinWhitt81.Stationary

theorem fac_upper (u v : ℝ) (_hu1 : u ≤ 1) (hv1 : v < 1) :
    (1 - u) / (1 - v) ≤ Real.exp (-u + v / (1 - v)) := by
  have hp : 0 < 1 - v := by linarith
  have h1 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  have h2 : 1 / (1 - v) ≤ Real.exp (v / (1 - v)) := by
    have := Real.add_one_le_exp (v / (1 - v))
    have e : v / (1 - v) + 1 = 1 / (1 - v) := by field_simp; ring
    linarith
  calc (1 - u) / (1 - v) = (1 - u) * (1 / (1 - v)) := by ring
    _ ≤ Real.exp (-u) * Real.exp (v / (1 - v)) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-u + v / (1 - v)) := (Real.exp_add _ _).symm

theorem fac_lower (u v : ℝ) (hu1 : u < 1) (hv1 : v < 1) :
    Real.exp (-(u / (1 - u)) + v) ≤ (1 - u) / (1 - v) := by
  have hp : 0 < 1 - v := by linarith
  have hq : 0 < 1 - u := by linarith
  have h1 : Real.exp (-(u / (1 - u))) ≤ 1 - u := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hq]
    have := Real.add_one_le_exp (u / (1 - u))
    have e : u / (1 - u) + 1 = (1 - u)⁻¹ := by field_simp; ring
    linarith
  have h2 : Real.exp v ≤ 1 / (1 - v) := by
    rw [le_div_iff₀ hp]
    have h3 := Real.add_one_le_exp (-v)
    have e : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos v]
  calc Real.exp (-(u / (1 - u)) + v) = Real.exp (-(u / (1 - u))) * Real.exp v := Real.exp_add _ _
    _ ≤ (1 - u) * (1 / (1 - v)) := mul_le_mul h1 h2 (Real.exp_pos _).le hq.le
    _ = (1 - u) / (1 - v) := by ring

theorem sum_range_id_real (k : ℕ) : ∑ j ∈ Finset.range k, (j : ℝ) = k * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem tendsto_sqrt_nat : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_floor_div (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => (⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n) atTop (𝓝 x) := by
  have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_sqrt_nat.inv_tendsto_atTop
  have hlow : Tendsto (fun n : ℕ => x - (Real.sqrt n)⁻¹) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
    rw [le_div_iff₀ hq]
    have := Nat.lt_floor_add_one (x * Real.sqrt n)
    have e : (x - (Real.sqrt n)⁻¹) * Real.sqrt n = x * Real.sqrt n - 1 := by field_simp
    rw [e]; linarith
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
    rw [div_le_iff₀ hq]
    exact Nat.floor_le (by positivity)

theorem exp_neg_div_le (v : ℝ) (hv1 : v < 1) : Real.exp (-(v / (1 - v))) ≤ 1 - v := by
  have hq : 0 < 1 - v := by linarith
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hq]
  have := Real.add_one_le_exp (v / (1 - v))
  have e : v / (1 - v) + 1 = (1 - v)⁻¹ := by field_simp; ring
  linarith

theorem one_sub_le_exp_neg (v : ℝ) : 1 - v ≤ Real.exp (-v) := by
  linarith [Real.add_one_le_exp (-v)]

theorem v_tendsto (v : ℕ → ℝ) (β : ℝ)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β)) :
    Tendsto v atTop (𝓝 0) := by
  have h := hc.mul (tendsto_sqrt_nat.inv_tendsto_atTop)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
  change v n * Real.sqrt n * (Real.sqrt n)⁻¹ = v n
  field_simp

theorem ind_integral (q : ℝ) (hq : 0 < q) (m : ℕ) (c : ℝ) :
    ∫ x in Set.Ici (0 : ℝ), (Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c) x
      = q⁻¹ * c := by
  have hsub : Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q) ⊆ Set.Ici 0 := by
    intro y hy
    exact le_trans (by positivity) hy.1
  have hle : (m : ℝ) / q ≤ ((m : ℝ) + 1) / q :=
    div_le_div_of_nonneg_right (by linarith) hq.le
  rw [integral_indicator_const _ measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 hsub, Real.volume_real_Ico_of_le hle, smul_eq_mul]
  have : ((m : ℝ) + 1) / q - (m : ℝ) / q = q⁻¹ := by ring
  rw [this]

theorem ind_integrable (q : ℝ) (m : ℕ) (c : ℝ) :
    Integrable (fun x : ℝ => (Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c) x)
      (volume.restrict (Set.Ici (0 : ℝ))) := by
  refine Integrable.restrict ?_
  exact (integrable_indicator_iff measurableSet_Ico).2
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))

theorem H_eq (q : ℝ) (hq : 0 < q) (c : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) :
    ∑' m : ℕ, (Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c m) x
      = c ⌊x * q⌋₊ := by
  have hxq : 0 ≤ x * q := by positivity
  rw [tsum_eq_single ⌊x * q⌋₊]
  · rw [Set.indicator_of_mem]
    rw [Set.mem_Ico, div_le_iff₀ hq, lt_div_iff₀ hq]
    exact ⟨Nat.floor_le hxq, Nat.lt_floor_add_one _⟩
  · intro m hm
    rw [Set.indicator_of_notMem]
    intro hmem
    rw [Set.mem_Ico, div_le_iff₀ hq, lt_div_iff₀ hq] at hmem
    exact hm ((Nat.floor_eq_iff hxq).2 ⟨hmem.1, hmem.2⟩).symm

theorem step_integral (q : ℝ) (hq : 0 < q) (c : ℕ → ℝ) (hs : Summable fun m => |c m|) :
    ∫ x in Set.Ici (0 : ℝ),
      (∑' m : ℕ, (Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c m) x)
      = q⁻¹ * ∑' m, c m := by
  have hsum : Summable fun m : ℕ => ∫ x in Set.Ici (0 : ℝ),
      ‖(Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c m) x‖ := by
    have : ∀ m : ℕ, ∫ x in Set.Ici (0 : ℝ),
        ‖(Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c m) x‖ =
          q⁻¹ * |c m| := by
      intro m
      simp_rw [norm_indicator_eq_indicator_norm, Real.norm_eq_abs]
      exact ind_integral q hq m |c m|
    simp_rw [this]
    exact hs.mul_left q⁻¹
  rw [← integral_tsum_of_summable_integral_norm (fun m => ind_integrable q m (c m)) hsum]
  simp_rw [ind_integral q hq]
  rw [tsum_mul_left]

/-- left products `∏_{i<j} (1 - i/n)/(1 - v)`. -/
noncomputable def uL (n : ℕ) (v : ℝ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, (1 - (i : ℝ) / n) / (1 - v)

theorem uL_nonneg (n : ℕ) (v : ℝ) (j : ℕ) (hn : 0 < n) (hj : j ≤ n) (hv : v < 1) :
    0 ≤ uL n v j := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold uL
  refine Finset.prod_nonneg fun i hi => ?_
  have h1 : i < n := lt_of_lt_of_le (Finset.mem_range.1 hi) hj
  have h2 : (i : ℝ) < n := by exact_mod_cast h1
  have h3 : (i : ℝ) / n ≤ 1 := by rw [div_le_one hnr]; linarith
  apply div_nonneg <;> linarith

theorem uL_upper (n : ℕ) (q : ℝ) (hq : (n : ℝ) = q ^ 2) (v : ℝ) (j : ℕ) (hn : 0 < n)
    (hj : j ≤ n) (hv : v < 1) :
    uL n v j ≤ Real.exp (-((j : ℝ) * (j - 1) / 2) / q ^ 2 + j * (v / (1 - v))) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← hq]
  unfold uL
  calc ∏ i ∈ Finset.range j, (1 - (i : ℝ) / n) / (1 - v)
      ≤ ∏ i ∈ Finset.range j, Real.exp (-((i : ℝ) / n) + v / (1 - v)) := by
        refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
        · have h1 : i < n := lt_of_lt_of_le (Finset.mem_range.1 hi) hj
          have h2 : (i : ℝ) < n := by exact_mod_cast h1
          have h3 : (i : ℝ) / n ≤ 1 := by rw [div_le_one hnr]; linarith
          apply div_nonneg <;> linarith
        · have h1 : i < n := lt_of_lt_of_le (Finset.mem_range.1 hi) hj
          have h2 : (i : ℝ) < n := by exact_mod_cast h1
          exact fac_upper _ _ (by rw [div_le_one hnr]; linarith) hv
    _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_div,
          sum_range_id_real, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem uL_lower (n : ℕ) (q : ℝ) (hq : (n : ℝ) = q ^ 2) (v : ℝ) (j : ℕ) (hn : 0 < n)
    (hj : j < n) (hv : v < 1) :
    Real.exp (-((j : ℝ) * (j - 1) / 2) / (q ^ 2 - j) + j * v) ≤ uL n v j := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hjr : (j : ℝ) < n := by exact_mod_cast hj
  rw [← hq]
  unfold uL
  calc Real.exp (-((j : ℝ) * (j - 1) / 2) / ((n : ℝ) - j) + j * v)
      = ∏ i ∈ Finset.range j, Real.exp (-((i : ℝ) / ((n : ℝ) - j)) + v) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_div,
          sum_range_id_real, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ ∏ i ∈ Finset.range j, (1 - (i : ℝ) / n) / (1 - v) := by
        refine Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i hi => ?_
        have hij : i < j := Finset.mem_range.1 hi
        have hi0 : (0 : ℝ) ≤ i := by positivity
        have hijr : (i : ℝ) < j := by exact_mod_cast hij
        have hu : (i : ℝ) / n < 1 := by rw [div_lt_one hnr]; linarith
        refine le_trans ?_ (fac_lower _ _ hu hv)
        apply Real.exp_le_exp.2
        have e : (i : ℝ) / n / (1 - (i : ℝ) / n) = (i : ℝ) / ((n : ℝ) - i) := by
          field_simp
        rw [e]
        have : (i : ℝ) / ((n : ℝ) - i) ≤ (i : ℝ) / ((n : ℝ) - j) :=
          div_le_div_of_nonneg_left hi0 (by linarith) (by linarith)
        linarith

theorem expo_upper_eq (q v j : ℝ) (hq : 0 < q) (hv : v < 1) :
    -(j * (j - 1) / 2) / q ^ 2 + j * (v / (1 - v)) =
      -((j / q) * (j / q - q⁻¹)) / 2 + (j / q) * ((v * q) / (1 - v)) := by
  have h1 : 1 - v ≠ 0 := by intro h; linarith
  field_simp
  try ring

theorem expo_lower_eq (q v j : ℝ) (hq : 0 < q) (hj : j < q ^ 2) :
    -(j * (j - 1) / 2) / (q ^ 2 - j) + j * v =
      -((j / q) * (j / q - q⁻¹) / 2) / (1 - (j / q) * q⁻¹) + (j / q) * (v * q) := by
  have h1 : q ^ 2 - j ≠ 0 := by intro h; linarith
  have h2 : 1 - (j / q) * q⁻¹ = (q ^ 2 - j) / q ^ 2 := by field_simp
  rw [h2]
  field_simp
  try ring

theorem tendsto_ceil_div (y : ℝ) (hy : 0 ≤ y) :
    Tendsto (fun n : ℕ => (⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n) atTop (𝓝 y) := by
  have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_sqrt_nat.inv_tendsto_atTop
  have hup : Tendsto (fun n : ℕ => y + (Real.sqrt n)⁻¹) atTop (𝓝 y) := by
    simpa using (tendsto_const_nhds (x := y)).add hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
    rw [le_div_iff₀ hq]
    exact Nat.le_ceil _
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
    rw [div_le_iff₀ hq]
    have := Nat.ceil_lt_add_one (a := y * Real.sqrt n) (by positivity)
    have e : (y + (Real.sqrt n)⁻¹) * Real.sqrt n = y * Real.sqrt n + 1 := by field_simp
    rw [e]; linarith

theorem uL_pointwise (v : ℕ → ℝ) (β : ℝ)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β))
    (hv0 : ∀ n : ℕ, 1 ≤ n → 0 < v n ∧ v n < 1) (y : ℝ) (hy : 0 ≤ y) :
    Tendsto (fun n : ℕ => uL n (v n) ⌈y * Real.sqrt n⌉₊) atTop
      (𝓝 (Real.exp (β * y - y ^ 2 / 2))) := by
  have hv := v_tendsto v β hc
  have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_sqrt_nat.inv_tendsto_atTop
  have ht := tendsto_ceil_div y hy
  have hU : Tendsto (fun n : ℕ =>
      -(((⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n) * ((⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n
        - (Real.sqrt n)⁻¹)) / 2 + ((⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n) *
        ((v n * Real.sqrt n) / (1 - v n))) atTop (𝓝 (β * y - y ^ 2 / 2)) := by
    have := ((ht.mul (ht.sub hs)).neg.div_const 2).add
      (ht.mul (hc.div (tendsto_const_nhds.sub hv) (show (1 : ℝ) - 0 ≠ 0 by norm_num)))
    have e : β * y - y ^ 2 / 2 = -(y * (y - 0)) / 2 + y * (β / (1 - 0)) := by ring
    rw [e]; exact this
  have hL : Tendsto (fun n : ℕ =>
      -(((⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n) * ((⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n
        - (Real.sqrt n)⁻¹) / 2) / (1 - ((⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n) *
        (Real.sqrt n)⁻¹) + ((⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n) * (v n * Real.sqrt n))
      atTop (𝓝 (β * y - y ^ 2 / 2)) := by
    have := (((ht.mul (ht.sub hs)).div_const 2).neg.div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (ht.mul hs))
      (show (1 : ℝ) - y * 0 ≠ 0 by norm_num)).add (ht.mul hc)
    have e : β * y - y ^ 2 / 2 = -(y * (y - 0) / 2) / (1 - y * 0) + y * β := by ring
    rw [e]; exact this
  have hUe := hU.rexp
  have hLe := hL.rexp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLe hUe ?_ ?_
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop (y + 1)] with n hq
    have hq0 : 0 < Real.sqrt n := lt_of_le_of_lt (by linarith) hq
    have hn : 0 < n := by
      have : (0 : ℝ) < n := Real.sqrt_pos.1 hq0
      exact_mod_cast this
    have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    have hj : (⌈y * Real.sqrt n⌉₊ : ℝ) < n := by
      have h1 := Nat.ceil_lt_add_one (a := y * Real.sqrt n) (by positivity)
      have : y * Real.sqrt n + 1 ≤ Real.sqrt n * Real.sqrt n := by nlinarith
      calc (⌈y * Real.sqrt n⌉₊ : ℝ) < y * Real.sqrt n + 1 := h1
        _ ≤ Real.sqrt n * Real.sqrt n := this
        _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hjn : ⌈y * Real.sqrt n⌉₊ < n := by exact_mod_cast hj
    have := uL_lower n (Real.sqrt n) hn2 (v n) _ hn hjn (hv0 n hn).2
    rw [expo_lower_eq _ _ _ hq0 (by rw [← hn2]; exact hj)] at this
    exact this
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop (y + 1)] with n hq
    have hq0 : 0 < Real.sqrt n := lt_of_le_of_lt (by linarith) hq
    have hn : 0 < n := by
      have : (0 : ℝ) < n := Real.sqrt_pos.1 hq0
      exact_mod_cast this
    have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    have hj : (⌈y * Real.sqrt n⌉₊ : ℝ) < n := by
      have h1 := Nat.ceil_lt_add_one (a := y * Real.sqrt n) (by positivity)
      have : y * Real.sqrt n + 1 ≤ Real.sqrt n * Real.sqrt n := by nlinarith
      calc (⌈y * Real.sqrt n⌉₊ : ℝ) < y * Real.sqrt n + 1 := h1
        _ ≤ Real.sqrt n * Real.sqrt n := this
        _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hjn : ⌈y * Real.sqrt n⌉₊ < n := by exact_mod_cast hj
    have := uL_upper n (Real.sqrt n) hn2 (v n) _ hn hjn.le (hv0 n hn).2
    rw [expo_upper_eq _ _ _ hq0 (hv0 n hn).2] at this
    exact this

/-- the real-variable bound used for domination. -/
theorem uL_exp_bound (q y j v β : ℝ) (hq1 : 1 ≤ q) (hy : 0 < y) (hj1 : 1 ≤ j)
    (hjy : y * q ≤ j) (hjy2 : j < y * q + 1) (hvq : v * q ≤ 2 * β) (hv0 : 0 < v)
    (hv2 : v ≤ 1 / 2) (hβ : 0 < β) :
    -(j * (j - 1) / 2) / q ^ 2 + j * (v / (1 - v)) ≤
      -y ^ 2 / 2 + y / 2 + 2 * (2 * β) * (y + 1) := by
  have hq0 : 0 < q := by linarith
  have h1 : v / (1 - v) ≤ 2 * v := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hvle : v ≤ 2 * β := by nlinarith
  have h2 : j * v ≤ 2 * β * (y + 1) := by nlinarith
  have h3 : j * (v / (1 - v)) ≤ 2 * (2 * β) * (y + 1) := by
    have : j * (v / (1 - v)) ≤ j * (2 * v) := mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  have h4 : y ^ 2 / 2 - y / 2 ≤ (j * (j - 1) / 2) / q ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : y * q * (y * q - 1) ≤ j * (j - 1) := by nlinarith
    have h5 : y * q ≤ y * q ^ 2 := by nlinarith
    nlinarith
  have : -(j * (j - 1) / 2) / q ^ 2 = -((j * (j - 1) / 2) / q ^ 2) := by ring
  rw [this]
  linarith

noncomputable def FL (v : ℕ → ℝ) (g : ℝ → ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, (Set.Ioc ((m : ℝ) / Real.sqrt n) (((m : ℝ) + 1) / Real.sqrt n)).indicator
    (fun _ => uL n (v n) (m + 1) * g (-((m : ℝ) + 1) / Real.sqrt n)) y

theorem FL_eq (v : ℕ → ℝ) (g : ℝ → ℝ) (n : ℕ) (hn : 0 < n) (y : ℝ) (hy : 0 < y) :
    FL v g n y = if ⌈y * Real.sqrt n⌉₊ - 1 < n then
      uL n (v n) ⌈y * Real.sqrt n⌉₊ * g (-(⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n) else 0 := by
  have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hyq : 0 < y * Real.sqrt n := mul_pos hy hq
  have hk : 1 ≤ ⌈y * Real.sqrt n⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hyq).ne'
  set k := ⌈y * Real.sqrt n⌉₊ with hk_def
  have hkc : ((k - 1 : ℕ) : ℝ) + 1 = k := by
    have : k - 1 + 1 = k := by omega
    exact_mod_cast this
  have key : ∀ m : ℕ, (Set.Ioc ((m : ℝ) / Real.sqrt n) (((m : ℝ) + 1) / Real.sqrt n)).indicator
      (fun _ => uL n (v n) (m + 1) * g (-((m : ℝ) + 1) / Real.sqrt n)) y =
      if k - 1 = m then uL n (v n) (m + 1) * g (-((m : ℝ) + 1) / Real.sqrt n) else 0 := by
    intro m
    by_cases h : k - 1 = m
    · rw [if_pos h, Set.indicator_of_mem]
      rw [Set.mem_Ioc, div_lt_iff₀ hq, le_div_iff₀ hq]
      have := (Nat.ceil_eq_iff (a := y * Real.sqrt n) (n := k) (by omega)).1 rfl
      subst h
      exact ⟨this.1, by rw [hkc]; exact this.2⟩
    · rw [if_neg h, Set.indicator_of_notMem]
      intro hmem
      rw [Set.mem_Ioc, div_lt_iff₀ hq, le_div_iff₀ hq] at hmem
      apply h
      have : ⌈y * Real.sqrt n⌉₊ = m + 1 := by
        refine (Nat.ceil_eq_iff (by omega)).2 ⟨?_, ?_⟩
        · simpa using hmem.1
        · push_cast; exact hmem.2
      omega
  unfold FL
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]
  split_ifs with h
  · have e : k - 1 + 1 = k := by omega
    rw [e]
    congr 2
    rw [← hkc]
    try ring
  · rfl

theorem FL_meas (v : ℕ → ℝ) (g : ℝ → ℝ) (n : ℕ) : Measurable (FL v g n) := by
  unfold FL
  exact Finset.measurable_sum _ fun m _ => measurable_const.indicator measurableSet_Ioc

theorem indL_integral (q : ℝ) (hq : 0 < q) (m : ℕ) (c : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), (Set.Ioc ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c) x
      = q⁻¹ * c := by
  have hsub : Set.Ioc ((m : ℝ) / q) (((m : ℝ) + 1) / q) ⊆ Set.Ioi 0 := by
    intro y hy
    exact lt_of_le_of_lt (by positivity) hy.1
  have hle : (m : ℝ) / q ≤ ((m : ℝ) + 1) / q :=
    div_le_div_of_nonneg_right (by linarith) hq.le
  rw [integral_indicator_const _ measurableSet_Ioc, measureReal_restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 hsub, Real.volume_real_Ioc_of_le hle, smul_eq_mul]
  have : ((m : ℝ) + 1) / q - (m : ℝ) / q = q⁻¹ := by ring
  rw [this]

theorem FL_integral (v : ℕ → ℝ) (g : ℝ → ℝ) (n : ℕ) (hn : 0 < n) :
    ∫ y in Set.Ioi (0 : ℝ), FL v g n y = (Real.sqrt n)⁻¹ *
      ∑ m ∈ Finset.range n, uL n (v n) (m + 1) * g (-((m : ℝ) + 1) / Real.sqrt n) := by
  have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  unfold FL
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => indL_integral _ hq m _
  · intro m _
    refine Integrable.restrict ?_
    exact (integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))

theorem bound_integrable' (β : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2 + x / 2 + 2 * β * (x + 1)))
      (volume.restrict (Set.Ici 0)) := by
  set b : ℝ := 2 * β + 1 / 2
  have hg := ((integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).comp_sub_right b).const_mul
    (Real.exp (2 * β + b ^ 2 / 2))
  refine (hg.congr (ae_of_all _ fun x => ?_)).restrict
  simp only
  rw [← Real.exp_add]
  congr 1
  simp only [b]
  ring

theorem left_core (v : ℕ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hv0 : ∀ n : ℕ, 1 ≤ n → 0 < v n ∧ v n < 1)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β))
    (g : ℝ → ℝ) (hgc : Continuous g) (C : ℝ) (hg : ∀ x, |g x| ≤ C) :
    Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ *
      ∑ m ∈ Finset.range n, uL n (v n) (m + 1) * g (-((m : ℝ) + 1) / Real.sqrt n))
      atTop (𝓝 (∫ y in Set.Ioi (0 : ℝ), Real.exp (β * y - y ^ 2 / 2) * g (-y))) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hg 0)
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ v n * Real.sqrt n < 2 * β ∧
      max 1 (4 * β) ≤ Real.sqrt n :=
    (eventually_ge_atTop 1).and ((hc.eventually (gt_mem_nhds (by linarith))).and
      (tendsto_sqrt_nat.eventually_ge_atTop _))
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (l := atTop) (F := FL v g)
    (f := fun y => Real.exp (β * y - y ^ 2 / 2) * g (-y))
    (fun y => C * Real.exp (-y ^ 2 / 2 + y / 2 + 2 * (2 * β) * (y + 1)))
    (Eventually.of_forall fun n => (FL_meas v g n).aestronglyMeasurable)
    (by
      filter_upwards [hev] with n ⟨hn, hcn, hqn⟩
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
      have hy : 0 < y := hy
      obtain ⟨h0, h1⟩ := hv0 n hn
      have hn0 : 0 < n := by omega
      have hq1 : 1 ≤ Real.sqrt n := le_trans (le_max_left _ _) hqn
      have hq4 : 4 * β ≤ Real.sqrt n := le_trans (le_max_right _ _) hqn
      have hq0 : 0 < Real.sqrt n := by linarith
      have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
      rw [FL_eq v g n hn0 y hy]
      split_ifs with hjn
      · set j := ⌈y * Real.sqrt n⌉₊ with hj
        have hyq : 0 < y * Real.sqrt n := mul_pos hy hq0
        have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hyq).ne'
        have hjn' : j ≤ n := by omega
        have hu0 := uL_nonneg n (v n) j hn0 hjn' h1
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0]
        have hup := uL_upper n (Real.sqrt n) hn2 (v n) j hn0 hjn' h1
        have hv2 : v n ≤ 1 / 2 := by
          have : v n * Real.sqrt n ≤ 2 * β := hcn.le
          nlinarith
        have hexp := uL_exp_bound (Real.sqrt n) y j (v n) β hq1 hy (by exact_mod_cast hj1)
          (Nat.le_ceil _) (Nat.ceil_lt_add_one hyq.le) hcn.le h0 hv2 hβ
        calc uL n (v n) j * |g (-(j : ℝ) / Real.sqrt n)|
            ≤ Real.exp (-y ^ 2 / 2 + y / 2 + 2 * (2 * β) * (y + 1)) * C :=
              mul_le_mul (hup.trans (Real.exp_le_exp.2 hexp)) (hg _) (abs_nonneg _)
                (Real.exp_pos _).le
          _ = C * Real.exp (-y ^ 2 / 2 + y / 2 + 2 * (2 * β) * (y + 1)) := by ring
      · rw [norm_zero]; positivity)
    (by
      exact (bound_integrable' (2 * β)).mono_measure
        (Measure.restrict_mono Set.Ioi_subset_Ici_self le_rfl) |>.const_mul C)
    (by
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
      have hy : 0 < y := hy
      have hg' : Tendsto (fun n : ℕ => g (-(⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n)) atTop
          (𝓝 (g (-y))) := by
        have h : Tendsto (fun n : ℕ => -(⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n) atTop (𝓝 (-y)) := by
          simpa only [neg_div] using (tendsto_ceil_div y hy.le).neg
        exact (hgc.tendsto (-y)).comp h
      refine ((uL_pointwise v β hc hv0 y hy.le).mul hg').congr' ?_
      filter_upwards [eventually_ge_atTop 1, tendsto_sqrt_nat.eventually_gt_atTop (y + 1)]
        with n hn hq
      have hn0 : 0 < n := by omega
      have hq0 : 0 < Real.sqrt n := lt_of_le_of_lt (by linarith) hq
      have hj : (⌈y * Real.sqrt n⌉₊ : ℝ) < n := by
        have h1 := Nat.ceil_lt_add_one (a := y * Real.sqrt n) (by positivity)
        have : y * Real.sqrt n + 1 ≤ Real.sqrt n * Real.sqrt n := by nlinarith
        calc (⌈y * Real.sqrt n⌉₊ : ℝ) < y * Real.sqrt n + 1 := h1
          _ ≤ Real.sqrt n * Real.sqrt n := this
          _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
      have hjn : ⌈y * Real.sqrt n⌉₊ < n := by exact_mod_cast hj
      show uL n (v n) ⌈y * Real.sqrt n⌉₊ * g (-(⌈y * Real.sqrt n⌉₊ : ℝ) / Real.sqrt n) =
        FL v g n y
      rw [FL_eq v g n hn0 y hy, if_pos (by omega)])
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact FL_integral v g n (by omega)

theorem flux (lam μ : ℝ) (n : ℕ) (p : ℕ → ℝ)
    (h : IsSteadyState (fun _ => lam) (mmcDeath μ n) p) :
    ∀ k : ℕ, lam * p k = mmcDeath μ n (k + 1) * p (k + 1) := by
  obtain ⟨_, _, hb1, hb2⟩ := h
  intro k
  induction k with
  | zero => simpa using hb2
  | succ k ih =>
    have := hb1 (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    linarith

theorem right_struct (lam μ : ℝ) (n : ℕ) (hn : 1 ≤ n) (hμ : 0 < μ) (p : ℕ → ℝ)
    (h : IsSteadyState (fun _ => lam) (mmcDeath μ n) p) :
    ∀ m : ℕ, p (n + m) = p n * (lam / (n * μ)) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hf := flux lam μ n p h (n + m)
    have hd : mmcDeath μ n (n + m + 1) = n * μ := by
      have : min (n + m + 1) n = n := by omega
      simp [mmcDeath, this]
    rw [hd] at hf
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hnm : (n : ℝ) * μ ≠ 0 := by positivity
    have : p (n + m + 1) = lam / (n * μ) * p (n + m) := by
      field_simp
      linarith
    rw [show n + (m + 1) = n + m + 1 by ring, this, ih]
    ring

theorem left_struct (lam μ : ℝ) (n : ℕ) (hn : 1 ≤ n) (hμ : 0 < μ) (hlam : 0 < lam) (p : ℕ → ℝ)
    (h : IsSteadyState (fun _ => lam) (mmcDeath μ n) p) :
    ∀ j : ℕ, j ≤ n → p (n - j) = p n * uL n (1 - lam / (n * μ)) j := by
  intro j
  induction j with
  | zero => intro _; simp [uL]
  | succ j ih =>
    intro hj
    have hf := flux lam μ n p h (n - (j + 1))
    have e1 : n - (j + 1) + 1 = n - j := by omega
    rw [e1] at hf
    have hd : mmcDeath μ n (n - j) = ((n : ℝ) - j) * μ := by
      have : min (n - j) n = n - j := by omega
      simp only [mmcDeath, this]
      rw [Nat.cast_sub (by omega)]
    rw [hd] at hf
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hjr : (j : ℝ) < n := by exact_mod_cast (by omega : j < n)
    have hq := ih (by omega)
    have hρ : 1 - (1 - lam / (n * μ)) = lam / (n * μ) := by ring
    have hnm : (n : ℝ) * μ ≠ 0 := by positivity
    unfold uL at hq ⊢
    rw [Finset.prod_range_succ, hρ] at *
    have : p (n - (j + 1)) = ((n - j) * μ / lam) * p (n - j) := by
      field_simp
      linarith
    rw [this, hq]
    have : ((n : ℝ) - j) * μ / lam = (1 - (j : ℝ) / n) / (lam / (n * μ)) := by
      field_simp
    rw [this]
    ring

/-- the scaled sums, factored through `p n`. -/
noncomputable def Asum (n : ℕ) (v : ℝ) (g : ℝ → ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * (∑ m ∈ Finset.range n, uL n v (m + 1) * g (-((m : ℝ) + 1) / Real.sqrt n)
     + ∑' m : ℕ, (1 - v) ^ m * g ((m : ℝ) / Real.sqrt n))

theorem scaled_eq (lam μ : ℝ) (n : ℕ) (hn : 1 ≤ n) (hμ : 0 < μ) (hlam : 0 < lam)
    (hlt : lam < n * μ) (v : ℝ) (hv : 1 - v = lam / (n * μ)) (p : ℕ → ℝ)
    (h : IsSteadyState (fun _ => lam) (mmcDeath μ n) p) (g : ℝ → ℝ) (C : ℝ)
    (hg : ∀ x, |g x| ≤ C) :
    scaledExpect p n g = p n * Real.sqrt n * Asum n v g := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hρ0 : 0 < lam / (n * μ) := by positivity
  have hρ1 : lam / (n * μ) < 1 := by rw [div_lt_one (by positivity)]; exact hlt
  have hvv : v = 1 - lam / (n * μ) := by linarith
  have hsum : Summable p := h.2.1.summable
  have hnn : ∀ k, 0 ≤ p k := h.1
  have hF : Summable (fun k : ℕ => p k * g (((k : ℝ) - n) / Real.sqrt n)) := by
    refine Summable.of_norm_bounded (hsum.mul_right C) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn k)]
    exact mul_le_mul_of_nonneg_left (hg _) (hnn k)
  unfold scaledExpect
  rw [← hF.sum_add_tsum_nat_add n]
  have hleft : ∑ k ∈ Finset.range n, p k * g (((k : ℝ) - n) / Real.sqrt n) =
      p n * ∑ m ∈ Finset.range n, uL n v (m + 1) * g (-((m : ℝ) + 1) / Real.sqrt n) := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.1 hj
    have e1 : n - 1 - j = n - (j + 1) := by omega
    rw [e1, left_struct lam μ n hn hμ hlam p h (j + 1) (by omega), hvv]
    have : ((n - (j + 1) : ℕ) : ℝ) = n - (j + 1) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]
    have e2 : ((n : ℝ) - (j + 1) - n) = -((j : ℝ) + 1) := by ring
    rw [e2]; ring
  have hright : ∑' i : ℕ, p (i + n) * g ((((i + n : ℕ) : ℝ) - n) / Real.sqrt n) =
      p n * ∑' m : ℕ, (1 - v) ^ m * g ((m : ℝ) / Real.sqrt n) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [add_comm i n, right_struct lam μ n hn hμ p h i, hv]
    have : (((n + i : ℕ) : ℝ) - n) = i := by push_cast; ring
    rw [this]; ring
  rw [hleft, hright]
  unfold Asum
  field_simp

theorem scaled_one (lam μ : ℝ) (n : ℕ) (hn : 1 ≤ n) (hμ : 0 < μ) (hlam : 0 < lam)
    (hlt : lam < n * μ) (v : ℝ) (hv : 1 - v = lam / (n * μ)) (p : ℕ → ℝ)
    (h : IsSteadyState (fun _ => lam) (mmcDeath μ n) p) :
    p n * Real.sqrt n * Asum n v (fun _ => 1) = 1 := by
  rw [← scaled_eq lam μ n hn hμ hlam hlt v hv p h (fun _ => 1) 1 (fun _ => by simp)]
  unfold scaledExpect
  simpa using h.2.1.tsum_eq


theorem pow_pointwise (v : ℕ → ℝ) (β : ℝ)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β))
    (hv0 : ∀ n : ℕ, 1 ≤ n → 0 < v n ∧ v n < 1) (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => (1 - v n) ^ ⌊x * Real.sqrt n⌋₊) atTop (𝓝 (Real.exp (-(β * x)))) := by
  have hv := v_tendsto v β hc
  have ht := tendsto_floor_div x hx
  have hU : Tendsto (fun n : ℕ => (⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n * (v n * Real.sqrt n))
      atTop (𝓝 (x * β)) := ht.mul hc
  have hL : Tendsto (fun n : ℕ => (⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n * (v n * Real.sqrt n)
      / (1 - v n)) atTop (𝓝 (x * β)) := by
    have h := hU.div (tendsto_const_nhds.sub hv) (show (1:ℝ) - 0 ≠ 0 by norm_num)
    rw [show x * β / (1 - 0) = x * β by norm_num] at h
    exact h
  have e : Real.exp (-(β * x)) = Real.exp (-(x * β)) := by rw [mul_comm]
  have hUe := hU.neg.rexp
  have hLe := hL.neg.rexp
  rw [← e] at hUe hLe
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLe hUe ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨h0, h1⟩ := hv0 n hn
    have hq : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))).ne'
    set m := ⌊x * Real.sqrt n⌋₊
    have e : (m : ℝ) / Real.sqrt n * (v n * Real.sqrt n) / (1 - v n)
        = m * (v n / (1 - v n)) := by field_simp
    beta_reduce
    rw [e, show -((m : ℝ) * (v n / (1 - v n))) = (m : ℝ) * (-(v n / (1 - v n))) by ring,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_div_le _ h1) m
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨h0, h1⟩ := hv0 n hn
    have hq : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))).ne'
    set m := ⌊x * Real.sqrt n⌋₊
    have e : (m : ℝ) / Real.sqrt n * (v n * Real.sqrt n) = m * v n := by field_simp
    beta_reduce
    rw [e, show -((m : ℝ) * v n) = (m : ℝ) * (-v n) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (one_sub_le_exp_neg _) m

theorem right_core (v : ℕ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hv0 : ∀ n : ℕ, 1 ≤ n → 0 < v n ∧ v n < 1)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β))
    (g : ℝ → ℝ) (hgc : Continuous g) (C : ℝ) (hg : ∀ x, |g x| ≤ C) :
    Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ * ∑' m : ℕ, (1 - v n) ^ m * g ((m : ℝ) / Real.sqrt n))
      atTop (𝓝 (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) * g x)) := by
  rw [← integral_Ici_eq_integral_Ioi]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hg 0)
  set G : ℕ → ℝ → ℝ := fun n x =>
    (1 - v n) ^ ⌊x * Real.sqrt n⌋₊ * g ((⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n) with hG
  have hmeas : ∀ n, Measurable (G n) := by
    intro n
    have : G n = (fun m : ℕ => (1 - v n) ^ m * g ((m : ℝ) / Real.sqrt n)) ∘
        (fun x : ℝ => ⌊x * Real.sqrt n⌋₊) := by ext x; rfl
    rw [this]
    exact measurable_from_nat.comp (Nat.measurable_floor.comp (measurable_id.mul_const _))
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ β / 2 < v n * Real.sqrt n :=
    (eventually_ge_atTop 1).and (hc.eventually (lt_mem_nhds (by linarith)))
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ici (0 : ℝ))) (l := atTop) (F := G)
    (f := fun x => Real.exp (-(β * x)) * g x)
    (fun x => C * Real.exp 1 * Real.exp (-(β / 2) * x))
    (Eventually.of_forall fun n => (hmeas n).aestronglyMeasurable)
    (by
      filter_upwards [hev] with n ⟨hn, hcn⟩
      refine ae_restrict_of_forall_mem measurableSet_Ici fun x hx => ?_
      have hx : 0 ≤ x := hx
      obtain ⟨h0, h1⟩ := hv0 n hn
      have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
      simp only [hG]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (by linarith) _)]
      set m := ⌊x * Real.sqrt n⌋₊ with hm
      have hpow : (1 - v n) ^ m ≤ Real.exp (-(m * v n)) := by
        calc (1 - v n) ^ m ≤ Real.exp (-(v n)) ^ m :=
              pow_le_pow_left₀ (by linarith) (one_sub_le_exp_neg _) m
          _ = Real.exp (-(m * v n)) := by rw [← Real.exp_nat_mul]; ring_nf
      have hmv : x * (β / 2) - 1 ≤ m * v n := by
        have := Nat.lt_floor_add_one (x * Real.sqrt n)
        nlinarith [mul_pos (sub_pos.2 this) h0, mul_nonneg hx (le_of_lt (sub_pos.2 hcn))]
      have hexp : Real.exp (-(m * v n)) ≤ Real.exp 1 * Real.exp (-(β / 2) * x) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith
      calc (1 - v n) ^ m * |g ((m : ℝ) / Real.sqrt n)|
          ≤ Real.exp (-(m * v n)) * C :=
            mul_le_mul hpow (hg _) (abs_nonneg _) (Real.exp_pos _).le
        _ ≤ (Real.exp 1 * Real.exp (-(β / 2) * x)) * C :=
            mul_le_mul_of_nonneg_right hexp hC
        _ = C * Real.exp 1 * Real.exp (-(β / 2) * x) := by ring)
    (by
      have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(β / 2) * x)) (Set.Ioi 0) :=
        integrableOn_exp_mul_Ioi (by linarith) 0
      exact (integrableOn_Ici_iff_integrableOn_Ioi).2 (h1.const_mul (C * Real.exp 1)))
    (by
      refine ae_restrict_of_forall_mem measurableSet_Ici fun x hx => ?_
      have hx : 0 ≤ x := hx
      exact (pow_pointwise v β hc hv0 x hx).mul
        ((hgc.tendsto x).comp (tendsto_floor_div x hx)))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨h0, h1⟩ := hv0 n hn
  have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
  have hs : Summable fun m : ℕ => |(1 - v n) ^ m * g ((m : ℝ) / Real.sqrt n)| := by
    refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => ?_)
      ((summable_geometric_of_lt_one (r := 1 - v n) (by linarith) (by linarith)).mul_right C)
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith) _)]
    exact mul_le_mul_of_nonneg_left (hg _) (pow_nonneg (by linarith) _)
  have e1 : ∫ x in Set.Ici (0 : ℝ), G n x = ∫ x in Set.Ici (0 : ℝ),
      ∑' m : ℕ, (Set.Ico ((m : ℝ) / Real.sqrt n) (((m : ℝ) + 1) / Real.sqrt n)).indicator
        (fun _ => (1 - v n) ^ m * g ((m : ℝ) / Real.sqrt n)) x :=
    setIntegral_congr_fun measurableSet_Ici fun x hx =>
      (H_eq (Real.sqrt n) hq (fun m => (1 - v n) ^ m * g ((m : ℝ) / Real.sqrt n)) x hx).symm
  show ∫ x in Set.Ici (0 : ℝ), G n x = _
  rw [e1, step_integral (Real.sqrt n) hq _ hs]

open ProbabilityTheory

theorem gauss_int : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
  have := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only; congr 1; ring

theorem cdf_std_eq (β : ℝ) : cdf (gaussianReal 0 1) β =
    (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x in Set.Iic β, Real.exp (-(x ^ 2) / 2) := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  rw [← integral_const_mul]
  congr 1; ext x
  simp [gaussianPDFReal]

theorem pdf_std_eq (β : ℝ) : gaussianPDFReal 0 1 β =
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(β ^ 2) / 2) := by
  simp [gaussianPDFReal]

theorem cdf_std_pos (β : ℝ) : 0 < cdf (gaussianReal 0 1) β := by
  rw [cdf_eq_real, measureReal_def]
  apply ENNReal.toReal_pos
  · intro h
    have h2 := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
    rw [Real.volume_Iic] at h2
    exact ENNReal.top_ne_zero h2
  · exact measure_ne_top _ _

/-- the limit density (unnormalised). -/
noncomputable def fdens (β x : ℝ) : ℝ := Real.exp (-(β * x) - (min x 0) ^ 2 / 2)

theorem fdens_pos (β x : ℝ) : 0 < fdens β x := Real.exp_pos _

theorem fdens_cont (β : ℝ) : Continuous (fdens β) := by
  unfold fdens; fun_prop

theorem fdens_pos_side (β x : ℝ) (hx : 0 ≤ x) : fdens β x = Real.exp (-(β * x)) := by
  unfold fdens; rw [min_eq_right hx]; simp

theorem fdens_neg_side (β x : ℝ) (hx : x ≤ 0) :
    fdens β x = Real.exp (-(β * x) - x ^ 2 / 2) := by
  unfold fdens; rw [min_eq_left hx]

theorem gauss_shift_int (β : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-(β * x) - x ^ 2 / 2)) := by
  have h := (gauss_int.comp_add_right β).const_mul (Real.exp (β ^ 2 / 2))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [← Real.exp_add]; congr 1; ring

theorem fdens_integrable (β : ℝ) (hβ : 0 < β) : Integrable (fdens β) := by
  have hR : IntegrableOn (fdens β) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -β) (by linarith) 0
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only
    rw [fdens_pos_side β x (le_of_lt hx), neg_mul]
  have hL : IntegrableOn (fdens β) (Set.Iic 0) := by
    refine (gauss_shift_int β).integrableOn.congr_fun (fun x hx => ?_) measurableSet_Iic
    exact (fdens_neg_side β x hx).symm
  have := hL.union hR
  rw [Set.Iic_union_Ioi] at this
  exact integrableOn_univ.1 this

theorem fdens_Ioi (β : ℝ) (hβ : 0 < β) (x : ℝ) (hx : 0 ≤ x) :
    ∫ t in Set.Ioi x, fdens β t = Real.exp (-(β * x)) / β := by
  have : ∫ t in Set.Ioi x, fdens β t = ∫ t in Set.Ioi x, Real.exp ((-β) * t) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      rw [fdens_pos_side β t (le_trans hx (le_of_lt ht)), neg_mul])
  rw [this, integral_exp_mul_Ioi (by linarith) x, neg_mul, neg_div_neg_eq]

theorem fdens_Iic (β : ℝ) (a : ℝ) (ha : a ≤ 0) :
    ∫ t in Set.Iic a, fdens β t = Real.exp (β ^ 2 / 2) *
      (Real.sqrt (2 * Real.pi) * cdf (gaussianReal 0 1) (β + a)) := by
  have h1 : ∫ t in Set.Iic a, fdens β t =
      ∫ t in Set.Iic a, Real.exp (β ^ 2 / 2) * Real.exp (-((t + β) ^ 2) / 2) :=
    setIntegral_congr_fun measurableSet_Iic (fun t ht => by
      rw [fdens_neg_side β t (le_trans ht ha), ← Real.exp_add]; congr 1; ring)
  rw [h1, integral_const_mul]
  have hshift : ∫ t in Set.Iic a, Real.exp (-((t + β) ^ 2) / 2) =
      ∫ t in Set.Iic (a + β), Real.exp (-(t ^ 2) / 2) := by
    have := (measurePreserving_add_right volume β).setIntegral_preimage_emb
      (measurableEmbedding_addRight β) (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Set.Iic (a + β))
    rw [← this]
    congr 1
    ext x; simp
  rw [hshift, show β + a = a + β by ring, cdf_std_eq]
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  field_simp

noncomputable def Lc (β : ℝ) : ℝ := ∫ x, fdens β x

theorem Lc_eq (β : ℝ) (hβ : 0 < β) :
    Lc β = Real.exp (β ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * cdf (gaussianReal 0 1) β) + 1 / β := by
  have hint := fdens_integrable β hβ
  unfold Lc
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
    fdens_Iic β 0 le_rfl, fdens_Ioi β hβ 0 le_rfl]
  simp

theorem Lc_pos (β : ℝ) (hβ : 0 < β) : 0 < Lc β := by
  rw [Lc_eq β hβ]
  have := cdf_std_pos β
  positivity

noncomputable def nu0 (β : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (fdens β x / Lc β))

theorem nu0_real (β : ℝ) (hβ : 0 < β) (s : Set ℝ) (hs : MeasurableSet s) :
    (nu0 β).real s = (∫ x in s, fdens β x) / Lc β := by
  have hL := Lc_pos β hβ
  unfold nu0
  rw [measureReal_def, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal
      (((fdens_integrable β hβ).div_const (Lc β)).restrict)
      (ae_of_all _ fun x => (div_pos (fdens_pos β x) hL).le),
    ENNReal.toReal_ofReal (setIntegral_nonneg hs fun x _ => (div_pos (fdens_pos β x) hL).le),
    integral_div]

theorem nu0_prob (β : ℝ) (hβ : 0 < β) : IsProbabilityMeasure (nu0 β) := by
  refine ⟨?_⟩
  have h := nu0_real β hβ Set.univ MeasurableSet.univ
  rw [Measure.restrict_univ] at h
  have hL := Lc_pos β hβ
  rw [show (∫ x, fdens β x) = Lc β from rfl, div_self hL.ne'] at h
  exact (ENNReal.toReal_eq_one_iff _).1 h

theorem nu0_integral (β : ℝ) (hβ : 0 < β) (g : ℝ → ℝ) :
    ∫ x, g x ∂(nu0 β) = ∫ x, fdens β x / Lc β * g x := by
  have hL := Lc_pos β hβ
  unfold nu0
  rw [integral_withDensity_eq_integral_toReal_smul
    ((fdens_cont β).measurable.div_const _ |>.ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_pos (fdens_pos β x) hL).le]

theorem Asum_tendsto (v : ℕ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hv0 : ∀ n : ℕ, 1 ≤ n → 0 < v n ∧ v n < 1)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β))
    (g : ℝ → ℝ) (hgc : Continuous g) (C : ℝ) (hg : ∀ x, |g x| ≤ C) :
    Tendsto (fun n : ℕ => Asum n (v n) g) atTop (𝓝 (∫ x, fdens β x * g x)) := by
  have hl := left_core v β hβ hv0 hc g hgc C hg
  have hr := right_core v β hβ hv0 hc g hgc C hg
  have hint : Integrable (fun x => fdens β x * g x) :=
    (fdens_integrable β hβ).mul_bdd hgc.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hg x)
  have e1 : ∫ x, fdens β x * g x = (∫ y in Set.Ioi (0 : ℝ), Real.exp (β * y - y ^ 2 / 2) * g (-y)) +
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) * g x := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
    congr 1
    · have := integral_comp_neg_Ioi (0 : ℝ) (fun x => fdens β x * g x)
      rw [neg_zero] at this
      rw [← this]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
      have hy : 0 < y := hy
      rw [fdens_neg_side β (-y) (by linarith)]
      congr 2
      ring
    · refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
      have hy : 0 < y := hy
      rw [fdens_pos_side β y hy.le]
  rw [e1]
  have := (hl.add hr)
  refine this.congr' ?_
  filter_upwards with n
  unfold Asum
  ring

theorem scaled_ratio (lam μ : ℝ) (n : ℕ) (hn : 1 ≤ n) (hμ : 0 < μ) (hlam : 0 < lam)
    (hlt : lam < n * μ) (v : ℝ) (hv : 1 - v = lam / (n * μ)) (p : ℕ → ℝ)
    (h : IsSteadyState (fun _ => lam) (mmcDeath μ n) p) (g : ℝ → ℝ) (C : ℝ)
    (hg : ∀ x, |g x| ≤ C) :
    scaledExpect p n g = Asum n v g / Asum n v (fun _ => 1) := by
  have h1 := scaled_one lam μ n hn hμ hlam hlt v hv p h
  have h2 := scaled_eq lam μ n hn hμ hlam hlt v hv p h g C hg
  have hne : Asum n v (fun _ => 1) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
  rw [h2, eq_div_iff hne]
  calc p n * Real.sqrt n * Asum n v g * Asum n v (fun _ => 1)
      = (p n * Real.sqrt n * Asum n v (fun _ => 1)) * Asum n v g := by ring
    _ = Asum n v g := by rw [h1, one_mul]

theorem main_thm (μ : ℝ) (hμ : 0 < μ) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (p : ℕ → ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → IsSteadyState (fun _ => lam n) (mmcDeath μ n) (p n))
    (β : ℝ) (hβ : 0 < β)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β)) :
    ∃ ν : ProbabilityMeasure ℝ,
      (ν : Measure ℝ).real (Set.Ici 0) = halfinWhittAlpha β ∧
      (∀ x : ℝ, 0 ≤ x →
        (ν : Measure ℝ).real (Set.Ioi x) / (ν : Measure ℝ).real (Set.Ici 0) =
          Real.exp (-(x * β))) ∧
      (∀ x : ℝ, x ≤ 0 →
        (ν : Measure ℝ).real (Set.Iic x) / (ν : Measure ℝ).real (Set.Iic 0) =
          ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (β + x) /
            ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) β) ∧
      ∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => scaledExpect (p n) n g) atTop (𝓝 (∫ x, g x ∂(ν : Measure ℝ))) := by
  have := nu0_prob β hβ
  have hL := Lc_pos β hβ
  have hΦ := cdf_std_pos β
  refine ⟨⟨nu0 β, this⟩, ?_, ?_, ?_, ?_⟩
  · -- the mass of [0, ∞)
    show (nu0 β).real (Set.Ici 0) = _
    rw [nu0_real β hβ _ measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      fdens_Ioi β hβ 0 le_rfl, Lc_eq β hβ]
    unfold halfinWhittAlpha
    rw [pdf_std_eq]
    have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hE : 0 < Real.exp (β ^ 2 / 2) := Real.exp_pos _
    have hE2 : Real.exp (-(β ^ 2) / 2) = (Real.exp (β ^ 2 / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hE2]
    simp only [mul_zero, neg_zero, Real.exp_zero]
    field_simp
    try ring
  · intro x hx
    show (nu0 β).real (Set.Ioi x) / (nu0 β).real (Set.Ici 0) = _
    rw [nu0_real β hβ _ measurableSet_Ioi, nu0_real β hβ _ measurableSet_Ici,
      integral_Ici_eq_integral_Ioi, fdens_Ioi β hβ x hx, fdens_Ioi β hβ 0 le_rfl]
    simp only [mul_zero, neg_zero, Real.exp_zero]
    field_simp
    try rw [mul_comm x β]
  · intro x hx
    show (nu0 β).real (Set.Iic x) / (nu0 β).real (Set.Iic 0) = _
    rw [nu0_real β hβ _ measurableSet_Iic, nu0_real β hβ _ measurableSet_Iic,
      fdens_Iic β x hx, fdens_Iic β 0 le_rfl]
    have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hE : 0 < Real.exp (β ^ 2 / 2) := Real.exp_pos _
    rw [add_zero]
    field_simp
  · intro g
    show Tendsto _ _ (𝓝 (∫ x, g x ∂(nu0 β)))
    rw [nu0_integral β hβ]
    set v : ℕ → ℝ := fun n => 1 - lam n / (n * μ) with hv
    have hv0 : ∀ n : ℕ, 1 ≤ n → 0 < v n ∧ v n < 1 := by
      intro n hn
      obtain ⟨h1, h2⟩ := hlam n hn
      have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hpos : 0 < lam n / (n * μ) := by positivity
      have hlt : lam n / (n * μ) < 1 := by rw [div_lt_one (by positivity)]; exact h2
      constructor <;> simp only [hv] <;> linarith
    have hC : ∀ x, |g x| ≤ ‖g‖ := fun x => by
      rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm x
    have h1 := Asum_tendsto v β hβ hv0 hβlim g g.continuous ‖g‖ hC
    have h2 := Asum_tendsto v β hβ hv0 hβlim (fun _ => 1) continuous_const 1 (fun x => by simp)
    have h3 := h1.div h2 (by
      simp only [mul_one]; exact hL.ne')
    have e : (∫ x, fdens β x / Lc β * g x) =
        (∫ x, fdens β x * g x) / ∫ x, fdens β x * (fun _ => (1 : ℝ)) x := by
      simp only [mul_one]
      change _ = _ / Lc β
      rw [← integral_div]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only
      ring
    rw [e]
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨h1', h2'⟩ := hlam n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact (scaled_ratio (lam n) μ n hn hμ h1' h2' (v n) (by simp only [hv]; ring) (p n) (hp n hn)
      g ‖g‖ hC).symm

end HW81c

open Filter Topology MeasureTheory QueueingFundamentals.BirthDeath HalfinWhitt81.Stationary in
theorem solution
    (μ : ℝ) (hμ : 0 < μ) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hlam_top : Tendsto lam atTop atTop)
    (p : ℕ → ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → IsSteadyState (fun _ => lam n) (mmcDeath μ n) (p n))
    (β : ℝ) (hβ : 0 < β)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β)) :
    ∃ ν : ProbabilityMeasure ℝ,
      (ν : Measure ℝ).real (Set.Ici 0) = halfinWhittAlpha β ∧
      (∀ x : ℝ, 0 ≤ x →
        (ν : Measure ℝ).real (Set.Ioi x) / (ν : Measure ℝ).real (Set.Ici 0) =
          Real.exp (-(x * β))) ∧
      (∀ x : ℝ, x ≤ 0 →
        (ν : Measure ℝ).real (Set.Iic x) / (ν : Measure ℝ).real (Set.Iic 0) =
          ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (β + x) /
            ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) β) ∧
      ∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => scaledExpect (p n) n g) atTop (𝓝 (∫ x, g x ∂(ν : Measure ℝ))) := by
  exact HW81c.main_thm μ hμ lam hlam p hp β hβ hβlim
