-- Prove2me | solution 1 for KallenbergLP.SemiMarkov.value_smallest_superharmonic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:23:17.834196+00:00
-- url     : https://prove2.me/submissions/4365cbd1-6ae0-4915-9e76-790b6511bc4f

import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Discounted



namespace KallenbergLP.SemiMarkov

open MeasureTheory Filter
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {S U : Type*} [Fintype S] [Nonempty S] [Fintype U] [DecidableEq S] [DecidableEq U]

lemma smv_hd_eq (M : Discounted S U) (t : ℝ) :
    holdingDiscount M.rate t =
      if t < 0 then 0 else (1 - Real.exp (-(M.rate * t))) / M.rate := by
  unfold holdingDiscount
  have hr := M.rate_pos
  split_ifs with ht
  · rw [Set.Icc_eq_empty (by linarith)]; simp
  · push_neg at ht
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u => -Real.exp (-(M.rate * u)) / M.rate)]
    · simp only [mul_zero, neg_zero, Real.exp_zero]
      field_simp
      ring
    · intro x _
      have := ((((hasDerivAt_id x).const_mul M.rate).neg).exp.neg).div_const M.rate
      refine this.congr_deriv ?_
      simp only [id, Pi.neg_apply]
      field_simp
    · exact (by fun_prop : Continuous fun u => Real.exp (-(M.rate * u))).intervalIntegrable _ _

lemma smv_hd_meas (M : Discounted S U) : Measurable (fun t => holdingDiscount M.rate t) := by
  have : (fun t => holdingDiscount M.rate t) =
      fun t => if t < 0 then 0 else (1 - Real.exp (-(M.rate * t))) / M.rate := by
    funext t; exact smv_hd_eq M t
  rw [this]
  exact Measurable.ite measurableSet_Iio measurable_const (by fun_prop)

lemma smv_hd_bound (M : Discounted S U) (t : ℝ) : |holdingDiscount M.rate t| ≤ 1 / M.rate := by
  rw [smv_hd_eq]
  have hr := M.rate_pos
  split_ifs with ht
  · simp; positivity
  · have h1 := Real.exp_pos (-(M.rate * t))
    have h2 : Real.exp (-(M.rate * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [abs_of_nonneg (by apply div_nonneg <;> linarith)]
    exact div_le_div_of_nonneg_right (by linarith) hr.le

lemma smv_ae_nonneg (M : Discounted S U) {i : S} {a : U} {j : S} (ha : a ∈ M.model.actions i) :
    ∀ᵐ t ∂M.model.F i a j, 0 ≤ t := by
  rw [ae_iff]
  convert M.model.F_nonneg i a j ha using 2
  ext t; simp

lemma smv_exp_int (M : Discounted S U) {i : S} {a : U} {j : S} (ha : a ∈ M.model.actions i) :
    Integrable (fun t => Real.exp (-(M.rate * t))) (M.model.F i a j) := by
  haveI := M.model.F_prob i a j ha
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [smv_ae_nonneg M (j := j) ha] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [M.rate_pos])

lemma smv_er_int (M : Discounted S U) {i : S} {a : U} {j : S} (ha : a ∈ M.model.actions i) :
    Integrable (fun t => epochReturn M i a t) (M.model.F i a j) := by
  haveI := M.model.F_prob i a j ha
  have hd : Integrable (fun t => holdingDiscount M.rate t) (M.model.F i a j) :=
    Integrable.of_bound (smv_hd_meas M).aestronglyMeasurable (1 / M.rate)
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact smv_hd_bound M t)
  exact (integrable_const _).add (hd.const_mul _)

lemma smv_step (M : Discounted S U) {i : S} {a : U} (ha : a ∈ M.model.actions i) (j : S) (c : ℝ) :
    ∫ t, (epochReturn M i a t + Real.exp (-(M.rate * t)) * c) ∂M.model.F i a j
      = ∫ t, epochReturn M i a t ∂M.model.F i a j + c * laplace M.model M.rate i a j := by
  rw [integral_add (smv_er_int M ha) ((smv_exp_int M ha).mul_const c), integral_mul_const]
  unfold laplace; ring

lemma smv_fR_succ (M : Discounted S U) (R : Policy M) (n : ℕ) (h : List (S × U)) (i : S) :
    finiteReward M R (n + 1) h i =
      ∑ a ∈ M.model.actions i, R.choose h i a *
        (rStar M i a + ∑ j, pStar M i a j * finiteReward M R n (h ++ [(i, a)]) j) := by
  rw [finiteReward]
  refine Finset.sum_congr rfl fun a ha => ?_
  congr 1
  simp_rw [smv_step M ha]
  simp only [rStar, pStar, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma smv_laplace_nonneg (M : Discounted S U) (i : S) (a : U) (j : S) :
    0 ≤ laplace M.model M.rate i a j :=
  integral_nonneg fun t => (Real.exp_pos _).le

lemma smv_pStar_nonneg (M : Discounted S U) {i : S} {a : U} (ha : a ∈ M.model.actions i) (j : S) :
    0 ≤ pStar M i a j :=
  mul_nonneg (M.model.p_nonneg i a j ha) (smv_laplace_nonneg M i a j)

lemma smv_row_lt (M : Discounted S U) {i : S} {a : U} (ha : a ∈ M.model.actions i) :
    ∑ j, pStar M i a j < 1 := by
  set L := Finset.univ.sup' Finset.univ_nonempty (fun j => laplace M.model M.rate i a j)
  have hL : L < 1 := Finset.sup'_lt_iff _ |>.mpr fun j _ => M.laplace_lt_one i a j ha
  calc ∑ j, pStar M i a j ≤ ∑ j, M.model.p i a j * L := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j => laplace M.model M.rate i a j)
          (Finset.mem_univ j)) (M.model.p_nonneg i a j ha)
    _ = L := by rw [← Finset.sum_mul, M.model.p_sum i a ha, one_mul]
    _ < 1 := hL

lemma smv_exists_rho (M : Discounted S U) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ i, ∀ a ∈ M.model.actions i, ∑ j, pStar M i a j ≤ ρ := by
  refine ⟨max 0 (Finset.univ.sup' Finset.univ_nonempty (fun i =>
    (M.model.actions i).sup' (M.model.actions_nonempty i) (fun a => ∑ j, pStar M i a j))),
    le_max_left _ _, ?_, ?_⟩
  · refine max_lt zero_lt_one ?_
    refine Finset.sup'_lt_iff _ |>.mpr fun i _ => ?_
    exact Finset.sup'_lt_iff _ |>.mpr fun a ha => smv_row_lt M ha
  · intro i a ha
    refine le_max_of_le_right ?_
    refine Finset.le_sup'_of_le _ (Finset.mem_univ i) ?_
    exact Finset.le_sup' (fun a => ∑ j, pStar M i a j) ha

lemma smv_swap (A : S → Finset U) (B : Finset U) (c : S → U → ℝ) (g : U → ℝ) (w : U → S → ℝ)
    (D : U → S → S → U → ℝ) :
    ∑ j, ∑ a ∈ A j, c j a * ∑ b ∈ B, g b * ∑ k, w b k * D b k j a =
      ∑ b ∈ B, g b * ∑ k, w b k * ∑ j, ∑ a ∈ A j, c j a * D b k j a := by
  simp only [Finset.mul_sum]
  calc ∑ j, ∑ a ∈ A j, ∑ b ∈ B, ∑ k, c j a * (g b * (w b k * D b k j a))
      = ∑ j, ∑ b ∈ B, ∑ a ∈ A j, ∑ k, c j a * (g b * (w b k * D b k j a)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b ∈ B, ∑ j, ∑ a ∈ A j, ∑ k, c j a * (g b * (w b k * D b k j a)) := Finset.sum_comm
    _ = ∑ b ∈ B, ∑ j, ∑ k, ∑ a ∈ A j, c j a * (g b * (w b k * D b k j a)) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b ∈ B, ∑ k, ∑ j, ∑ a ∈ A j, c j a * (g b * (w b k * D b k j a)) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
        ring

lemma smv_fR_eq_sum (M : Discounted S U) (R : Policy M) (N : ℕ) : ∀ h i,
    finiteReward M R N h i = ∑ n ∈ Finset.range N, ∑ j, ∑ a ∈ M.model.actions j,
      rStar M j a * discountedVisit M R n h i j a := by
  induction N with
  | zero => intro h i; simp [finiteReward]
  | succ N ih =>
    intro h i
    rw [smv_fR_succ, Finset.sum_range_succ']
    simp only [ih, discountedVisit]
    have h0 : ∑ j, ∑ a ∈ M.model.actions j,
        rStar M j a * (if i = j then R.choose h i a else 0) =
        ∑ a ∈ M.model.actions i, rStar M i a * R.choose h i a := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    rw [h0]
    simp only [smv_swap]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · simp only [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact Finset.sum_comm
    · refine Finset.sum_congr rfl fun a _ => ?_; ring

lemma smv_dV_nonneg (M : Discounted S U) (R : Policy M) (n : ℕ) : ∀ h i j,
    ∀ a ∈ M.model.actions j, 0 ≤ discountedVisit M R n h i j a := by
  induction n with
  | zero =>
    intro h i j a ha
    simp only [discountedVisit]
    split_ifs with hij
    · subst hij; exact R.choose_nonneg h i a ha
    · exact le_rfl
  | succ n ih =>
    intro h i j a ha
    simp only [discountedVisit]
    refine Finset.sum_nonneg fun b hb => mul_nonneg (R.choose_nonneg h i b hb) ?_
    exact Finset.sum_nonneg fun k _ => mul_nonneg (smv_pStar_nonneg M hb k) (ih _ _ _ a ha)

lemma smv_dV_mass (M : Discounted S U) (R : Policy M) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (hρ : ∀ i, ∀ a ∈ M.model.actions i, ∑ j, pStar M i a j ≤ ρ) (n : ℕ) : ∀ h i,
    ∑ j, ∑ a ∈ M.model.actions j, discountedVisit M R n h i j a ≤ ρ ^ n := by
  induction n with
  | zero =>
    intro h i
    simp only [discountedVisit, pow_zero]
    rw [Finset.sum_eq_single i]
    · simp [R.choose_sum h i]
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  | succ n ih =>
    intro h i
    have := smv_swap M.model.actions (M.model.actions i) (fun _ _ => (1:ℝ)) (R.choose h i)
      (pStar M i) (fun b k j a => discountedVisit M R n (h ++ [(i, b)]) k j a)
    simp only [one_mul] at this
    simp only [discountedVisit]
    rw [this]
    calc ∑ b ∈ M.model.actions i, R.choose h i b * ∑ k, pStar M i b k *
          ∑ j, ∑ a ∈ M.model.actions j, discountedVisit M R n (h ++ [(i, b)]) k j a
        ≤ ∑ b ∈ M.model.actions i, R.choose h i b * ∑ k, pStar M i b k * ρ ^ n := by
          refine Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (R.choose_nonneg h i b hb)
          exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ih _ _) (smv_pStar_nonneg M hb k)
      _ ≤ ∑ b ∈ M.model.actions i, R.choose h i b * ρ ^ (n + 1) := by
          refine Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (R.choose_nonneg h i b hb)
          rw [← Finset.sum_mul, pow_succ, mul_comm (ρ ^ n)]
          exact mul_le_mul_of_nonneg_right (hρ i b hb) (pow_nonneg h0 n)
      _ = ρ ^ (n + 1) := by rw [← Finset.sum_mul, R.choose_sum, one_mul]

lemma smv_hasSum (M : Discounted S U) (R : Policy M) (i : S) :
    HasSum (fun n => ∑ j, ∑ a ∈ M.model.actions j, rStar M j a * discountedVisit M R n [] i j a)
      (∑' n : ℕ, ∑ j : S, ∑ a ∈ M.model.actions j, rStar M j a * discountedVisit M R n [] i j a) := by
  obtain ⟨ρ, h0, h1, hρ⟩ := smv_exists_rho M
  set K := ∑ j, ∑ a ∈ M.model.actions j, |rStar M j a|
  have hK : ∀ j, ∀ a ∈ M.model.actions j, |rStar M j a| ≤ K := by
    intro j a ha
    calc |rStar M j a| ≤ ∑ a ∈ M.model.actions j, |rStar M j a| :=
          Finset.single_le_sum (f := fun a => |rStar M j a|) (fun _ _ => abs_nonneg _) ha
      _ ≤ K := Finset.single_le_sum (f := fun j => ∑ a ∈ M.model.actions j, |rStar M j a|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hb : ∀ n, ‖∑ j, ∑ a ∈ M.model.actions j, rStar M j a * discountedVisit M R n [] i j a‖
      ≤ K * ρ ^ n := by
    intro n
    rw [Real.norm_eq_abs]
    calc _ ≤ ∑ j, ∑ a ∈ M.model.actions j, |rStar M j a * discountedVisit M R n [] i j a| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ j, ∑ a ∈ M.model.actions j, K * discountedVisit M R n [] i j a := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a ha => ?_
          rw [abs_mul, abs_of_nonneg (smv_dV_nonneg M R n [] i j a ha)]
          exact mul_le_mul_of_nonneg_right (hK j a ha) (smv_dV_nonneg M R n [] i j a ha)
      _ = K * ∑ j, ∑ a ∈ M.model.actions j, discountedVisit M R n [] i j a := by
          simp only [Finset.mul_sum]
      _ ≤ K * ρ ^ n := mul_le_mul_of_nonneg_left (smv_dV_mass M R h0 hρ n [] i)
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
  exact (Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_left K) hb).hasSum

lemma smv_tendsto (M : Discounted S U) (R : Policy M) (i : S) :
    Tendsto (fun N => finiteReward M R N [] i) atTop
      (nhds (∑' n : ℕ, ∑ j : S, ∑ a ∈ M.model.actions j,
        rStar M j a * discountedVisit M R n [] i j a)) := by
  have := (smv_hasSum M R i).tendsto_sum_nat
  simpa only [← smv_fR_eq_sum] using this

theorem roi_core (M : Discounted S U) (R : Policy M) (i : S) :
    policyValue M R i =
      ∑' n : ℕ, ∑ j : S, ∑ a ∈ M.model.actions j,
        rStar M j a * discountedVisit M R n [] i j a :=
  (smv_tendsto M R i).limUnder_eq

lemma smv_tendsto_pv (M : Discounted S U) (R : Policy M) (i : S) :
    Tendsto (fun N => finiteReward M R N [] i) atTop (nhds (policyValue M R i)) := by
  rw [roi_core]; exact smv_tendsto M R i

lemma smv_fR_le (M : Discounted S U) (R : Policy M) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (hρ : ∀ i, ∀ a ∈ M.model.actions i, ∑ j, pStar M i a j ≤ ρ) (w : S → ℝ)
    (hw : Superharmonic M w) (n : ℕ) : ∀ h i,
    finiteReward M R n h i ≤ w i + ρ ^ n * ∑ j, |w j| := by
  have hK : ∀ i, |w i| ≤ ∑ j, |w j| := fun i =>
    Finset.single_le_sum (f := fun j => |w j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hK0 : 0 ≤ ∑ j, |w j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  induction n with
  | zero =>
    intro h i
    simp only [finiteReward, pow_zero, one_mul]
    linarith [neg_abs_le (w i), hK i]
  | succ n ih =>
    intro h i
    rw [smv_fR_succ]
    calc _ ≤ ∑ a ∈ M.model.actions i, R.choose h i a * (w i + ρ ^ (n + 1) * ∑ j, |w j|) := by
          refine Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ (R.choose_nonneg h i a ha)
          have h1 : ∑ j, pStar M i a j * finiteReward M R n (h ++ [(i, a)]) j ≤
              ∑ j, pStar M i a j * (w j + ρ ^ n * ∑ j, |w j|) :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih _ _) (smv_pStar_nonneg M ha j)
          have h2 : ∑ j, pStar M i a j * (w j + ρ ^ n * ∑ j, |w j|) =
              ∑ j, pStar M i a j * w j + (∑ j, pStar M i a j) * (ρ ^ n * ∑ j, |w j|) := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
          have h3 : (∑ j, pStar M i a j) * (ρ ^ n * ∑ j, |w j|) ≤ ρ * (ρ ^ n * ∑ j, |w j|) :=
            mul_le_mul_of_nonneg_right (hρ i a ha) (mul_nonneg (pow_nonneg h0 n) hK0)
          have h4 := hw i a ha
          rw [pow_succ]
          nlinarith
      _ = _ := by rw [← Finset.sum_mul, R.choose_sum, one_mul]

lemma smv_pv_le (M : Discounted S U) (R : Policy M) (w : S → ℝ) (hw : Superharmonic M w) (i : S) :
    policyValue M R i ≤ w i := by
  obtain ⟨ρ, h0, h1, hρ⟩ := smv_exists_rho M
  have ht : Tendsto (fun n => w i + ρ ^ n * ∑ j, |w j|) atTop (nhds (w i + 0 * ∑ j, |w j|)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const _)
  rw [zero_mul, add_zero] at ht
  exact le_of_tendsto_of_tendsto' (smv_tendsto_pv M R i) ht
    (fun n => smv_fR_le M R h0 hρ w hw n [] i)

lemma smv_pure_fR (M : Discounted S U) (f : S → U) (hf : ∀ i, f i ∈ M.model.actions i)
    {ρ : ℝ} (h0 : 0 ≤ ρ)
    (hρ : ∀ i, ∀ a ∈ M.model.actions i, ∑ j, pStar M i a j ≤ ρ) (v : S → ℝ)
    (hv : ∀ i, rStar M i (f i) + ∑ j, pStar M i (f i) j * v j = v i) (n : ℕ) : ∀ h i,
    |finiteReward M (purePolicy M f hf) n h i - v i| ≤ ρ ^ n * ∑ j, |v j| := by
  have hK : ∀ i, |v i| ≤ ∑ j, |v j| := fun i =>
    Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hK0 : 0 ≤ ∑ j, |v j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  induction n with
  | zero =>
    intro h i
    simp only [finiteReward, pow_zero, one_mul, zero_sub, abs_neg]
    exact hK i
  | succ n ih =>
    intro h i
    rw [smv_fR_succ]
    have e : ∑ a ∈ M.model.actions i, (purePolicy M f hf).choose h i a *
        (rStar M i a + ∑ j, pStar M i a j * finiteReward M (purePolicy M f hf) n (h ++ [(i, a)]) j)
        = rStar M i (f i) + ∑ j, pStar M i (f i) j *
            finiteReward M (purePolicy M f hf) n (h ++ [(i, f i)]) j := by
      simp [purePolicy, ite_mul, Finset.sum_ite_eq', hf i]
    rw [e]
    conv_lhs => rw [← hv i]
    have e2 : rStar M i (f i) + ∑ j, pStar M i (f i) j *
            finiteReward M (purePolicy M f hf) n (h ++ [(i, f i)]) j -
          (rStar M i (f i) + ∑ j, pStar M i (f i) j * v j) =
        ∑ j, pStar M i (f i) j * (finiteReward M (purePolicy M f hf) n (h ++ [(i, f i)]) j - v j) := by
      rw [← sub_sub, add_sub_cancel_left, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    calc _ ≤ ∑ j, |pStar M i (f i) j *
          (finiteReward M (purePolicy M f hf) n (h ++ [(i, f i)]) j - v j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, pStar M i (f i) j * (ρ ^ n * ∑ j, |v j|) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (smv_pStar_nonneg M (hf i) j)]
          exact mul_le_mul_of_nonneg_left (ih _ _) (smv_pStar_nonneg M (hf i) j)
      _ = (∑ j, pStar M i (f i) j) * (ρ ^ n * ∑ j, |v j|) := by rw [Finset.sum_mul]
      _ ≤ ρ * (ρ ^ n * ∑ j, |v j|) :=
          mul_le_mul_of_nonneg_right (hρ i (f i) (hf i)) (mul_nonneg (pow_nonneg h0 n) hK0)
      _ = _ := by ring

lemma smv_pure_pv (M : Discounted S U) (f : S → U) (hf : ∀ i, f i ∈ M.model.actions i)
    (v : S → ℝ) (hv : ∀ i, rStar M i (f i) + ∑ j, pStar M i (f i) j * v j = v i) (i : S) :
    policyValue M (purePolicy M f hf) i = v i := by
  obtain ⟨ρ, h0, h1, hρ⟩ := smv_exists_rho M
  have ht : Tendsto (fun n => finiteReward M (purePolicy M f hf) n [] i) atTop (nhds (v i)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hz : Tendsto (fun n => ρ ^ n * ∑ j, |v j|) atTop (nhds (0 * ∑ j, |v j|)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const _
    rw [zero_mul] at hz
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hz
    rw [Real.norm_eq_abs]; exact smv_pure_fR M f hf h0 hρ v hv n [] i
  exact ht.limUnder_eq

theorem bso_core (M : Discounted S U) (f : S → U)
    (hf : ∀ i, f i ∈ M.model.actions i)
    (hbellman : ∀ i, rStar M i (f i) +
      ∑ j, pStar M i (f i) j * value M j = value M i) :
    ∀ i, policyValue M (purePolicy M f hf) i = value M i :=
  smv_pure_pv M f hf (value M) hbellman

noncomputable def smvBop (M : Discounted S U) (v : S → ℝ) (i : S) : ℝ :=
  (M.model.actions i).sup' (M.model.actions_nonempty i)
    (fun a => rStar M i a + ∑ j, pStar M i a j * v j)

lemma smv_bop_le (M : Discounted S U) {ρ : ℝ}
    (hρ : ∀ i, ∀ a ∈ M.model.actions i, ∑ j, pStar M i a j ≤ ρ)
    (v w : S → ℝ) (d : ℝ) (hd0 : 0 ≤ d) (hd : ∀ j, |v j - w j| ≤ d) (i : S) :
    smvBop M v i ≤ smvBop M w i + ρ * d := by
  unfold smvBop
  refine Finset.sup'_le _ _ fun a ha => ?_
  have h1 : ∑ j, pStar M i a j * v j ≤ ∑ j, pStar M i a j * w j + (∑ j, pStar M i a j) * d := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have := (abs_le.mp (hd j)).2
    nlinarith [smv_pStar_nonneg M ha j]
  have h2 : (∑ j, pStar M i a j) * d ≤ ρ * d := mul_le_mul_of_nonneg_right (hρ i a ha) hd0
  have h3 := Finset.le_sup' (fun a => rStar M i a + ∑ j, pStar M i a j * w j) ha
  linarith

lemma smv_exists_fixed (M : Discounted S U) : ∃ v : S → ℝ, smvBop M v = v := by
  obtain ⟨ρ, h0, h1, hρ⟩ := smv_exists_rho M
  have hc : ContractingWith ⟨ρ, h0⟩ (smvBop M) := by
    refine ⟨by exact_mod_cast h1, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
    refine (dist_pi_le_iff (mul_nonneg h0 dist_nonneg)).mpr fun i => ?_
    have hd : ∀ j, |v j - w j| ≤ dist v w := fun j => by
      rw [← Real.dist_eq]; exact dist_le_pi_dist v w j
    have hd' : ∀ j, |w j - v j| ≤ dist v w := fun j => by
      rw [abs_sub_comm]; exact hd j
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor
    · linarith [smv_bop_le M hρ v w _ dist_nonneg hd i]
    · linarith [smv_bop_le M hρ w v _ dist_nonneg hd' i]
  exact ⟨_, hc.fixedPoint_isFixedPt⟩

lemma smv_value_char (M : Discounted S U) :
    Superharmonic M (value M) ∧
      (∀ i, ∃ a ∈ M.model.actions i,
        rStar M i a + ∑ j, pStar M i a j * value M j = value M i) := by
  obtain ⟨v, hv⟩ := smv_exists_fixed M
  have hsh : Superharmonic M v := by
    intro i a ha
    have := Finset.le_sup' (fun a => rStar M i a + ∑ j, pStar M i a j * v j) ha
    have e := congrFun hv i
    unfold smvBop at e
    linarith
  have hsel : ∀ i, ∃ a ∈ M.model.actions i, rStar M i a + ∑ j, pStar M i a j * v j = v i := by
    intro i
    obtain ⟨a, ha, e⟩ := Finset.exists_mem_eq_sup' (M.model.actions_nonempty i)
      (fun a => rStar M i a + ∑ j, pStar M i a j * v j)
    refine ⟨a, ha, ?_⟩
    have e2 := congrFun hv i
    unfold smvBop at e2
    rw [← e2, e]
  choose f hf hfe using hsel
  have hpv := smv_pure_pv M f hf v hfe
  have hval : value M = v := by
    funext i
    refine IsGreatest.csSup_eq ⟨⟨purePolicy M f hf, hpv i⟩, ?_⟩
    rintro _ ⟨R, rfl⟩
    exact smv_pv_le M R v hsh i
  rw [hval]
  exact ⟨hsh, fun i => ⟨f i, hf i, hfe i⟩⟩

theorem vss_core (M : Discounted S U) :
    Superharmonic M (value M) ∧
      ∀ w : S → ℝ, Superharmonic M w → ∀ i : S, value M i ≤ w i := by
  refine ⟨(smv_value_char M).1, fun w hw i => ?_⟩
  obtain ⟨_, hsel⟩ := smv_value_char M
  choose f hf hfe using hsel
  rw [← smv_pure_pv M f hf (value M) hfe i]
  exact smv_pv_le M _ w hw i

end KallenbergLP.SemiMarkov

open KallenbergLP.SemiMarkov
variable {S U : Type*} [Fintype S] [Fintype U] [Nonempty S] [DecidableEq S] [DecidableEq U]

theorem solution (M : Discounted S U) :
    Superharmonic M (value M) ∧
      ∀ w : S → ℝ, Superharmonic M w → ∀ i : S, value M i ≤ w i := by
  exact vss_core M
