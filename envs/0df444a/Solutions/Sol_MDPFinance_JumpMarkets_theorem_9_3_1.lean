-- Prove2me | solution 1 for MDPFinance.JumpMarkets.theorem_9_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T06:02:59.979205+00:00
-- url     : https://prove2.me/submissions/fa2d62b5-42f5-4971-bced-67775725de5b

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket
import Theorems.Thm_MDPFinance_JumpMarkets_theorem_9_3_4
import Theorems.Thm_MDPFinance_JumpMarkets_proposition_9_3_2

open MeasureTheory ProbabilityTheory Filter Topology MDPFinance.JumpMarkets
open scoped ENNReal NNReal

namespace SolTheorem931

variable {d : ℕ}

lemma isBoundingFunction_max_zero (M : JumpMarket d) (bf : ℝ × ℝ → ℝ) (alpha : ℝ)
    (hb : M.IsBoundingFunction bf alpha) :
    M.IsBoundingFunction bf (max 0 alpha) := by
  refine ⟨hb.1, hb.2.1, fun p hp a => (hb.2.2 p hp a).trans ?_⟩
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right 0 alpha) (hb.1 p hp).le)

lemma ucal_coord_le_one {u : Fin d → ℝ} (hu : u ∈ Ucal d) (i : Fin d) :
    |u i| ≤ 1 := by
  rw [abs_of_nonneg (hu.1 i)]
  have hle : u i ≤ ∑ j, u j :=
    Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)
  linarith [hu.2]

lemma lintegral_Ioi_lam_exp (lam : ℝ) (hlam : 0 < lam) (t : ℝ) :
    ∫⁻ s in Set.Ioi t, ENNReal.ofReal (lam * Real.exp (-lam * s)) =
      ENNReal.ofReal (Real.exp (-lam * t)) := by
  have hcont : ContinuousWithinAt (fun x => -Real.exp (-lam * x)) (Set.Ici t) t :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).neg.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi t,
      HasDerivAt (fun x => -Real.exp (-lam * x)) (lam * Real.exp (-lam * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => -lam * x) (-lam) x := by
      simpa using (hasDerivAt_id x).const_mul (-lam)
    exact (h1.exp.neg).congr_deriv (by ring)
  have hnonneg : ∀ x ∈ Set.Ioi t, 0 ≤ lam * Real.exp (-lam * x) :=
    fun x _ => mul_nonneg hlam.le (Real.exp_pos _).le
  have htendsto : Tendsto (fun x => -Real.exp (-lam * x)) atTop (𝓝 0) := by
    have h_lin : Tendsto (fun x : ℝ => -lam * x) atTop atBot := by
      simp_rw [neg_mul]
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hlam)
    simpa using (Real.tendsto_exp_atBot.comp h_lin).neg
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg htendsto
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg htendsto
  have h_ae : 0 ≤ᵐ[volume.restrict (Set.Ioi t)] (fun x => lam * Real.exp (-lam * x)) :=
    Filter.Eventually.of_forall fun x => mul_nonneg hlam.le (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint h_ae, hval, sub_neg_eq_add, zero_add]

lemma measurable_phi_control (M : JumpMarket d) (t : ℝ) :
    Measurable (fun a : Control d =>
      ∫ s in Set.Ioc (0 : ℝ) t, (M.rho + ∑ i, a.val s i * (M.mu i - M.rho))) := by
  have hIoc : MeasurableSet (Set.Ioc (0 : ℝ) t) := measurableSet_Ioc
  by_cases ht : 0 < t
  · let g : (Fin d → ℝ) → ℝ := fun u => M.rho + ∑ i, u i * (M.mu i - M.rho)
    let w : ℝ × Ucal d → ℝ := fun su =>
      (Set.Ioc (0 : ℝ) t).indicator (fun _ => g su.2.1) su.1
    have hg_cont : Continuous (fun u : Ucal d => g u.1) := by
      refine continuous_const.add (continuous_finsetSum _ fun i _ => ?_)
      exact ((continuous_apply i).comp continuous_subtype_val).mul continuous_const
    let C : ℝ := |M.rho| + ∑ i : Fin d, |M.mu i - M.rho|
    have hg_bound : ∀ u : Ucal d, |g u.1| ≤ C := by
      intro u
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (ucal_coord_le_one u.2 i)
    have hw : IsCaratheodory w := by
      refine ⟨fun s => ?_, fun u => ?_, ?_⟩
      · by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
        · simpa [w, hs] using hg_cont
        · simpa [w, hs] using continuous_const
      · exact (measurable_const : Measurable (fun _ : ℝ => g u.1)).indicator hIoc
      · have hle : ∀ s : ℝ, (⨆ u : Ucal d, ENNReal.ofReal |w (s, u)|) ≤
            (Set.Ioc (0 : ℝ) t).indicator (fun _ => ENNReal.ofReal C) s := by
          intro s
          by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
          · rw [Set.indicator_of_mem hs]
            exact iSup_le fun u => ENNReal.ofReal_le_ofReal (by simpa [w, hs] using hg_bound u)
          · rw [Set.indicator_of_notMem hs]
            exact iSup_le fun u => by simp [w, hs]
        refine (lintegral_mono hle).trans_lt ?_
        rw [lintegral_indicator hIoc, setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
          refine (Measure.restrict_apply_le _ _).trans_lt ?_
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_lt_top)
    have _h_borel : BorelSpace (RelaxedControl d) := ⟨rfl⟩
    have hcont_rel : Continuous (fun α : RelaxedControl d =>
        ∫ s in Set.Ioi (0 : ℝ), ∫ u, w (s, u) ∂(α.1 s).toMeasure) := by
      rw [continuous_iff_le_induced]
      exact (induced_mono (iInf₂_le w hw)).trans induced_compose.le
    have hmeas_ctrl : Measurable (fun a : Control d =>
        ∫ s in Set.Ioi (0 : ℝ), ∫ u, w (s, u) ∂((a.toRelaxed).1 s).toMeasure) :=
      hcont_rel.measurable.comp (Measurable.of_comap_le le_rfl)
    have h_eq : (fun a : Control d =>
        ∫ s in Set.Ioc (0 : ℝ) t, (M.rho + ∑ i, a.val s i * (M.mu i - M.rho))) =
        fun a : Control d =>
          ∫ s in Set.Ioi (0 : ℝ), ∫ u, w (s, u) ∂((a.toRelaxed).1 s).toMeasure := by
      ext a
      have h_inner : ∀ s : ℝ, (∫ u, w (s, u) ∂((a.toRelaxed).1 s).toMeasure) =
          (Set.Ioc (0 : ℝ) t).indicator (fun s => g (a.val s)) s := by
        intro s
        change (∫ u, w (s, u) ∂Measure.dirac (⟨a.val s, a.mem s⟩ : Ucal d)) = _
        rw [integral_dirac]
        rfl
      simp_rw [h_inner]
      rw [integral_indicator hIoc, Measure.restrict_restrict hIoc,
          Set.Ioc_inter_Ioi, max_eq_left le_rfl]
    rw [h_eq]
    exact hmeas_ctrl
  · have h_empty : Set.Ioc (0 : ℝ) t = ∅ := Set.Ioc_eq_empty ht
    simp [h_empty, measurable_const]

lemma continuous_phi_time (M : JumpMarket d) (a : Control d) :
    Continuous (fun t : ℝ =>
      ∫ s in Set.Ioc (0 : ℝ) t, (M.rho + ∑ i, a.val s i * (M.mu i - M.rho))) := by
  let f : ℝ → ℝ := fun s => M.rho + ∑ i, a.val s i * (M.mu i - M.rho)
  have hf_meas : AEStronglyMeasurable f volume := by
    refine (measurable_const.add (Finset.measurable_sum _ fun i _ => ?_)).aestronglyMeasurable
    exact ((measurable_pi_apply i).comp a.meas).mul measurable_const
  let C : ℝ := |M.rho| + ∑ i : Fin d, |M.mu i - M.rho|
  have hf_bound : ∀ s : ℝ, ‖f s‖ ≤ C := by
    intro s
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (ucal_coord_le_one (a.mem s) i)
  have hf_int : ∀ u v : ℝ, IntervalIntegrable f volume u v := fun u v =>
    ⟨IntegrableOn.of_bound measure_Ioc_lt_top hf_meas.restrict C (Filter.Eventually.of_forall hf_bound),
     IntegrableOn.of_bound measure_Ioc_lt_top hf_meas.restrict C (Filter.Eventually.of_forall hf_bound)⟩
  have hcont_prim : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..(max 0 t), f s) :=
    (intervalIntegral.continuous_primitive hf_int 0).comp (continuous_const.max continuous_id)
  have h_eq : (fun t : ℝ => ∫ s in Set.Ioc (0 : ℝ) t, f s) =
      fun t : ℝ => ∫ s in (0 : ℝ)..(max 0 t), f s := by
    ext t
    by_cases ht : 0 ≤ t
    · rw [max_eq_right ht, intervalIntegral.integral_of_le ht]
    · rw [max_eq_left (le_of_not_ge ht), intervalIntegral.integral_same,
          Set.Ioc_eq_empty (not_lt_of_ge (le_of_not_ge ht)), MeasureTheory.setIntegral_empty]
  rw [h_eq]
  exact hcont_prim

lemma tendsto_floor_div_succ (t : ℝ) :
    Tendsto (fun n : ℕ => (⌊((n : ℝ) + 1) * t⌋ : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 t) := by
  have h_pos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have h_le : ∀ n : ℕ, t - 1 / ((n : ℝ) + 1) ≤ (⌊((n : ℝ) + 1) * t⌋ : ℝ) / ((n : ℝ) + 1) := by
    intro n
    rw [sub_div' (h_pos n).ne', div_le_div_iff_of_pos_right (h_pos n)]
    linarith [Int.sub_one_lt_floor (((n : ℝ) + 1) * t)]
  have h_ge : ∀ n : ℕ, (⌊((n : ℝ) + 1) * t⌋ : ℝ) / ((n : ℝ) + 1) ≤ t := by
    intro n
    rw [div_le_iff₀ (h_pos n)]
    linarith [Int.floor_le (((n : ℝ) + 1) * t)]
  have h_sub : Tendsto (fun n : ℕ => t - 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
    simpa [sub_zero] using (tendsto_const_nhds (x := t)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_sub tendsto_const_nhds h_le h_ge

lemma measurable_phi_joint (M : JumpMarket d) :
    Measurable (fun atx : (Control d × ℝ) × ℝ => M.phi atx.1.1 atx.1.2 atx.2) := by
  let F : Control d → ℝ → ℝ := fun a t =>
    ∫ s in Set.Ioc (0 : ℝ) t, (M.rho + ∑ i, a.val s i * (M.mu i - M.rho))
  have hF_meas : Measurable (fun at_1 : Control d × ℝ => F at_1.1 at_1.2) := by
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (at_1 : Control d × ℝ) =>
      F at_1.1 ((⌊((n : ℝ) + 1) * at_1.2⌋ : ℝ) / ((n : ℝ) + 1))) (fun n => ?_) ?_
    · have h1 : Measurable (fun az : Control d × ℤ => F az.1 ((az.2 : ℝ) / ((n : ℝ) + 1))) :=
        measurable_from_prod_countable_left fun z => measurable_phi_control M ((z : ℝ) / ((n : ℝ) + 1))
      have h2 : Measurable (fun at_1 : Control d × ℝ => (at_1.1, ⌊((n : ℝ) + 1) * at_1.2⌋)) :=
        measurable_fst.prodMk (Int.measurable_floor.comp (measurable_const.mul measurable_snd))
      exact h1.comp h2
    · rw [tendsto_pi_nhds]
      intro ⟨a, t⟩
      exact (continuous_phi_time M a).tendsto t |>.comp (tendsto_floor_div_succ t)
  exact measurable_snd.mul (Real.continuous_exp.measurable.comp (hF_meas.comp measurable_fst))

lemma measurable_map_of_measurable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (ν : Measure β) [SFinite ν] {F : α × β → γ} (hF : Measurable F) :
    Measurable (fun a => ν.map (fun b => F (a, b))) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have h_eq : (fun a => (ν.map (fun b => F (a, b))) s) =
      fun a => ∫⁻ b, s.indicator (fun _ => (1 : ℝ≥0∞)) (F (a, b)) ∂ν := by
    ext a
    have hFa : Measurable (fun b => F (a, b)) := hF.comp (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hFa hs, ← lintegral_indicator_one (hFa hs)]
    rfl
  rw [h_eq]
  exact ((measurable_const.indicator hs).comp hF).lintegral_prod_right'

lemma measurable_stepKernel (M : JumpMarket d) (a : Control d) (q : ℝ × ℝ) :
    Measurable (fun s : ℝ => M.QY.map (fun y => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i)))) := by
  have := M.QY_prob
  refine measurable_map_of_measurable M.QY
    (F := fun sy : ℝ × (Fin d → ℝ) => (q.1 + sy.1, M.phi a sy.1 q.2 * (1 + ∑ i, a.val sy.1 i * sy.2 i))) ?_
  refine (measurable_const.add measurable_fst).prodMk ?_
  have hphi_meas : Measurable (fun sy : ℝ × (Fin d → ℝ) => M.phi a sy.1 q.2) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_phi_time M a))).measurable.comp measurable_fst
  refine hphi_meas.mul (measurable_const.add (Finset.measurable_sum _ fun i _ => ?_))
  exact (((measurable_pi_apply i).comp a.meas).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)

lemma step_fst_preimage (M : JumpMarket d) (a : Control d) (q : ℝ × ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (M.step a q) (Prod.fst ⁻¹' A) =
      ∫⁻ s in Set.Ioi (0 : ℝ),
        ((fun s => q.1 + s) ⁻¹' A).indicator (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) s := by
  have := M.QY_prob
  unfold JumpMarket.step
  rw [Measure.bind_apply (measurable_fst hA) (measurable_stepKernel M a q).aemeasurable]
  have h_eval : ∀ s : ℝ,
      (M.QY.map (fun y => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i)))) (Prod.fst ⁻¹' A) =
        ((fun s => q.1 + s) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) s := by
    intro s
    have hm : Measurable (fun y : Fin d → ℝ => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i))) := by
      refine measurable_const.prodMk (measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun i _ => ?_)))
      exact measurable_const.mul (measurable_pi_apply i)
    rw [Measure.map_apply hm (measurable_fst hA)]
    by_cases hs : q.1 + s ∈ A
    · have h_pre : (fun y : Fin d → ℝ => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i))) ⁻¹' (Prod.fst ⁻¹' A) = Set.univ := by
        ext y; simp [hs]
      rw [h_pre, measure_univ, Set.indicator_of_mem (Set.mem_preimage.mpr hs)]
    · have h_pre : (fun y : Fin d → ℝ => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i))) ⁻¹' (Prod.fst ⁻¹' A) = ∅ := by
        ext y; simp [hs]
      rw [h_pre, measure_empty, Set.indicator_of_notMem (by simpa using hs)]
  simp_rw [h_eval]
  have h_dens : Measurable (fun s : ℝ => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))
  have h_ind_meas : Measurable (((fun s => q.1 + s) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator ((measurable_const.add measurable_id) hA)
  rw [lintegral_withDensity_eq_lintegral_mul _ h_dens h_ind_meas]
  refine lintegral_congr fun s => ?_
  by_cases hs : q.1 + s ∈ A <;> simp [hs]

lemma step_Iic_eq_zero (M : JumpMarket d) (a : Control d) {q : ℝ × ℝ} (hq : M.T < q.1) :
    (M.step a q) {q' : ℝ × ℝ | q'.1 ≤ M.T} = 0 := by
  change (M.step a q) (Prod.fst ⁻¹' Set.Iic M.T) = 0
  rw [step_fst_preimage M a q measurableSet_Iic]
  refine nonpos_iff_eq_zero.mp ((setLIntegral_mono' measurableSet_Ioi fun s hs => ?_).trans lintegral_zero.le)
  have hnot : s ∉ (fun s => q.1 + s) ⁻¹' Set.Iic M.T := by
    simp only [Set.mem_preimage, Set.mem_Iic]
    linarith [Set.mem_Ioi.mp hs]
  rw [Set.indicator_of_notMem hnot]

lemma step_Ioi_eq_exp (M : JumpMarket d) (a : Control d) {q : ℝ × ℝ} (hq : q.1 ≤ M.T) :
    (M.step a q) {q' : ℝ × ℝ | M.T < q'.1} = ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1))) := by
  change (M.step a q) (Prod.fst ⁻¹' Set.Ioi M.T) = _
  rw [step_fst_preimage M a q measurableSet_Ioi]
  have h_pre : (fun s : ℝ => q.1 + s) ⁻¹' Set.Ioi M.T = Set.Ioi (M.T - q.1) := by
    ext s; simp [sub_lt_iff_lt_add']
  rw [h_pre, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have h_inter : Set.Ioi (M.T - q.1) ∩ Set.Ioi (0 : ℝ) = Set.Ioi (M.T - q.1) :=
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi (sub_nonneg.mpr hq))
  rw [h_inter, lintegral_Ioi_lam_exp M.lam M.lam_pos (M.T - q.1)]

lemma step_snd_lt_zero_eq_zero (M : JumpMarket d) (a : Control d) {q : ℝ × ℝ} (hq : 0 ≤ q.2) :
    (M.step a q) {q' : ℝ × ℝ | q'.2 < 0} = 0 := by
  change (M.step a q) (Prod.snd ⁻¹' Set.Iio 0) = 0
  unfold JumpMarket.step
  rw [Measure.bind_apply (measurable_snd measurableSet_Iio) (measurable_stepKernel M a q).aemeasurable]
  have h_eval : ∀ s : ℝ,
      (M.QY.map (fun y => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i)))) (Prod.snd ⁻¹' Set.Iio 0) = 0 := by
    intro s
    have hm : Measurable (fun y : Fin d → ℝ => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i))) := by
      refine measurable_const.prodMk (measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun i _ => ?_)))
      exact measurable_const.mul (measurable_pi_apply i)
    rw [Measure.map_apply hm (measurable_snd measurableSet_Iio)]
    refine measure_mono_null (fun y hy => ?_) M.QY_supp
    simp only [Set.mem_preimage, Set.mem_Iio] at hy
    simp only [Set.mem_ofPred_eq]
    by_contra! h_gt
    have hphi : 0 ≤ M.phi a s q.2 := mul_nonneg hq (Real.exp_pos _).le
    have hsum : -1 ≤ ∑ i, a.val s i * y i := by
      have h1 : - ∑ i, a.val s i ≤ ∑ i, a.val s i * y i := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        have := mul_le_mul_of_nonneg_left (h_gt i).le ((a.mem s).1 i)
        linarith
      linarith [(a.mem s).2]
    linarith [mul_nonneg hphi (by linarith : 0 ≤ 1 + ∑ i, a.val s i * y i)]
  simp [h_eval]

lemma lintegral_step_exp_fst (M : JumpMarket d) (a : Control d) (q : ℝ × ℝ) :
    ∫⁻ q', ENNReal.ofReal (Real.exp (-M.lam * q'.1)) ∂(M.step a q) =
      (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-M.lam * q.1)) := by
  have := M.QY_prob
  unfold JumpMarket.step
  have hf_meas : Measurable (fun q' : ℝ × ℝ => ENNReal.ofReal (Real.exp (-M.lam * q'.1))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst))
  rw [Measure.lintegral_bind (measurable_stepKernel M a q).aemeasurable hf_meas.aemeasurable]
  have h_inner : ∀ s : ℝ,
      ∫⁻ q', ENNReal.ofReal (Real.exp (-M.lam * q'.1))
        ∂(M.QY.map (fun y => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i)))) =
        ENNReal.ofReal (Real.exp (-M.lam * (q.1 + s))) := by
    intro s
    have hm : Measurable (fun y : Fin d → ℝ => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i))) := by
      refine measurable_const.prodMk (measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun i _ => ?_)))
      exact measurable_const.mul (measurable_pi_apply i)
    rw [lintegral_map hf_meas hm]
    simp
  simp_rw [h_inner]
  have h_dens : Measurable (fun s : ℝ => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))
  have h_exp_meas : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-M.lam * (q.1 + s)))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_const.add measurable_id)))
  rw [lintegral_withDensity_eq_lintegral_mul _ h_dens h_exp_meas]
  have h_congr : ∀ s : ℝ,
      (ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) * ENNReal.ofReal (Real.exp (-M.lam * (q.1 + s)))) =
        ((1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-M.lam * q.1))) *
          ENNReal.ofReal ((2 * M.lam) * Real.exp (-(2 * M.lam) * s)) := by
    intro s
    have h1 : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [one_div, one_div, ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
    rw [h1, ← ENNReal.ofReal_mul (mul_nonneg M.lam_pos.le (Real.exp_pos _).le),
        ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (Real.exp_pos _).le)]
    congr 1
    rw [mul_add, Real.exp_add]
    have hexp : Real.exp (-(2 * M.lam) * s) = Real.exp (-M.lam * s) * Real.exp (-M.lam * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]
    ring
  simp_rw [Pi.mul_apply, h_congr]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top),
      lintegral_Ioi_lam_exp (2 * M.lam) (by linarith [M.lam_pos]) 0]
  simp

noncomputable def chainExpect (M : JumpMarket d) (g : HistPolicy d) :
    (n : ℕ) → (Fin (n + 1) → ℝ × ℝ) → ℕ → (ℝ × ℝ → ℝ≥0∞) → ℝ≥0∞
  | _, h, 0, ψ => ψ (h (Fin.last _))
  | n, h, m + 1, ψ =>
      ∫⁻ q, chainExpect M g (n + 1) (Fin.snoc h q) m ψ ∂(M.step (g n h) (h (Fin.last n)))

lemma chainExpect_mono (M : JumpMarket d) (g : HistPolicy d) :
    ∀ (m n : ℕ) (h : Fin (n + 1) → ℝ × ℝ) {ψ₁ ψ₂ : ℝ × ℝ → ℝ≥0∞},
      (∀ q, ψ₁ q ≤ ψ₂ q) → chainExpect M g n h m ψ₁ ≤ chainExpect M g n h m ψ₂
  | 0, _, h, _, _, hle => hle (h (Fin.last _))
  | m + 1, n, h, _, _, hle =>
      lintegral_mono fun q => chainExpect_mono M g m (n + 1) (Fin.snoc h q) hle

lemma chainExpect_const_mul (M : JumpMarket d) (g : HistPolicy d) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    ∀ (m n : ℕ) (h : Fin (n + 1) → ℝ × ℝ) (ψ : ℝ × ℝ → ℝ≥0∞),
      chainExpect M g n h m (fun q => c * ψ q) = c * chainExpect M g n h m ψ
  | 0, _, _, _ => rfl
  | m + 1, n, h, ψ => by
      simp only [chainExpect, chainExpect_const_mul M g c hc m (n + 1) _ ψ,
        lintegral_const_mul' c _ hc]

lemma chainExpect_zero (M : JumpMarket d) (g : HistPolicy d) :
    ∀ (m n : ℕ) (h : Fin (n + 1) → ℝ × ℝ),
      chainExpect M g n h m (fun _ => 0) = 0
  | 0, _, _ => rfl
  | m + 1, n, h => by
      simp [chainExpect, chainExpect_zero M g m (n + 1)]

lemma chainCyl_single_aux (M : JumpMarket d) (g : HistPolicy d) (S : Set (ℝ × ℝ))
    (hS : MeasurableSet S) :
    ∀ (k n : ℕ) (h : Fin (n + 1) → ℝ × ℝ) (B : ℕ → Set (ℝ × ℝ)),
      (∀ i < k, B i = Set.univ) → B k = S →
      M.chainCyl g n h (k + 1) B = chainExpect M g n h (k + 1) (S.indicator (fun _ => 1))
  | 0, n, h, B, _, hB0 => by
      simp only [JumpMarket.chainCyl, chainExpect, hB0, ← lintegral_indicator hS, Fin.snoc_last]
  | k + 1, n, h, B, hB_lt, hBk => by
      simp only [JumpMarket.chainCyl, chainExpect]
      rw [hB_lt 0 (Nat.zero_lt_succ k), Measure.restrict_univ]
      congr 1
      ext q
      exact chainCyl_single_aux M g S hS k (n + 1) (Fin.snoc h q) (fun i => B (i + 1))
        (fun i hi => hB_lt (i + 1) (Nat.succ_lt_succ hi)) hBk

lemma pr_coord_mem (M : JumpMarket d) (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hLaw : M.IsChainLaw g Pr) (p : ℝ × ℝ) (k : ℕ) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    Pr p {w : ℕ → ℝ × ℝ | w k ∈ S} = chainExpect M g 0 (fun _ => p) k (S.indicator (fun _ => 1)) := by
  let B : ℕ → Set (ℝ × ℝ) := fun i => if i = k then S else Set.univ
  have hB_meas : ∀ i, MeasurableSet (B i) := by
    intro i; by_cases hi : i = k <;> simp [B, hi, hS]
  have h_set : {w : ℕ → ℝ × ℝ | w k ∈ S} = {w : ℕ → ℝ × ℝ | ∀ i ≤ k, w i ∈ B i} := by
    ext w
    simp only [Set.mem_ofPred_eq, B]
    refine ⟨fun hw i _ => ?_, fun h => by simpa using h k le_rfl⟩
    split_ifs with hik
    · subst hik; exact hw
    · trivial
  rw [h_set, hLaw.2 p k B hB_meas]
  cases k with
  | zero =>
      simp [B, JumpMarket.chainCyl, chainExpect]
  | succ k =>
      have hB0 : p ∈ B 0 := by simp [B]
      rw [Set.indicator_of_mem hB0]
      exact chainCyl_single_aux M g S hS k 0 (fun _ => p) (fun i => B (i + 1))
        (fun i hi => by dsimp [B]; exact if_neg (by omega))
        (by simp [B])

lemma chainCyl_pair_aux (M : JumpMarket d) (g : HistPolicy d) (S T' : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (φ : ℝ × ℝ → ℝ≥0∞)
    (hφ : ∀ (a : Control d), ∀ q ∈ S, (M.step a q) T' = φ q) :
    ∀ (k n : ℕ) (h : Fin (n + 1) → ℝ × ℝ) (B : ℕ → Set (ℝ × ℝ)),
      (∀ i < k, B i = Set.univ) → B k = S → B (k + 1) = T' →
      M.chainCyl g n h (k + 2) B = chainExpect M g n h (k + 1) (S.indicator φ)
  | 0, n, h, B, _, hB0, hB1 => by
      simp only [JumpMarket.chainCyl, chainExpect, hB0, hB1, ← lintegral_indicator hS, Fin.snoc_last]
      refine lintegral_congr fun q => ?_
      by_cases hq : q ∈ S
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, lintegral_const, one_mul,
            Measure.restrict_apply_univ, hφ _ q hq]
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
  | k + 1, n, h, B, hB_lt, hBk, hBk1 => by
      simp only [JumpMarket.chainCyl, chainExpect]
      rw [hB_lt 0 (Nat.zero_lt_succ k), Measure.restrict_univ]
      congr 1
      ext q
      exact chainCyl_pair_aux M g S T' hS φ hφ k (n + 1) (Fin.snoc h q) (fun i => B (i + 1))
        (fun i hi => hB_lt (i + 1) (Nat.succ_lt_succ hi)) hBk hBk1

lemma pr_pair_mem (M : JumpMarket d) (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hLaw : M.IsChainLaw g Pr) (p : ℝ × ℝ) (k : ℕ) (S T' : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (hT : MeasurableSet T') (φ : ℝ × ℝ → ℝ≥0∞)
    (hφ : ∀ (a : Control d), ∀ q ∈ S, (M.step a q) T' = φ q) :
    Pr p {w : ℕ → ℝ × ℝ | w k ∈ S ∧ w (k + 1) ∈ T'} =
      chainExpect M g 0 (fun _ => p) k (S.indicator φ) := by
  let B : ℕ → Set (ℝ × ℝ) := fun i => if i = k then S else if i = k + 1 then T' else Set.univ
  have hB_meas : ∀ i, MeasurableSet (B i) := by
    intro i
    by_cases hi1 : i = k
    · simp [B, hi1, hS]
    · by_cases hi2 : i = k + 1 <;> simp [B, hi1, hi2, hT]
  have h_set : {w : ℕ → ℝ × ℝ | w k ∈ S ∧ w (k + 1) ∈ T'} =
      {w : ℕ → ℝ × ℝ | ∀ i ≤ k + 1, w i ∈ B i} := by
    ext w
    simp only [Set.mem_ofPred_eq, B]
    refine ⟨fun ⟨hwk, hwk1⟩ i _ => ?_, fun h => ⟨?_, ?_⟩⟩
    · split_ifs with hi1 hi2
      · subst hi1; exact hwk
      · subst hi2; exact hwk1
      · trivial
    · simpa using h k (Nat.le_succ k)
    · simpa [Nat.succ_ne_self] using h (k + 1) le_rfl
  rw [h_set, hLaw.2 p (k + 1) B hB_meas]
  cases k with
  | zero =>
      dsimp [B, JumpMarket.chainCyl, chainExpect]
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, lintegral_const, one_mul,
            Measure.restrict_apply_univ, hφ _ p hp]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
  | succ k =>
      have hB0 : p ∈ B 0 := by simp [B]
      rw [Set.indicator_of_mem hB0]
      exact chainCyl_pair_aux M g S T' hS φ hφ k 0 (fun _ => p) (fun i => B (i + 1))
        (fun i hi => by dsimp [B]; rw [if_neg (by omega), if_neg (by omega)])
        (by dsimp [B]; rw [if_pos rfl])
        (by dsimp [B]; rw [if_neg (by omega), if_pos rfl])

lemma pr_w0_ne_eq_zero (M : JumpMarket d) (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hLaw : M.IsChainLaw g Pr) (p : ℝ × ℝ) :
    Pr p {w : ℕ → ℝ × ℝ | w 0 ≠ p} = 0 := by
  have := pr_coord_mem M g Pr hLaw p 0 ({p}ᶜ) (MeasurableSet.compl (measurableSet_singleton p))
  simpa [chainExpect] using this

lemma pr_jump_drop_eq_zero (M : JumpMarket d) (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hLaw : M.IsChainLaw g Pr) (p : ℝ × ℝ) (k : ℕ) :
    Pr p {w : ℕ → ℝ × ℝ | M.T < (w k).1 ∧ (w (k + 1)).1 ≤ M.T} = 0 := by
  have h1 := pr_pair_mem M g Pr hLaw p k {q : ℝ × ℝ | M.T < q.1} {q' : ℝ × ℝ | q'.1 ≤ M.T}
    (measurable_fst measurableSet_Ioi) (measurable_fst measurableSet_Iic) (fun _ => 0)
    (fun a q hq => step_Iic_eq_zero M a hq)
  simpa [Set.indicator_zero', chainExpect_zero] using h1

lemma pr_wealth_neg_eq_zero (M : JumpMarket d) (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hLaw : M.IsChainLaw g Pr) {p : ℝ × ℝ} (hp : 0 ≤ p.2) :
    ∀ k : ℕ, Pr p {w : ℕ → ℝ × ℝ | (w k).2 < 0} = 0
  | 0 => by
      have h1 := pr_coord_mem M g Pr hLaw p 0 {q : ℝ × ℝ | q.2 < 0} (measurable_snd measurableSet_Iio)
      simpa [chainExpect, not_lt.mpr hp] using h1
  | k + 1 => by
      have h_sub : {w : ℕ → ℝ × ℝ | (w (k + 1)).2 < 0} ⊆
          {w : ℕ → ℝ × ℝ | (w k).2 < 0} ∪ {w : ℕ → ℝ × ℝ | 0 ≤ (w k).2 ∧ (w (k + 1)).2 < 0} := by
        intro w hw
        by_cases hwk : (w k).2 < 0
        · exact Or.inl hwk
        · exact Or.inr ⟨not_lt.mp hwk, hw⟩
      refine measure_mono_null h_sub (measure_union_null (pr_wealth_neg_eq_zero M g Pr hLaw hp k) ?_)
      have h1 := pr_pair_mem M g Pr hLaw p k {q : ℝ × ℝ | 0 ≤ q.2} {q' : ℝ × ℝ | q'.2 < 0}
        (measurable_snd measurableSet_Ici) (measurable_snd measurableSet_Iio) (fun _ => 0)
        (fun a q hq => step_snd_lt_zero_eq_zero M a hq)
      simpa [Set.indicator_zero', chainExpect_zero] using h1

lemma chainExpect_exp_fst (M : JumpMarket d) (g : HistPolicy d) :
    ∀ (m n : ℕ) (h : Fin (n + 1) → ℝ × ℝ),
      chainExpect M g n h m (fun q => ENNReal.ofReal (Real.exp (-M.lam * q.1))) =
        (1 / 2 : ℝ≥0∞) ^ m * ENNReal.ofReal (Real.exp (-M.lam * (h (Fin.last n)).1))
  | 0, _, _ => by simp [chainExpect]
  | m + 1, n, h => by
      simp only [chainExpect, chainExpect_exp_fst M g m (n + 1)]
      simp only [Fin.snoc_last]
      rw [lintegral_const_mul' ((1 / 2 : ℝ≥0∞) ^ m) _ (ENNReal.pow_ne_top (by norm_num)),
          lintegral_step_exp_fst, ← mul_assoc, ← pow_succ]

lemma pr_all_le_T_eq_zero (M : JumpMarket d) (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hLaw : M.IsChainLaw g Pr) (p : ℝ × ℝ) :
    Pr p {w : ℕ → ℝ × ℝ | ∀ k : ℕ, (w k).1 ≤ M.T} = 0 := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (M.lam * M.T))
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_bound : ∀ k : ℕ,
      Pr p {w : ℕ → ℝ × ℝ | ∀ n : ℕ, (w n).1 ≤ M.T} ≤
        (1 / 2 : ℝ≥0∞) ^ k * (c * ENNReal.ofReal (Real.exp (-M.lam * p.1))) := by
    intro k
    have h_sub : {w : ℕ → ℝ × ℝ | ∀ n : ℕ, (w n).1 ≤ M.T} ⊆
        {w : ℕ → ℝ × ℝ | w k ∈ {q : ℝ × ℝ | q.1 ≤ M.T}} := fun w hw => hw k
    refine (measure_mono h_sub).trans ?_
    rw [pr_coord_mem M g Pr hLaw p k {q : ℝ × ℝ | q.1 ≤ M.T} (measurable_fst measurableSet_Iic)]
    have h_ind_le : ∀ q : ℝ × ℝ,
        ({q : ℝ × ℝ | q.1 ≤ M.T} : Set (ℝ × ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) q ≤
          c * ENNReal.ofReal (Real.exp (-M.lam * q.1)) := by
      intro q
      by_cases hq : q.1 ≤ M.T
      · have h1 : q ∈ {q : ℝ × ℝ | q.1 ≤ M.T} := hq
        rw [Set.indicator_of_mem h1, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        have h_exp : 1 ≤ Real.exp (M.lam * M.T + -M.lam * q.1) := by
          rw [Real.one_le_exp_iff]
          nlinarith [M.lam_pos]
        simpa using ENNReal.ofReal_le_ofReal h_exp
      · have h1 : q ∉ {q : ℝ × ℝ | q.1 ≤ M.T} := hq
        rw [Set.indicator_of_notMem h1]
        exact zero_le
    refine (chainExpect_mono M g k 0 (fun _ => p) h_ind_le).trans ?_
    rw [chainExpect_const_mul M g c hc_ne_top, chainExpect_exp_fst]
    ring_nf
    exact le_rfl
  have h_tendsto : Tendsto (fun k : ℕ => (1 / 2 : ℝ≥0∞) ^ k * (c * ENNReal.ofReal (Real.exp (-M.lam * p.1))))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
      (Or.inr (ENNReal.mul_ne_top hc_ne_top ENNReal.ofReal_ne_top))
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto h_tendsto (Filter.Eventually.of_forall h_bound))

lemma ennreal_le_of_forall_add_inv_nat {A B : ℝ≥0∞}
    (hAB : ∀ N : ℕ, 0 < N → A ≤ B + 1 / (N : ℝ≥0∞)) : A ≤ B := by
  by_cases hB : B = ⊤
  · subst hB; exact le_top
  · have hA : A ≠ ⊤ := by
      have h1 : A ≤ B + 1 := by simpa using hAB 1 Nat.one_pos
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hB, by norm_num⟩) h1
    rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB]
    refine ENNReal.ofReal_le_ofReal (le_of_forall_pos_le_add fun ε hε => ?_)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    have hN_pos : 0 < N + 1 := Nat.succ_pos N
    have h1 := hAB (N + 1) hN_pos
    have h_inv_ne_top : (1 / ((N + 1 : ℕ) : ℝ≥0∞)) ≠ ⊤ := by simp
    have h2 := (ENNReal.toReal_le_toReal hA (ENNReal.add_ne_top.mpr ⟨hB, h_inv_ne_top⟩)).mpr h1
    rw [ENNReal.toReal_add hB h_inv_ne_top, one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        Nat.cast_add, Nat.cast_one, ← one_div] at h2
    linarith [hN.le]

lemma ennreal_eq_of_forall_add_inv_nat {L R : ℝ≥0∞}
    (h1 : ∀ N : ℕ, 0 < N → L ≤ R + 1 / (N : ℝ≥0∞))
    (h2 : ∀ N : ℕ, 0 < N → R ≤ L + 1 / (N : ℝ≥0∞)) :
    L = R :=
  le_antisymm (ennreal_le_of_forall_add_inv_nat h1) (ennreal_le_of_forall_add_inv_nat h2)

lemma pr_pair_Ioi_bounds (M : JumpMarket d) (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hLaw : M.IsChainLaw g Pr) (p : ℝ × ℝ) (k : ℕ) {A : Set (ℝ × ℝ)}
    (hA : MeasurableSet A) (hA_sub : ∀ q ∈ A, q.1 ≤ M.T)
    {c₁ c₂ : ℝ≥0∞} (hc₁ : c₁ ≠ ⊤) (hc₂ : c₂ ≠ ⊤)
    (h_le : ∀ q ∈ A, c₁ ≤ ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1))) ∧
      ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1))) ≤ c₂) :
    c₁ * Pr p {w | w k ∈ A} ≤ Pr p {w | w k ∈ A ∧ M.T < (w (k + 1)).1} ∧
      Pr p {w | w k ∈ A ∧ M.T < (w (k + 1)).1} ≤ c₂ * Pr p {w | w k ∈ A} := by
  let e_T : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1)))
  have h_pair := pr_pair_mem M g Pr hLaw p k A {q' : ℝ × ℝ | M.T < q'.1}
    hA (measurable_fst measurableSet_Ioi) e_T (fun a q hq => step_Ioi_eq_exp M a (hA_sub q hq))
  have h_coord := pr_coord_mem M g Pr hLaw p k A hA
  change c₁ * Pr p {w | w k ∈ A} ≤ Pr p {w | w k ∈ A ∧ w (k + 1) ∈ {q' : ℝ × ℝ | M.T < q'.1}} ∧
    Pr p {w | w k ∈ A ∧ w (k + 1) ∈ {q' : ℝ × ℝ | M.T < q'.1}} ≤ c₂ * Pr p {w | w k ∈ A}
  rw [h_pair, h_coord, ← chainExpect_const_mul M g c₁ hc₁, ← chainExpect_const_mul M g c₂ hc₂]
  refine ⟨chainExpect_mono M g k 0 (fun _ => p) fun q => ?_,
          chainExpect_mono M g k 0 (fun _ => p) fun q => ?_⟩
  · by_cases hq : q ∈ A
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, mul_one]
      exact (h_le q hq).1
    · simp [hq]
  · by_cases hq : q ∈ A
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, mul_one]
      exact (h_le q hq).2
    · simp [hq]

lemma pr_pair_Ioi_eq_setLIntegral (M : JumpMarket d) (g : HistPolicy d)
    (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ)) (hLaw : M.IsChainLaw g Pr) (p : ℝ × ℝ) (k : ℕ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hS_sub : ∀ q ∈ S, q.1 ≤ M.T) :
    Pr p {w | w k ∈ S ∧ M.T < (w (k + 1)).1} =
      ∫⁻ w in {w | w k ∈ S}, ENNReal.ofReal (Real.exp (-M.lam * (M.T - (w k).1))) ∂(Pr p) := by
  have := hLaw.1 p
  let e_T : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1)))
  have h_approx : ∀ N : ℕ, 0 < N →
      ∃ S_N : ℝ≥0∞,
        (S_N ≤ Pr p {w | w k ∈ S ∧ M.T < (w (k + 1)).1} ∧
          Pr p {w | w k ∈ S ∧ M.T < (w (k + 1)).1} ≤ S_N + 1 / (N : ℝ≥0∞)) ∧
        (S_N ≤ (∫⁻ w in {w | w k ∈ S}, e_T (w k) ∂(Pr p)) ∧
          (∫⁻ w in {w | w k ∈ S}, e_T (w k) ∂(Pr p)) ≤ S_N + 1 / (N : ℝ≥0∞)) := by
    intro N hN
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    let b : ℝ × ℝ → ℕ := fun q => ⌊(N : ℝ) * Real.exp (-M.lam * (M.T - q.1))⌋₊
    have hb_meas : Measurable b :=
      Nat.measurable_floor.comp (measurable_const.mul
        (Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_const.sub measurable_fst))))
    let A : ℕ → Set (ℝ × ℝ) := fun i => S ∩ {q | b q = i}
    have hA_meas : ∀ i, MeasurableSet (A i) :=
      fun i => hS.inter (hb_meas (measurableSet_singleton i))
    have hA_disj : Set.PairwiseDisjoint (↑(Finset.range (N + 1)) : Set ℕ) A := by
      intro i _ j _ hij
      rw [Function.onFun, Set.disjoint_left]
      rintro q ⟨_, rfl⟩ ⟨_, h2⟩
      exact hij h2
    have hA_union : (⋃ i ∈ Finset.range (N + 1), A i) = S := by
      ext q
      simp only [Set.mem_iUnion, Finset.mem_range, A, Set.mem_inter_iff, Set.mem_ofPred_eq]
      refine ⟨fun ⟨i, _, hq, _⟩ => hq, fun hq => ⟨b q, ?_, hq, rfl⟩⟩
      have hexp : Real.exp (-M.lam * (M.T - q.1)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [M.lam_pos, hS_sub q hq]
      have hfl : b q ≤ N := Nat.floor_le_of_le (by simpa using mul_le_mul_of_nonneg_left hexp hN_pos.le)
      exact Nat.lt_succ_of_le hfl
    have hA_bounds : ∀ i, ∀ q ∈ A i,
        ENNReal.ofReal ((i : ℝ) / N) ≤ e_T q ∧ e_T q ≤ ENNReal.ofReal (((i : ℝ) + 1) / N) := by
      intro i q ⟨_, hbi⟩
      subst hbi
      refine ⟨ENNReal.ofReal_le_ofReal ?_, ENNReal.ofReal_le_ofReal ?_⟩
      · rw [div_le_iff₀ hN_pos, mul_comm]
        exact Nat.floor_le (mul_nonneg hN_pos.le (Real.exp_pos _).le)
      · rw [le_div_iff₀ hN_pos, mul_comm]
        exact (Nat.lt_floor_add_one _).le
    let W : ℕ → Set (ℕ → ℝ × ℝ) := fun i => {w | w k ∈ A i}
    let W_T : ℕ → Set (ℕ → ℝ × ℝ) := fun i => {w | w k ∈ A i ∧ M.T < (w (k + 1)).1}
    have hW_meas : ∀ i, MeasurableSet (W i) := fun i => measurable_pi_apply k (hA_meas i)
    have hWT_meas : ∀ i, MeasurableSet (W_T i) := fun i =>
      (hW_meas i).inter (by
        show MeasurableSet {w : ℕ → ℝ × ℝ | M.T < (w (k + 1)).1}
        exact measurableSet_lt measurable_const (measurable_fst.comp (measurable_pi_apply (k + 1))))
    have hW_disj : Set.PairwiseDisjoint (↑(Finset.range (N + 1)) : Set ℕ) W := by
      intro i hi j hj hij
      rw [Function.onFun, Set.disjoint_left]
      intro w hwi hwj
      exact Set.disjoint_left.mp (hA_disj hi hj hij) hwi hwj
    have hWT_disj : Set.PairwiseDisjoint (↑(Finset.range (N + 1)) : Set ℕ) W_T := by
      intro i hi j hj hij
      rw [Function.onFun, Set.disjoint_left]
      intro w hwi hwj
      exact Set.disjoint_left.mp (hA_disj hi hj hij) hwi.1 hwj.1
    have hW_union : (⋃ i ∈ Finset.range (N + 1), W i) = {w | w k ∈ S} := by
      ext w
      rw [← hA_union]
      simp [W]
    have hWT_union : (⋃ i ∈ Finset.range (N + 1), W_T i) = {w | w k ∈ S ∧ M.T < (w (k + 1)).1} := by
      ext w
      rw [← hA_union]
      simp [W_T, ← exists_and_right]
      tauto
    let S_N : ℝ≥0∞ := ∑ i ∈ Finset.range (N + 1), ENNReal.ofReal ((i : ℝ) / N) * Pr p (W i)
    refine ⟨S_N, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [← hWT_union, measure_biUnion_finset hWT_disj (fun i _ => hWT_meas i)]
      refine Finset.sum_le_sum fun i _ => ?_
      exact (pr_pair_Ioi_bounds M g Pr hLaw p k (hA_meas i) (fun q hq => hS_sub q hq.1)
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (hA_bounds i)).1
    · rw [← hWT_union, measure_biUnion_finset hWT_disj (fun i _ => hWT_meas i)]
      have h_sum_le : ∑ i ∈ Finset.range (N + 1), Pr p (W_T i) ≤
          ∑ i ∈ Finset.range (N + 1), ENNReal.ofReal (((i : ℝ) + 1) / N) * Pr p (W i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact (pr_pair_Ioi_bounds M g Pr hLaw p k (hA_meas i) (fun q hq => hS_sub q hq.1)
          ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (hA_bounds i)).2
      refine h_sum_le.trans ?_
      have h_split : ∀ i : ℕ, ENNReal.ofReal (((i : ℝ) + 1) / N) * Pr p (W i) =
          ENNReal.ofReal ((i : ℝ) / N) * Pr p (W i) + ENNReal.ofReal (1 / (N : ℝ)) * Pr p (W i) := by
        intro i
        rw [add_div, ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg i) hN_pos.le) (by positivity), add_mul]
      simp_rw [h_split, Finset.sum_add_distrib]
      refine add_le_add le_rfl ?_
      rw [← Finset.mul_sum, ← measure_biUnion_finset hW_disj (fun i _ => hW_meas i), hW_union]
      have h_inv : ENNReal.ofReal (1 / (N : ℝ)) = 1 / (N : ℝ≥0∞) := by
        rw [one_div, one_div, ENNReal.ofReal_inv_of_pos hN_pos, ENNReal.ofReal_natCast]
      rw [h_inv]
      exact mul_le_of_le_one_right zero_le prob_le_one
    · rw [← hW_union, lintegral_biUnion_finset hW_disj (fun i _ => hW_meas i)]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : ENNReal.ofReal ((i : ℝ) / N) * Pr p (W i) = ∫⁻ _ in W i, ENNReal.ofReal ((i : ℝ) / N) ∂(Pr p) := by
        rw [setLIntegral_const]
      rw [h1]
      exact setLIntegral_mono' (hW_meas i) fun w hw => (hA_bounds i (w k) hw).1
    · rw [← hW_union, lintegral_biUnion_finset hW_disj (fun i _ => hW_meas i)]
      have h_sum_le : (∑ i ∈ Finset.range (N + 1), ∫⁻ w in W i, e_T (w k) ∂(Pr p)) ≤
          ∑ i ∈ Finset.range (N + 1), ENNReal.ofReal (((i : ℝ) + 1) / N) * Pr p (W i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : ENNReal.ofReal (((i : ℝ) + 1) / N) * Pr p (W i) =
            ∫⁻ _ in W i, ENNReal.ofReal (((i : ℝ) + 1) / N) ∂(Pr p) := by
          rw [setLIntegral_const]
        rw [h1]
        exact setLIntegral_mono' (hW_meas i) fun w hw => (hA_bounds i (w k) hw).2
      refine h_sum_le.trans ?_
      have h_split : ∀ i : ℕ, ENNReal.ofReal (((i : ℝ) + 1) / N) * Pr p (W i) =
          ENNReal.ofReal ((i : ℝ) / N) * Pr p (W i) + ENNReal.ofReal (1 / (N : ℝ)) * Pr p (W i) := by
        intro i
        rw [add_div, ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg i) hN_pos.le) (by positivity), add_mul]
      simp_rw [h_split, Finset.sum_add_distrib]
      refine add_le_add le_rfl ?_
      rw [← Finset.mul_sum, ← measure_biUnion_finset hW_disj (fun i _ => hW_meas i), hW_union]
      have h_inv : ENNReal.ofReal (1 / (N : ℝ)) = 1 / (N : ℝ≥0∞) := by
        rw [one_div, one_div, ENNReal.ofReal_inv_of_pos hN_pos, ENNReal.ofReal_natCast]
      rw [h_inv]
      exact mul_le_of_le_one_right zero_le prob_le_one
  refine ennreal_eq_of_forall_add_inv_nat (fun N hN => ?_) (fun N hN => ?_)
  · obtain ⟨S_N, ⟨_, hL2⟩, ⟨hR1, _⟩⟩ := h_approx N hN
    exact hL2.trans (add_le_add hR1 le_rfl)
  · obtain ⟨S_N, ⟨hL1, _⟩, ⟨_, hR2⟩⟩ := h_approx N hN
    exact hR2.trans (add_le_add hL1 le_rfl)

lemma measurable_coord_fst (j : ℕ) : Measurable (fun w : ℕ → ℝ × ℝ => (w j).1) :=
  measurable_fst.comp (measurable_pi_apply j)

lemma stage_reward_lintegral_eq (M : JumpMarket d) (f : ℕ → ℝ × ℝ → Control d)
    (hf : IsMarkovStrategy f) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hLaw : M.IsChainLaw (ofMarkov f) Pr) {p : ℝ × ℝ} (hp : 0 ≤ p.2) (k : ℕ) :
    ∫⁻ w in {w | (w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1},
        ENNReal.ofReal (M.U (M.phi (f k (w k)) (M.T - (w k).1) (w k).2)) ∂(Pr p) =
      ∫⁻ w, (if (w k).1 ≤ M.T then ENNReal.ofReal (M.r (f k (w k)) (w k)) else 0) ∂(Pr p) := by
  let S₀ : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.1 ≤ M.T ∧ 0 ≤ q.2}
  have hS₀_meas : MeasurableSet S₀ :=
    (measurable_fst measurableSet_Iic).inter (measurable_snd measurableSet_Ici)
  let e_T : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (Real.exp (-M.lam * (M.T - q.1)))
  have he_T_meas : Measurable e_T :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_const.sub measurable_fst)))
  let u_k : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (M.U (max 0 (M.phi (f k q) (M.T - q.1) q.2)))
  have hU_max_cont : Continuous (fun x : ℝ => M.U (max 0 x)) :=
    M.U_cont.comp_continuous (continuous_const.max continuous_id) (fun x => le_max_left 0 x)
  have hu_k_meas : Measurable u_k := by
    refine ENNReal.measurable_ofReal.comp (hU_max_cont.measurable.comp ?_)
    exact (measurable_phi_joint M).comp (((hf k).prodMk (measurable_const.sub measurable_fst)).prodMk measurable_snd)
  let W₀ : Set (ℕ → ℝ × ℝ) := {w | w k ∈ S₀}
  let W_T : Set (ℕ → ℝ × ℝ) := {w | w k ∈ S₀ ∧ M.T < (w (k + 1)).1}
  have hW₀_meas : MeasurableSet W₀ := measurable_pi_apply k hS₀_meas
  have hWT_meas : MeasurableSet W_T :=
    hW₀_meas.inter (measurableSet_lt measurable_const (measurable_coord_fst (k + 1)))
  let μ₁ : Measure (ℝ × ℝ) := ((Pr p).restrict W_T).map (fun w => w k)
  let μ₂ : Measure (ℝ × ℝ) := (((Pr p).restrict W₀).map (fun w => w k)).withDensity e_T
  have h_mu_eq : μ₁ = μ₂ := by
    ext S hS
    have h1 : μ₁ S = Pr p {w | w k ∈ S ∩ S₀ ∧ M.T < (w (k + 1)).1} := by
      rw [Measure.map_apply (measurable_pi_apply k) hS, Measure.restrict_apply ((measurable_pi_apply k) hS)]
      congr 1
      ext w
      simp [W_T, S₀, and_assoc]
    have h2 : μ₂ S = ∫⁻ w in {w | w k ∈ S ∩ S₀}, e_T (w k) ∂(Pr p) := by
      have hmS : MeasurableSet {w : ℕ → ℝ × ℝ | w k ∈ S} := measurable_pi_apply k hS
      rw [withDensity_apply _ hS, ← lintegral_indicator hS,
          lintegral_map (he_T_meas.indicator hS) (measurable_pi_apply k)]
      have hind : (fun a : ℕ → ℝ × ℝ => S.indicator e_T (a k)) =
          {w : ℕ → ℝ × ℝ | w k ∈ S}.indicator (fun w => e_T (w k)) := by
        ext w; by_cases hw : w k ∈ S <;> simp [hw]
      rw [hind, lintegral_indicator hmS, Measure.restrict_restrict hmS]
      rfl
    rw [h1, h2]
    exact pr_pair_Ioi_eq_setLIntegral M (ofMarkov f) Pr hLaw p k (hS.inter hS₀_meas) (fun q hq => hq.2.1)
  have h_int_mu : ∫⁻ q, u_k q ∂μ₁ = ∫⁻ q, u_k q ∂μ₂ := by rw [h_mu_eq]
  have h_lhs_mu : ∫⁻ q, u_k q ∂μ₁ = ∫⁻ w in W_T, u_k (w k) ∂(Pr p) :=
    lintegral_map hu_k_meas (measurable_pi_apply k)
  have h_rhs_mu : ∫⁻ q, u_k q ∂μ₂ = ∫⁻ w in W₀, e_T (w k) * u_k (w k) ∂(Pr p) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ he_T_meas hu_k_meas]
    exact lintegral_map (he_T_meas.mul hu_k_meas) (measurable_pi_apply k)
  have h_ae_nonneg : ∀ᵐ w ∂(Pr p), 0 ≤ (w k).2 := by
    rw [ae_iff]
    simpa [not_le] using pr_wealth_neg_eq_zero M (ofMarkov f) Pr hLaw hp k
  have h_lhs_eq : ∫⁻ w in {w | (w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1},
      ENNReal.ofReal (M.U (M.phi (f k (w k)) (M.T - (w k).1) (w k).2)) ∂(Pr p) =
      ∫⁻ w in W_T, u_k (w k) ∂(Pr p) := by
    have h_meas1 : MeasurableSet {w : ℕ → ℝ × ℝ | (w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1} :=
      (measurableSet_le (measurable_coord_fst k) measurable_const).inter
        (measurableSet_lt measurable_const (measurable_coord_fst (k + 1)))
    rw [← lintegral_indicator h_meas1, ← lintegral_indicator hWT_meas]
    refine lintegral_congr_ae (h_ae_nonneg.mono fun w hw => ?_)
    have hphi_nonneg : 0 ≤ M.phi (f k (w k)) (M.T - (w k).1) (w k).2 :=
      mul_nonneg hw (Real.exp_pos _).le
    by_cases hwk : w ∈ {w : ℕ → ℝ × ℝ | (w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1}
    · have hwk' : w ∈ W_T := ⟨⟨hwk.1, hw⟩, hwk.2⟩
      rw [Set.indicator_of_mem hwk, Set.indicator_of_mem hwk']
      simp [u_k, max_eq_right hphi_nonneg]
    · have hwk' : w ∉ W_T := fun h => hwk ⟨h.1.1, h.2⟩
      rw [Set.indicator_of_notMem hwk, Set.indicator_of_notMem hwk']
  have h_rhs_eq : ∫⁻ w, (if (w k).1 ≤ M.T then ENNReal.ofReal (M.r (f k (w k)) (w k)) else 0) ∂(Pr p) =
      ∫⁻ w in W₀, e_T (w k) * u_k (w k) ∂(Pr p) := by
    rw [← lintegral_indicator hW₀_meas]
    refine lintegral_congr_ae (h_ae_nonneg.mono fun w hw => ?_)
    have hphi_nonneg : 0 ≤ M.phi (f k (w k)) (M.T - (w k).1) (w k).2 :=
      mul_nonneg hw (Real.exp_pos _).le
    dsimp only
    by_cases hwk : (w k).1 ≤ M.T
    · have hwk' : w ∈ W₀ := ⟨hwk, hw⟩
      rw [if_pos hwk, Set.indicator_of_mem hwk']
      dsimp [JumpMarket.r, e_T, u_k]
      rw [max_eq_right hphi_nonneg, ENNReal.ofReal_mul (Real.exp_pos _).le]
    · have hwk' : w ∉ W₀ := fun h => hwk h.1
      rw [if_neg hwk, Set.indicator_of_notMem hwk']
  rw [h_lhs_eq, h_rhs_eq, ← h_lhs_mu, ← h_rhs_mu, h_int_mu]

lemma jump_gt_mono_of_no_drop {M : JumpMarket d} {w : ℕ → ℝ × ℝ}
    (h_no_drop : ∀ m : ℕ, ¬ (M.T < (w m).1 ∧ (w (m + 1)).1 ≤ M.T))
    {m : ℕ} (hm : M.T < (w m).1) :
    ∀ n : ℕ, m ≤ n → M.T < (w n).1 := by
  intro n hmn
  induction hmn with
  | refl => exact hm
  | @step j _ ih =>
      by_contra hle
      exact h_no_drop j ⟨ih, not_lt.mp hle⟩

lemma terminalWealth_ae_eq_tsum (M : JumpMarket d) (f : ℕ → ℝ × ℝ → Control d)
    (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ)) (hLaw : M.IsChainLaw (ofMarkov f) Pr)
    {p : ℝ × ℝ} (hpT : p.1 ≤ M.T) :
    ∀ᵐ w ∂(Pr p),
      ENNReal.ofReal (M.U (M.terminalWealth (ofMarkov f) w)) =
        ∑' k : ℕ, ({w' : ℕ → ℝ × ℝ | (w' k).1 ≤ M.T ∧ M.T < (w' (k + 1)).1}).indicator
          (fun w' => ENNReal.ofReal (M.U (M.phi (f k (w' k)) (M.T - (w' k).1) (w' k).2))) w := by
  have hw0 : ∀ᵐ w ∂(Pr p), w 0 = p := by
    rw [ae_iff]
    exact pr_w0_ne_eq_zero M (ofMarkov f) Pr hLaw p
  have hall : ∀ᵐ w ∂(Pr p), ∃ n : ℕ, M.T < (w n).1 := by
    rw [ae_iff]
    simpa [not_exists, not_lt] using pr_all_le_T_eq_zero M (ofMarkov f) Pr hLaw p
  have hnodrop : ∀ᵐ w ∂(Pr p), ∀ m : ℕ, ¬ (M.T < (w m).1 ∧ (w (m + 1)).1 ≤ M.T) := by
    rw [ae_all_iff]
    intro m
    rw [ae_iff]
    simpa using pr_jump_drop_eq_zero M (ofMarkov f) Pr hLaw p m
  filter_upwards [hw0, hall, hnodrop] with w hw0 hall hnodrop
  classical
  have h_ex : ∃ k : ℕ, (w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1 := by
    let n₀ := Nat.find hall
    have hn₀ : M.T < (w n₀).1 := Nat.find_spec hall
    have hn₀_ne : n₀ ≠ 0 := by
      intro h0
      rw [h0, hw0] at hn₀
      exact hn₀.not_ge hpT
    obtain ⟨k₀, hk₀⟩ := Nat.exists_eq_succ_of_ne_zero hn₀_ne
    refine ⟨k₀, not_lt.mp (Nat.find_min hall (by omega)), ?_⟩
    simpa [hk₀] using hn₀
  have h_uniq : ∀ k : ℕ, ((w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1) → k = h_ex.choose := by
    intro k hk
    have hch := h_ex.choose_spec
    rcases lt_trichotomy k h_ex.choose with hlt | rfl | hgt
    · have hgt_T := jump_gt_mono_of_no_drop hnodrop hk.2 h_ex.choose hlt
      exact False.elim (hgt_T.not_ge hch.1)
    · rfl
    · have hgt_T := jump_gt_mono_of_no_drop hnodrop hch.2 k hgt
      exact False.elim (hgt_T.not_ge hk.1)
  let kstar := h_ex.choose
  have hkstar : (w kstar).1 ≤ M.T ∧ M.T < (w (kstar + 1)).1 := h_ex.choose_spec
  rw [tsum_eq_single kstar (fun k hk => by
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hk (h_uniq k hmem))]
  have hmem : w ∈ {w' : ℕ → ℝ × ℝ | (w' kstar).1 ≤ M.T ∧ M.T < (w' (kstar + 1)).1} := hkstar
  rw [Set.indicator_of_mem hmem]
  unfold JumpMarket.terminalWealth
  rw [dif_pos h_ex]
  rfl

end SolTheorem931

/-- **Theorem 9.3.1** (p. 283). a) For a Markov portfolio strategy `π = (π_t) = (f_n)`,
`V_π(t,x) = J_{∞(f_n)}(t,x)` on `E`. b) `V = J_∞`: the supremum of `V_π` over all
(history-dependent) strategies equals the value of the embedded discrete-time model. `Pr` is the
family of chain laws `ℙ^π_{tx}` (one for each strategy), pinned by `IsChainLaw`. -/
theorem solution {d : ℕ} (M : JumpMarket d)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) :
    (∀ f : ℕ → ℝ × ℝ → Control d, IsMarkovStrategy f →
      ∀ p ∈ M.E, M.Vpi (ofMarkov f) (Pr (ofMarkov f)) p = M.Jinfpi f (Pr (ofMarkov f)) p) ∧
    (∀ p ∈ M.E, M.V Pr p = M.Jinf Pr p) := by
  open SolTheorem931 in
  refine ⟨fun f hf p hp => ?_, ?_⟩
  · unfold JumpMarket.Vpi JumpMarket.Jinfpi
    let A : ℕ → Set (ℕ → ℝ × ℝ) := fun k => {w | (w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1}
    have hA_meas : ∀ k : ℕ, MeasurableSet (A k) := fun k =>
      (measurableSet_le (measurable_coord_fst k) measurable_const).inter
        (measurableSet_lt measurable_const (measurable_coord_fst (k + 1)))
    have hU_max_cont : Continuous (fun x : ℝ => M.U (max 0 x)) :=
      M.U_cont.comp_continuous (continuous_const.max continuous_id) (fun x => le_max_left 0 x)
    have h_ae_nonneg : ∀ k : ℕ, ∀ᵐ w ∂(Pr (ofMarkov f) p), 0 ≤ (w k).2 := by
      intro k
      rw [ae_iff]
      simpa [not_le] using pr_wealth_neg_eq_zero M (ofMarkov f) (Pr (ofMarkov f)) (hPr (ofMarkov f)) hp.2 k
    have h_term_aemeas : ∀ k : ℕ, AEMeasurable
        (fun w : ℕ → ℝ × ℝ => (A k).indicator
          (fun w' => ENNReal.ofReal (M.U (M.phi (f k (w' k)) (M.T - (w' k).1) (w' k).2))) w)
        (Pr (ofMarkov f) p) := by
      intro k
      have hm : Measurable (fun w : ℕ → ℝ × ℝ =>
          (A k).indicator (fun w' => ENNReal.ofReal (M.U (max 0 (M.phi (f k (w' k)) (M.T - (w' k).1) (w' k).2)))) w) := by
        refine (ENNReal.measurable_ofReal.comp (hU_max_cont.measurable.comp ?_)).indicator (hA_meas k)
        exact (measurable_phi_joint M).comp
          ((((hf k).comp (measurable_pi_apply k)).prodMk
            (measurable_const.sub (measurable_fst.comp (measurable_pi_apply k)))).prodMk
            (measurable_snd.comp (measurable_pi_apply k)))
      refine hm.aemeasurable.congr ((h_ae_nonneg k).mono fun w hw => ?_)
      have hphi_nonneg : 0 ≤ M.phi (f k (w k)) (M.T - (w k).1) (w k).2 :=
        mul_nonneg hw (Real.exp_pos _).le
      by_cases hwk : w ∈ A k <;> simp [hwk, max_eq_right hphi_nonneg]
    have h_rhs_aemeas : ∀ k : ℕ, AEMeasurable
        (fun w : ℕ → ℝ × ℝ => if (w k).1 ≤ M.T then ENNReal.ofReal (M.r (f k (w k)) (w k)) else 0)
        (Pr (ofMarkov f) p) := by
      intro k
      have hm : Measurable (fun w : ℕ → ℝ × ℝ =>
          if (w k).1 ≤ M.T then
            ENNReal.ofReal (Real.exp (-M.lam * (M.T - (w k).1)) * M.U (max 0 (M.phi (f k (w k)) (M.T - (w k).1) (w k).2)))
          else 0) := by
        refine Measurable.ite (measurableSet_le (measurable_fst.comp (measurable_pi_apply k)) measurable_const) ?_ measurable_const
        refine ENNReal.measurable_ofReal.comp ((Real.continuous_exp.measurable.comp
          (measurable_const.mul (measurable_const.sub (measurable_fst.comp (measurable_pi_apply k))))).mul ?_)
        refine hU_max_cont.measurable.comp ((measurable_phi_joint M).comp
          ((((hf k).comp (measurable_pi_apply k)).prodMk
            (measurable_const.sub (measurable_fst.comp (measurable_pi_apply k)))).prodMk
            (measurable_snd.comp (measurable_pi_apply k))))
      refine hm.aemeasurable.congr ((h_ae_nonneg k).mono fun w hw => ?_)
      have hphi_nonneg : 0 ≤ M.phi (f k (w k)) (M.T - (w k).1) (w k).2 :=
        mul_nonneg hw (Real.exp_pos _).le
      by_cases hwk : (w k).1 ≤ M.T <;> simp [hwk, JumpMarket.r, max_eq_right hphi_nonneg]
    rw [lintegral_congr_ae (terminalWealth_ae_eq_tsum M f (Pr (ofMarkov f)) (hPr (ofMarkov f)) hp.1.2),
        lintegral_tsum h_term_aemeas, lintegral_tsum h_rhs_aemeas]
    congr 1
    ext k
    rw [lintegral_indicator (hA_meas k)]
    exact stage_reward_lintegral_eq M f hf (Pr (ofMarkov f)) (hPr (ofMarkov f)) hp.2 k
  · obtain ⟨gamma0, _, hprop⟩ := (proposition_9_3_2 M).2.2
    obtain ⟨halpha_lt, hb⟩ := hprop gamma0 le_rfl
    have hb_max := isBoundingFunction_max_zero M (M.bfun gamma0) (M.alphaGamma gamma0) hb
    have halpha_max_lt : max 0 (M.alphaGamma gamma0) < 1 := max_lt zero_lt_one halpha_lt
    obtain ⟨v, -, hV, hJinf, -⟩ :=
      theorem_9_3_4 M gamma0 (max 0 (M.alphaGamma gamma0)) hb_max (le_max_left _ _) halpha_max_lt Pr hPr
    intro p hp
    rw [hV p hp, hJinf p hp]
