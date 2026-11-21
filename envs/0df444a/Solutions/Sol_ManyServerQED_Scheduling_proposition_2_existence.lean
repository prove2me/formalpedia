-- Prove2me | solution 1 for ManyServerQED.Scheduling.proposition_2_existence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:32:30.971758+00:00
-- url     : https://prove2.me/submissions/8d7bcb1a-b00e-486a-b2fd-eaca7441346a

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Aux_P2E

open ManyServerQED.Scheduling

lemma simplex_abs_le_one {k : ℕ} {u : Fin k → ℝ} (hu : u ∈ stdSimplex ℝ (Fin k)) (i : Fin k) :
    |u i| ≤ 1 := by
  have h0 : 0 ≤ u i := hu.1 i
  have h1 : u i ≤ 1 := by
    have h := Finset.single_le_sum (f := u) (fun j _ => hu.1 j) (Finset.mem_univ i)
    rw [hu.2] at h
    exact h
  rw [abs_of_nonneg h0]
  exact h1

lemma drift_lip {k : ℕ} (D : DiffusionData k) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x y u : Fin k → ℝ, u ∈ stdSimplex ℝ (Fin k) →
      ‖drift D x u - drift D y u‖ ≤ K * ‖x - y‖ := by
  have hK0 : 0 ≤ ∑ i, (|D.mu i - D.theta i| * (k : ℝ) + D.mu i) :=
    Finset.sum_nonneg (fun i _ =>
      add_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (D.mu_pos i).le)
  refine ⟨∑ i, (|D.mu i - D.theta i| * (k : ℝ) + D.mu i), hK0, ?_⟩
  intro x y u hu
  have hsum : |∑ j, x j - ∑ j, y j| ≤ (k : ℝ) * ‖x - y‖ := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ j, (x j - y j)| ≤ ∑ j, |x j - y j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, ‖x - y‖ := by
          apply Finset.sum_le_sum
          intro j _
          have h := norm_le_pi_norm (x - y) j
          rw [Pi.sub_apply, Real.norm_eq_abs] at h
          exact h
      _ = (k : ℝ) * ‖x - y‖ := by simp
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hK0 (norm_nonneg _))).2 (fun i => ?_)
  have e : (drift D x u - drift D y u) i =
      (D.mu i - D.theta i) * (max (∑ j, x j) 0 - max (∑ j, y j) 0) * u i
        - D.mu i * (x i - y i) := by
    simp only [drift, Pi.sub_apply]
    ring
  rw [e, Real.norm_eq_abs]
  have hm : |max (∑ j, x j) 0 - max (∑ j, y j) 0| ≤ (k : ℝ) * ‖x - y‖ :=
    (abs_max_sub_max_le_abs _ _ _).trans hsum
  have hu1 := simplex_abs_le_one hu i
  have hxi : |x i - y i| ≤ ‖x - y‖ := by
    have h := norm_le_pi_norm (x - y) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact h
  have hA : |(D.mu i - D.theta i) * (max (∑ j, x j) 0 - max (∑ j, y j) 0) * u i| ≤
      |D.mu i - D.theta i| * ((k : ℝ) * ‖x - y‖) := by
    rw [abs_mul, abs_mul]
    calc |D.mu i - D.theta i| * |max (∑ j, x j) 0 - max (∑ j, y j) 0| * |u i|
        ≤ |D.mu i - D.theta i| * ((k : ℝ) * ‖x - y‖) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm (abs_nonneg _)) hu1 (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))
      _ = |D.mu i - D.theta i| * ((k : ℝ) * ‖x - y‖) := mul_one _
  have hB : |D.mu i * (x i - y i)| ≤ D.mu i * ‖x - y‖ := by
    rw [abs_mul, abs_of_pos (D.mu_pos i)]
    exact mul_le_mul_of_nonneg_left hxi (D.mu_pos i).le
  have hle : (|D.mu i - D.theta i| * (k : ℝ) + D.mu i) ≤
      ∑ i, (|D.mu i - D.theta i| * (k : ℝ) + D.mu i) :=
    Finset.single_le_sum (f := fun i => |D.mu i - D.theta i| * (k : ℝ) + D.mu i)
      (fun j _ => add_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (D.mu_pos j).le)
      (Finset.mem_univ i)
  obtain ⟨a1, a2⟩ := abs_le.1 hA
  obtain ⟨b1, b2⟩ := abs_le.1 hB
  calc |(D.mu i - D.theta i) * (max (∑ j, x j) 0 - max (∑ j, y j) 0) * u i
        - D.mu i * (x i - y i)|
      ≤ |D.mu i - D.theta i| * ((k : ℝ) * ‖x - y‖) + D.mu i * ‖x - y‖ := by
        rw [abs_le]
        constructor <;> linarith
    _ = (|D.mu i - D.theta i| * (k : ℝ) + D.mu i) * ‖x - y‖ := by ring
    _ ≤ (∑ i, (|D.mu i - D.theta i| * (k : ℝ) + D.mu i)) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)

lemma drift_zero {k : ℕ} (D : DiffusionData k) (u : Fin k → ℝ) : drift D 0 u = D.ell := by
  funext i
  simp [drift]

lemma drift_bound {k : ℕ} (D : DiffusionData k) (K : ℝ)
    (hK : ∀ x y u : Fin k → ℝ, u ∈ stdSimplex ℝ (Fin k) →
      ‖drift D x u - drift D y u‖ ≤ K * ‖x - y‖)
    (z u : Fin k → ℝ) (hu : u ∈ stdSimplex ℝ (Fin k)) :
    ‖drift D z u‖ ≤ ‖D.ell‖ + K * ‖z‖ := by
  have h := hK z 0 u hu
  rw [drift_zero, sub_zero] at h
  have h2 : ‖drift D z u‖ ≤ ‖drift D z u - D.ell‖ + ‖D.ell‖ := by
    calc ‖drift D z u‖ = ‖(drift D z u - D.ell) + D.ell‖ := by rw [sub_add_cancel]
      _ ≤ ‖drift D z u - D.ell‖ + ‖D.ell‖ := norm_add_le _ _
  linarith

lemma drift_cont {k : ℕ} (D : DiffusionData k) :
    Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) => drift D p.1 p.2) := by
  have h1 : Continuous fun p : (Fin k → ℝ) × (Fin k → ℝ) => ∑ j, p.1 j :=
    continuous_finset_sum _ (fun j _ => (continuous_apply j).comp continuous_fst)
  refine continuous_pi (fun i => ?_)
  simp only [drift]
  first
  | fun_prop
  | exact ((continuous_const.add ((continuous_const.mul (h1.max continuous_const)).mul
      ((continuous_apply i).comp continuous_snd))).sub
      (continuous_const.mul ((continuous_apply i).comp continuous_fst)))

lemma u_meas {k : ℕ} (π : AdmissibleSystem k) (ω : π.Ω) :
    Measurable (fun t : ℝ≥0 => π.u t ω) := by
  have hv : ∀ N : ℕ, Measurable (fun t : ℝ≥0 => π.u (min t (N : ℝ≥0)) ω) := by
    intro N
    have hφ : @Measurable ℝ≥0 (Set.Iic (N : ℝ≥0) × π.Ω) _
        (MeasurableSpace.prod inferInstance (π.F (N : ℝ≥0)))
        (fun t : ℝ≥0 => ((⟨min t (N : ℝ≥0), Set.mem_Iic.mpr (min_le_right _ _)⟩ :
          Set.Iic (N : ℝ≥0)), ω)) :=
      Measurable.prodMk ((continuous_id.min continuous_const).measurable.subtype_mk)
        measurable_const
    exact ((π.u_prog (N : ℝ≥0)).comp_measurable hφ).measurable
  refine measurable_of_tendsto_metrizable hv (tendsto_pi_nhds.2 (fun t => ?_))
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈t⌉₊) (fun N hN => ?_)
  have htN : t ≤ (N : ℝ≥0) := (Nat.le_ceil t).trans (Nat.cast_le.2 hN)
  simp only [min_eq_left htN]

lemma integOn {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (Z : ℝ≥0 → Fin k → ℝ)
    (hZ : Continuous Z) (ω : π.Ω) (a b : ℝ) :
    IntegrableOn (fun s : ℝ => drift D (Z s.toNNReal) (π.u s.toNNReal ω)) (Set.Icc a b) := by
  obtain ⟨K, hK0, hK⟩ := drift_lip D
  have hZ' : Continuous fun s : ℝ => Z s.toNNReal := hZ.comp continuous_real_toNNReal
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hZ'.continuousOn
  have hmeas : Measurable fun s : ℝ => drift D (Z s.toNNReal) (π.u s.toNNReal ω) :=
    (drift_cont D).measurable.comp
      (hZ'.measurable.prodMk ((u_meas π ω).comp measurable_real_toNNReal))
  refine Measure.integrableOn_of_bounded (M := ‖D.ell‖ + K * C) measure_Icc_lt_top.ne
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (fun s hs => ?_))
  have h1 := drift_bound D K hK (Z s.toNNReal) (π.u s.toNNReal ω) (π.u_mem _ _)
  have h3 : ‖Z s.toNNReal‖ ≤ C := hC s hs
  have h2 : K * ‖Z s.toNNReal‖ ≤ K * C := mul_le_mul_of_nonneg_left h3 hK0
  linarith

lemma intInt {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (Z : ℝ≥0 → Fin k → ℝ)
    (hZ : Continuous Z) (ω : π.Ω) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => drift D (Z s.toNNReal) (π.u s.toNNReal ω)) volume a b :=
  ⟨(integOn D π Z hZ ω a b).mono_set Set.Ioc_subset_Icc_self,
    (integOn D π Z hZ ω b a).mono_set Set.Ioc_subset_Icc_self⟩

def goodSet {k : ℕ} (π : AdmissibleSystem k) : Set π.Ω :=
  {ω | ∀ i, Continuous (fun t => π.W t ω i)}

noncomputable def Wm {k : ℕ} (π : AdmissibleSystem k) (t : ℝ≥0) (ω : π.Ω) : Fin k → ℝ :=
  (goodSet π).indicator (fun ω' => π.W t ω') ω

noncomputable def Bp {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ)
    (t : ℝ≥0) (ω : π.Ω) : Fin k → ℝ :=
  x + (fun i => D.r i * Wm π t ω i)

noncomputable def Yp {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ) :
    ℕ → ℝ≥0 → π.Ω → (Fin k → ℝ)
  | 0 => fun t ω => Bp D π x t ω
  | n + 1 => fun t ω => Bp D π x t ω +
      ∫ s in (0 : ℝ)..(t : ℝ), drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)

lemma Yp_succ_apply {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : π.Ω) :
    Yp D π x (n + 1) t ω = Bp D π x t ω +
      ∫ s in (0 : ℝ)..(t : ℝ), drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω) := rfl

lemma Yp_succ_fun {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ)
    (n : ℕ) (t : ℝ≥0) :
    Yp D π x (n + 1) t = fun ω => Bp D π x t ω +
      ∫ s in (0 : ℝ)..(t : ℝ), drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω) := rfl

noncomputable def Xl {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ)
    (t : ℝ≥0) (ω : π.Ω) : Fin k → ℝ :=
  limUnder atTop (fun n => Yp D π x n t ω)

lemma Wm_cont {k : ℕ} (π : AdmissibleSystem k) (ω : π.Ω) : Continuous (fun t => Wm π t ω) := by
  by_cases h : ω ∈ goodSet π
  · simp only [Wm, Set.indicator_of_mem h]
    exact continuous_pi h
  · simp only [Wm, Set.indicator_of_notMem h]
    exact continuous_const

lemma good_meas {k : ℕ} (π : AdmissibleSystem k) : MeasurableSet[π.F 0] (goodSet π) := by
  have hae : ∀ᵐ ω ∂π.P, ∀ i, Continuous (fun t => π.W t ω i) :=
    ae_all_iff.2 (fun i => (π.W_bm.brownian i).cont)
  have hnull : π.P (goodSet π)ᶜ = 0 := ae_iff.1 hae
  exact (π.null_mem _ hnull).of_compl

lemma Wm_meas {k : ℕ} (π : AdmissibleSystem k) (t : ℝ≥0) : Measurable[π.F t] (Wm π t) :=
  (π.W_bm.adapted t).indicator (π.F.mono ((zero_le : (0:ℝ≥0) ≤ t)) _ (good_meas π))

lemma Bp_cont {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ)
    (ω : π.Ω) : Continuous (fun t => Bp D π x t ω) := by
  show Continuous fun t => x + (fun i => D.r i * Wm π t ω i)
  exact continuous_const.add (continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (Wm_cont π ω)))

lemma Bp_meas {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ)
    (t : ℝ≥0) : Measurable[π.F t] (Bp D π x t) := by
  have hc : Continuous fun w : Fin k → ℝ => x + (fun i => D.r i * w i) :=
    continuous_const.add (continuous_pi fun i => continuous_const.mul (continuous_apply i))
  exact hc.measurable.comp (Wm_meas π t)

lemma sm_integral {k : ℕ} {Ω : Type*} (m : MeasurableSpace Ω) (μ : Measure ℝ) [SFinite μ]
    (f : ℝ × Ω → (Fin k → ℝ))
    (hf : StronglyMeasurable[MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ) m] f) :
    StronglyMeasurable[m] (fun ω => ∫ s, f (s, ω) ∂μ) := by
  letI := m
  exact hf.integral_prod_left'

lemma Yp_props {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ)
    (n : ℕ) : (∀ ω, Continuous fun t => Yp D π x n t ω) ∧
      ∀ t, StronglyMeasurable[π.F t] (Yp D π x n t) := by
  induction n with
  | zero => exact ⟨fun ω => Bp_cont D π x ω, fun t => (Bp_meas D π x t).stronglyMeasurable⟩
  | succ n ih =>
    obtain ⟨hc, hm⟩ := ih
    refine ⟨fun ω => ?_, fun t => ?_⟩
    · show Continuous fun t : ℝ≥0 => Bp D π x t ω +
        ∫ s in (0 : ℝ)..(t : ℝ), drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)
      exact (Bp_cont D π x ω).add ((intervalIntegral.continuous_primitive
        (fun a b => intInt D π (fun t => Yp D π x n t ω) (hc ω) ω a b) 0).comp
          NNReal.continuous_coe)
    · have hYp : IsStronglyProgressive π.F (Yp D π x n) :=
        StronglyAdapted.isStronglyProgressive_of_continuous hm hc
      have hφ : @Measurable (ℝ × π.Ω) (Set.Iic t × π.Ω)
          (MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ) (π.F t))
          (MeasurableSpace.prod inferInstance (π.F t))
          (fun q : ℝ × π.Ω => ((⟨min q.1.toNNReal t, Set.mem_Iic.mpr (min_le_right _ _)⟩ :
            Set.Iic t), q.2)) := by
        refine Measurable.prodMk ?_ measurable_snd
        exact ((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk
      have hYj : StronglyMeasurable[MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ) (π.F t)]
          (fun q : ℝ × π.Ω => Yp D π x n (min q.1.toNNReal t) q.2) :=
        (hYp t).comp_measurable hφ
      have huj : StronglyMeasurable[MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ) (π.F t)]
          (fun q : ℝ × π.Ω => π.u (min q.1.toNNReal t) q.2) :=
        (π.u_prog t).comp_measurable hφ
      have hH : StronglyMeasurable[MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ) (π.F t)]
          (fun q : ℝ × π.Ω => drift D (Yp D π x n (min q.1.toNNReal t) q.2)
            (π.u (min q.1.toNNReal t) q.2)) :=
        (drift_cont D).comp_stronglyMeasurable (hYj.prodMk huj)
      have hmeasI := sm_integral (π.F t) (volume.restrict (Set.Ioc (0 : ℝ) t)) _ hH
      have hint : (fun ω => ∫ s in (0 : ℝ)..(t : ℝ),
            drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)) =
          fun ω => ∫ s, drift D (Yp D π x n (min s.toNNReal t) ω) (π.u (min s.toNNReal t) ω)
            ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
        funext ω
        rw [intervalIntegral.integral_of_le t.coe_nonneg]
        refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
        have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
        simp only [min_eq_left hst]
      have h2 : StronglyMeasurable[π.F t] (fun ω => ∫ s in (0 : ℝ)..(t : ℝ),
          drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)) := by
        rw [hint]
        exact hmeasI
      rw [Yp_succ_fun]
      exact (Bp_meas D π x t).stronglyMeasurable.add h2

lemma picard {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x y u : Fin k → ℝ, u ∈ stdSimplex ℝ (Fin k) →
      ‖drift D x u - drift D y u‖ ≤ K * ‖x - y‖)
    (ω : π.Ω) (T : ℝ≥0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ T →
      ‖Yp D π x (n + 1) t ω - Yp D π x n t ω‖ ≤
        M * (K * (t : ℝ)) ^ n / (Nat.factorial n : ℝ) := by
  have hc1 : Continuous fun t => Yp D π x 1 t ω - Yp D π x 0 t ω :=
    ((Yp_props D π x 1).1 ω).sub ((Yp_props D π x 0).1 ω)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    hc1.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, (zero_le : (0:ℝ≥0) ≤ T)⟩)
  refine ⟨M, hM0, fun n => ?_⟩
  induction n with
  | zero =>
    intro t ht
    have h := hM t ⟨(zero_le : (0:ℝ≥0) ≤ t), ht⟩
    simpa using h
  | succ n ih =>
    intro t ht
    have hi1 : IntervalIntegrable
        (fun s : ℝ => drift D (Yp D π x (n + 1) s.toNNReal ω) (π.u s.toNNReal ω)) volume 0 t :=
      intInt D π (fun t => Yp D π x (n + 1) t ω) ((Yp_props D π x (n + 1)).1 ω) ω 0 t
    have hi0 : IntervalIntegrable
        (fun s : ℝ => drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)) volume 0 t :=
      intInt D π (fun t => Yp D π x n t ω) ((Yp_props D π x n).1 ω) ω 0 t
    have e : Yp D π x (n + 1 + 1) t ω - Yp D π x (n + 1) t ω =
        ∫ s in (0 : ℝ)..(t : ℝ), (drift D (Yp D π x (n + 1) s.toNNReal ω) (π.u s.toNNReal ω) -
          drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)) := by
      rw [intervalIntegral.integral_sub hi1 hi0, Yp_succ_apply D π x (n + 1) t ω,
        Yp_succ_apply D π x n t ω]
      abel
    rw [e]
    have hbound : Continuous fun s : ℝ =>
        K * (M * (K * s) ^ n / (Nat.factorial n : ℝ)) := by fun_prop
    calc ‖∫ s in (0 : ℝ)..(t : ℝ),
          (drift D (Yp D π x (n + 1) s.toNNReal ω) (π.u s.toNNReal ω) -
            drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω))‖
        ≤ ∫ s in (0 : ℝ)..(t : ℝ), K * (M * (K * s) ^ n / (Nat.factorial n : ℝ)) := by
          refine intervalIntegral.norm_integral_le_of_norm_le t.coe_nonneg
            (Eventually.of_forall (fun s hs => ?_)) (hbound.intervalIntegrable 0 t)
          have hs0 : 0 ≤ s := hs.1.le
          have hsT : s.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe.2 hs.2).trans ht
          have h1 := hK (Yp D π x (n + 1) s.toNNReal ω) (Yp D π x n s.toNNReal ω)
            (π.u s.toNNReal ω) (π.u_mem _ _)
          have h2 := ih s.toNNReal hsT
          rw [Real.coe_toNNReal s hs0] at h2
          calc ‖drift D (Yp D π x (n + 1) s.toNNReal ω) (π.u s.toNNReal ω) -
                drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)‖
              ≤ K * ‖Yp D π x (n + 1) s.toNNReal ω - Yp D π x n s.toNNReal ω‖ := h1
            _ ≤ K * (M * (K * s) ^ n / (Nat.factorial n : ℝ)) :=
                mul_le_mul_of_nonneg_left h2 hK0
      _ = M * (K * (t : ℝ)) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
          have hfun : (fun s : ℝ => K * (M * (K * s) ^ n / (Nat.factorial n : ℝ))) =
              fun s => (K * M * K ^ n / (Nat.factorial n : ℝ)) * s ^ n := by
            funext s
            ring
          rw [hfun, intervalIntegral.integral_const_mul, integral_pow,
            zero_pow (show n + 1 ≠ 0 by omega), sub_zero, Nat.factorial_succ, Nat.cast_mul,
            Nat.cast_succ]
          have hf : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
          have hn : (n : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
          rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hf hn) (mul_ne_zero hn hf)]
          ring

lemma convY {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x y u : Fin k → ℝ, u ∈ stdSimplex ℝ (Fin k) →
      ‖drift D x u - drift D y u‖ ≤ K * ‖x - y‖)
    (ω : π.Ω) (T : ℝ≥0) : ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ T →
      Tendsto (fun m => Yp D π x m t ω) atTop (𝓝 (Xl D π x t ω)) ∧
        ‖Yp D π x n t ω - Xl D π x t ω‖ ≤ e n := by
  obtain ⟨M, hM0, hM⟩ := picard D π x hK0 hK ω T
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun m => M * ((K * (T : ℝ)) ^ m / (Nat.factorial m : ℝ)) :=
    ⟨_, rfl⟩
  have hsum : Summable a := by
    rw [ha]
    exact (Real.summable_pow_div_factorial (K * (T : ℝ))).mul_left M
  refine ⟨fun n => ∑' m, a (n + m), ?_, ?_⟩
  · have h : (fun n => ∑' m, a (n + m)) = fun n => ∑' m, a (m + n) := by
      funext n
      exact tsum_congr (fun m => by rw [Nat.add_comm])
    rw [h]
    exact tendsto_sum_nat_add a
  · intro n t ht
    have hd : ∀ m : ℕ, dist (Yp D π x m t ω) (Yp D π x m.succ t ω) ≤ a m := by
      intro m
      rw [dist_eq_norm, norm_sub_rev]
      have hpow : (K * (t : ℝ)) ^ m ≤ (K * (T : ℝ)) ^ m :=
        pow_le_pow_left₀ (mul_nonneg hK0 t.coe_nonneg)
          (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) hK0) m
      rw [ha]
      calc ‖Yp D π x m.succ t ω - Yp D π x m t ω‖
          ≤ M * (K * (t : ℝ)) ^ m / (Nat.factorial m : ℝ) := hM m t ht
        _ = M * ((K * (t : ℝ)) ^ m / (Nat.factorial m : ℝ)) := mul_div_assoc _ _ _
        _ ≤ M * ((K * (T : ℝ)) ^ m / (Nat.factorial m : ℝ)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)) hM0
    have hcs := cauchySeq_of_dist_le_of_summable a hd hsum
    have hlim : Tendsto (fun m => Yp D π x m t ω) atTop (𝓝 (Xl D π x t ω)) :=
      tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hcs)
    refine ⟨hlim, ?_⟩
    rw [← dist_eq_norm]
    exact dist_le_tsum_of_dist_le_of_tendsto a hd hsum hlim n

end Aux_P2E

open ManyServerQED.Scheduling Aux_P2E in
theorem solution {k : ℕ} [NeZero k] (D : DiffusionData k) (π : AdmissibleSystem k)
    (x : Fin k → ℝ) :
    ∃ X : ℝ≥0 → π.Ω → Fin k → ℝ, IsControlledProcess D π x X := by
  obtain ⟨K, hK0, hK⟩ := drift_lip D
  have hcont : ∀ ω, Continuous fun t => Xl D π x t ω := by
    intro ω
    refine continuous_iff_continuousAt.2 (fun t0 => ?_)
    obtain ⟨e, he, hb⟩ := convY D π x hK0 hK ω (t0 + 1)
    have hU : TendstoUniformlyOn (fun n t => Yp D π x n t ω) (fun t => Xl D π x t ω) atTop
        (Set.Iic (t0 + 1)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [he.eventually (eventually_lt_nhds hε)] with n hn
      intro t ht
      rw [dist_comm, dist_eq_norm]
      exact lt_of_le_of_lt (hb n t ht).2 hn
    have hco : ContinuousOn (fun t => Xl D π x t ω) (Set.Iic (t0 + 1)) :=
      hU.continuousOn
        (Eventually.of_forall (fun n => ((Yp_props D π x n).1 ω).continuousOn)).frequently
    exact hco.continuousAt (Iic_mem_nhds (lt_add_one t0))
  refine ⟨Xl D π x, ⟨hcont, ?_, ?_, ?_⟩⟩
  · intro t
    have hsm : StronglyMeasurable[π.F t] (Xl D π x t) := by
      refine stronglyMeasurable_of_tendsto atTop (fun n => (Yp_props D π x n).2 t) ?_
      refine tendsto_pi_nhds.2 (fun ω => ?_)
      obtain ⟨e, -, hb⟩ := convY D π x hK0 hK ω t
      exact (hb 0 t le_rfl).1
    exact hsm.measurable
  · exact Eventually.of_forall (fun ω t _ =>
      integOn D π (fun t => Xl D π x t ω) (hcont ω) ω 0 t)
  · have hae : ∀ᵐ ω ∂π.P, ∀ i, Continuous (fun t => π.W t ω i) :=
      ae_all_iff.2 (fun i => (π.W_bm.brownian i).cont)
    filter_upwards [hae] with ω hω
    intro t
    have hB : Bp D π x t ω = x + (fun i => D.r i * π.W t ω i) := by
      simp only [Bp, Wm, Set.indicator_of_mem (show ω ∈ goodSet π from hω)]
    obtain ⟨e, he, hb⟩ := convY D π x hK0 hK ω t
    have h1 : Tendsto (fun n => Yp D π x (n + 1) t ω) atTop (𝓝 (Xl D π x t ω)) :=
      (hb 0 t le_rfl).1.comp (tendsto_add_atTop_nat 1)
    have hlim0 : Tendsto (fun n => K * e n * |(t : ℝ) - 0|) atTop (𝓝 0) := by
      have h := (he.const_mul K).mul_const |(t : ℝ) - 0|
      rwa [mul_zero, zero_mul] at h
    have hI : Tendsto (fun n => ∫ s in (0 : ℝ)..(t : ℝ),
          drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)) atTop
        (𝓝 (∫ s in (0 : ℝ)..(t : ℝ), drift D (Xl D π x s.toNNReal ω) (π.u s.toNNReal ω))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
      show ‖(∫ s in (0 : ℝ)..(t : ℝ), drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)) -
          ∫ s in (0 : ℝ)..(t : ℝ), drift D (Xl D π x s.toNNReal ω) (π.u s.toNNReal ω)‖ ≤
        K * e n * |(t : ℝ) - 0|
      have hi1 : IntervalIntegrable
          (fun s : ℝ => drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω)) volume 0 t :=
        intInt D π (fun t => Yp D π x n t ω) ((Yp_props D π x n).1 ω) ω 0 t
      have hi2 : IntervalIntegrable
          (fun s : ℝ => drift D (Xl D π x s.toNNReal ω) (π.u s.toNNReal ω)) volume 0 t :=
        intInt D π (fun t => Xl D π x t ω) (hcont ω) ω 0 t
      rw [← intervalIntegral.integral_sub hi1 hi2]
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
      rw [Set.uIoc_of_le t.coe_nonneg] at hs
      have hsT : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
      calc ‖drift D (Yp D π x n s.toNNReal ω) (π.u s.toNNReal ω) -
            drift D (Xl D π x s.toNNReal ω) (π.u s.toNNReal ω)‖
          ≤ K * ‖Yp D π x n s.toNNReal ω - Xl D π x s.toNNReal ω‖ :=
            hK _ _ _ (π.u_mem _ _)
        _ ≤ K * e n := mul_le_mul_of_nonneg_left (hb n _ hsT).2 hK0
    have h2 : Tendsto (fun n => Yp D π x (n + 1) t ω) atTop
        (𝓝 (Bp D π x t ω + ∫ s in (0 : ℝ)..(t : ℝ),
          drift D (Xl D π x s.toNNReal ω) (π.u s.toNNReal ω))) :=
      hI.const_add (Bp D π x t ω)
    rw [← hB]
    exact tendsto_nhds_unique h1 h2
