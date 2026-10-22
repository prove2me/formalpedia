-- Prove2me | solution 1 for IncentiveAwarePricing.CORP.theorem_4_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-22T05:03:39.470813+00:00
-- url     : https://prove2.me/submissions/79f88186-bed0-44b7-b347-029d49807003

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model
import Definitions.Def_IncentiveAwarePricing_CORP_Play


open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

/-- uniform density on [-1,1] -/
noncomputable def fU : ℝ → ℝ := (Set.Icc (-1:ℝ) 1).indicator (fun _ => (1/2:ℝ))

noncomputable def Fx (z : ℝ) : ℝ := max 0 (min 1 ((z + 1) / 2))

lemma noiseCDF_fU (z : ℝ) : noiseCDF fU z = Fx z := by
  unfold noiseCDF fU Fx
  rw [integral_indicator_const _ measurableSet_Icc]
  simp only [smul_eq_mul]
  rw [measureReal_def, Measure.restrict_apply measurableSet_Icc]
  rcases le_or_gt z (-1) with h | h
  · have : Set.Icc (-1:ℝ) 1 ∩ Set.Iic z ⊆ {-1} := by
      intro t ⟨⟨h1, _⟩, h3⟩; simp only [Set.mem_Iic] at h3; simp; linarith
    have h0 : volume (Set.Icc (-1:ℝ) 1 ∩ Set.Iic z) = 0 :=
      measure_mono_null this (by simp)
    rw [h0]; simp; right; linarith
  · rcases le_or_gt z 1 with h' | h'
    · have : Set.Icc (-1:ℝ) 1 ∩ Set.Iic z = Set.Icc (-1) z := by
        ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]; constructor
        · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, c⟩
        · rintro ⟨a, c⟩; exact ⟨⟨a, by linarith⟩, c⟩
      rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
    · have : Set.Icc (-1:ℝ) 1 ∩ Set.Iic z = Set.Icc (-1) 1 := by
        ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]; constructor
        · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, b⟩
        · rintro ⟨a, b⟩; exact ⟨⟨a, b⟩, by linarith⟩
      rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
      rw [min_eq_left (by linarith), max_eq_right (by norm_num)]; norm_num

lemma noiseCDF_fU' : noiseCDF fU = Fx := funext noiseCDF_fU

lemma Fx_continuous : Continuous Fx := by
  unfold Fx; fun_prop

lemma Fx_eq_one {z : ℝ} (h : 1 ≤ z) : Fx z = 1 := by
  unfold Fx; rw [min_eq_left (by linarith)]; norm_num

lemma Fx_eq_zero {z : ℝ} (h : z ≤ -1) : Fx z = 0 := by
  unfold Fx; rw [max_eq_left]; apply min_le_of_right_le; linarith

lemma Fx_mid {z : ℝ} (h1 : -1 ≤ z) (h2 : z ≤ 1) : Fx z = (z+1)/2 := by
  unfold Fx; rw [min_eq_right (by linarith), max_eq_right (by linarith)]

lemma Fx_nonneg (z : ℝ) : 0 ≤ Fx z := le_max_left _ _
lemma Fx_le_one (z : ℝ) : Fx z ≤ 1 := max_le (by norm_num) (min_le_left _ _)

lemma noiseStanding_fU : NoiseStanding 1 fU where
  pos := by norm_num
  nonneg := by
    intro z; unfold fU; apply Set.indicator_nonneg; intros; norm_num
  zero_outside := by
    intro z hz; unfold fU; exact Set.indicator_of_notMem hz _
  continuousOn := by
    have : Set.EqOn fU (fun _ => (1/2:ℝ)) (Set.Icc (-1) 1) := by
      intro z hz; unfold fU; exact Set.indicator_of_mem hz _
    exact (continuousOn_const).congr this
  mass_one := by
    have : ∫ z in (-1:ℝ)..1, fU z = ∫ z in (-1:ℝ)..1, (1/2:ℝ) := by
      apply intervalIntegral.integral_congr
      intro z hz; rw [Set.uIcc_of_le (by norm_num)] at hz; unfold fU
      exact Set.indicator_of_mem hz _
    rw [this]; simp; norm_num
  mean_zero := by
    have : ∫ z in (-1:ℝ)..1, z * fU z = ∫ z in (-1:ℝ)..1, z * (1/2:ℝ) := by
      apply intervalIntegral.integral_congr
      intro z hz; rw [Set.uIcc_of_le (by norm_num)] at hz; unfold fU
      simp only [Set.indicator_of_mem hz]
    rw [this, intervalIntegral.integral_mul_const]; simp

lemma logConcave_affine (c s : ℝ) (hs : ∀ z ∈ Set.Icc (-1:ℝ) 1, 0 ≤ c + s * z)
    (g : ℝ → ℝ) (hg : ∀ z ∈ Set.Icc (-1:ℝ) 1, g z = c + s * z) :
    ConvexOptimization.LogConcaveOn (Set.Icc (-1:ℝ) 1) g := by
  refine ⟨fun x hx => by rw [hg x hx]; exact hs x hx, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ Set.Icc (-1:ℝ) 1 := (convex_Icc (-1:ℝ) 1) hx hy ha hb hab
  rw [hg x hx, hg y hy, hg _ hxy]
  have := Real.geom_mean_le_arith_mean2_weighted ha hb (hs x hx) (hs y hy) hab
  calc (c + s * x) ^ a * (c + s * y) ^ b ≤ a * (c + s * x) + b * (c + s * y) := this
    _ = c + s * (a • x + b • y) := by
      simp only [smul_eq_mul]
      have : b = 1 - a := by linarith
      subst this; ring

lemma assumption1_fU : Assumption1 1 fU := by
  refine ⟨?_, ?_⟩
  · rw [noiseCDF_fU']
    refine logConcave_affine (1/2) (1/2) ?_ Fx ?_
    · intro z hz; linarith [hz.1]
    · intro z hz; rw [Fx_mid hz.1 hz.2]; ring
  · rw [noiseCDF_fU']
    refine logConcave_affine (1/2) (-1/2) ?_ (fun z => 1 - Fx z) ?_
    · intro z hz; linarith [hz.2]
    · intro z hz; rw [Fx_mid hz.1 hz.2]; ring

end CorpCE


open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

noncomputable def resU (θ : ℝ) : ℝ :=
  if θ ≤ -1 then 100 else if θ ≤ 3 then (1 + θ) / 2 else θ - 1

lemma resU_measurable : Measurable resU := by
  unfold resU
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)

lemma obj_eq (θ y : ℝ) : reserveObjective fU θ y = y * (1 - Fx (y - θ)) := by
  simp [reserveObjective, noiseCDF_fU']

lemma one_sub_Fx (s : ℝ) : 1 - Fx s = max 0 (min 1 ((1 - s) / 2)) := by
  unfold Fx
  rcases le_or_gt s (-1) with h | h
  · rw [min_eq_right (a := (1:ℝ)) (by linarith), max_eq_left (by linarith),
      min_eq_left (by linarith), max_eq_right (by norm_num)]; norm_num
  · rcases le_or_gt s 1 with h' | h'
    · rw [min_eq_right (a := (1:ℝ)) (by linarith), max_eq_right (by linarith),
        min_eq_right (by linarith), max_eq_right (by linarith)]; ring
    · rw [min_eq_left (a := (1:ℝ)) (by linarith), max_eq_right (by norm_num),
        min_eq_right (by linarith), max_eq_left (by linarith)]; norm_num

lemma G_cases (s : ℝ) : (s ≤ -1 ∧ 1 - Fx s = 1) ∨ (-1 ≤ s ∧ s ≤ 1 ∧ 1 - Fx s = (1 - s) / 2)
    ∨ (1 ≤ s ∧ 1 - Fx s = 0) := by
  rcases le_or_gt s (-1) with h | h
  · left; exact ⟨h, by rw [Fx_eq_zero h]; norm_num⟩
  · rcases le_or_gt s 1 with h' | h'
    · right; left; exact ⟨h.le, h', by rw [Fx_mid h.le h']; ring⟩
    · right; right; exact ⟨h'.le, by rw [Fx_eq_one h'.le]; norm_num⟩

lemma isReserveRule_resU : IsReserveRule fU resU := by
  intro θ y _
  show reserveObjective fU θ y ≤ reserveObjective fU θ (resU θ)
  rw [obj_eq, obj_eq]
  unfold resU
  split_ifs with h1 h2
  · rw [show Fx (100 - θ) = 1 from Fx_eq_one (by linarith)]
    rcases G_cases (y - θ) with ⟨a, hh⟩ | ⟨a, b, hh⟩ | ⟨a, hh⟩ <;> rw [hh] <;> nlinarith
  · rw [show 1 - Fx ((1 + θ) / 2 - θ) = (1 + θ) / 4 by
      rw [Fx_mid (by linarith) (by linarith)]; ring]
    rcases G_cases (y - θ) with ⟨a, hh⟩ | ⟨a, b, hh⟩ | ⟨a, hh⟩ <;> rw [hh] <;>
      nlinarith [sq_nonneg (θ - 3), sq_nonneg (2*y - (1+θ))]
  · rw [show 1 - Fx (θ - 1 - θ) = 1 by rw [Fx_eq_zero (by linarith)]; norm_num]
    rcases G_cases (y - θ) with ⟨a, hh⟩ | ⟨a, b, hh⟩ | ⟨a, hh⟩ <;> rw [hh] <;> nlinarith

/-- the unit vector of `Ctx 1` -/
noncomputable def e1 : Ctx 1 := EuclideanSpace.single 0 1

lemma inner_single_single (a b : ℝ) :
    ⟪(EuclideanSpace.single 0 a : Ctx 1), EuclideanSpace.single 0 b⟫ = a * b := by
  simp [EuclideanSpace.inner_single_left]

lemma ctx1_eq (u : Ctx 1) : u = EuclideanSpace.single 0 (u 0) := by
  ext i; fin_cases i; simp

lemma norm_ctx1 (u : Ctx 1) : ‖u‖ = |u 0| := by
  conv_lhs => rw [ctx1_eq u]
  simp [PiLp.norm_single]

lemma featureLaw_dirac : FeatureLaw 1 (1/2) 2 (Measure.dirac e1) where
  isProb := inferInstance
  norm_le_one := by
    rw [ae_dirac_iff]
    · simp [e1, PiLp.norm_single]
    · exact measurableSet_le measurable_norm measurable_const
  lower := by
    intro u hu
    rw [integral_dirac]
    have h0 : u 0 ≠ 0 := by
      intro h; apply hu; rw [ctx1_eq u, h]; simp
    rw [norm_ctx1, ctx1_eq u, e1, inner_single_single]
    simp only [PiLp.single_apply, if_true, one_mul, sq_abs]
    have : 0 < u 0 ^ 2 := by positivity
    norm_num; linarith
  upper := by
    intro u
    rw [integral_dirac, norm_ctx1, ctx1_eq u, e1, inner_single_single]
    simp only [PiLp.single_apply, if_true, one_mul, sq_abs]
    have : 0 ≤ u 0 ^ 2 := by positivity
    norm_num; linarith

end CorpCE


open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

lemma nll_continuous : Continuous nll := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases lt_trichotomy p 0 with h | h | h
  · have : nll =ᶠ[𝓝 p] fun _ => ⊤ := by
      filter_upwards [Iio_mem_nhds h] with q hq
      simp [nll, le_of_lt (show q < 0 from hq)]
    exact (continuousAt_const).congr this.symm
  · subst h
    rw [ContinuousAt, show nll 0 = ⊤ by simp [nll]]
    rw [ENNReal.tendsto_nhds_top_iff_nnreal]
    intro x
    have hpos : 0 < Real.exp (-((x:ℝ) + 1)) := Real.exp_pos _
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hpos) hpos] with q hq
    by_cases hq0 : q ≤ 0
    · simp [nll, hq0]
    · push Not at hq0
      simp only [nll, not_le.mpr hq0, if_false]
      have : Real.log q < -((x:ℝ) + 1) := by
        rw [Real.log_lt_iff_lt_exp hq0]; exact hq.2
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  · have : nll =ᶠ[𝓝 p] fun q => ENNReal.ofReal (-Real.log q) := by
      filter_upwards [Ioi_mem_nhds h] with q hq
      simp [nll, not_le.mpr (show 0 < q from hq)]
    refine ContinuousAt.congr ?_ this.symm
    exact ENNReal.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log h.ne').neg)

lemma nll_measurable : Measurable nll := nll_continuous.measurable

lemma nll_one : nll 1 = 0 := by simp [nll]

lemma obsNLL_measurable {d : ℕ} (β : Ctx d) : Measurable (obsNLL fU β) := by
  unfold obsNLL
  have hF : Continuous (noiseCDF fU) := by rw [noiseCDF_fU']; exact Fx_continuous
  have h1 : Measurable fun o : Obs d => nll (1 - noiseCDF fU (o.2.1 - ⟪o.1, β⟫)) :=
    nll_measurable.comp (by fun_prop)
  have h2 : Measurable fun o : Obs d => nll (noiseCDF fU (o.2.1 - ⟪o.1, β⟫)) :=
    nll_measurable.comp (by fun_prop)
  refine Measurable.ite ?_ (Measurable.ite ?_ h1 h2) measurable_const
  · exact (measurableSet_singleton true).preimage (by fun_prop)
  · exact (measurableSet_singleton true).preimage (by fun_prop)

/-- the profile `t ↦ NLL(data, t e₁)` -/
noncomputable def phi {m : ℕ} (data : Fin m → Obs 1) (t : ℝ) : ℝ≥0∞ :=
  negLogLik fU data (EuclideanSpace.single 0 t)

lemma phi_continuous {m : ℕ} (data : Fin m → Obs 1) : Continuous (phi data) := by
  unfold phi negLogLik
  refine continuous_finsetSum _ fun j _ => ?_
  have hF : Continuous (noiseCDF fU) := by rw [noiseCDF_fU']; exact Fx_continuous
  have hin : Continuous fun t : ℝ => ⟪(data j).1, (EuclideanSpace.single 0 t : Ctx 1)⟫ := by
    have : (fun t : ℝ => ⟪(data j).1, (EuclideanSpace.single 0 t : Ctx 1)⟫) =
        fun t => t * (data j).1 0 := by
      funext t; simp [EuclideanSpace.inner_single_right]
    rw [this]; fun_prop
  unfold obsNLL
  split_ifs
  · exact nll_continuous.comp (continuous_const.sub (hF.comp (continuous_const.sub hin)))
  · exact nll_continuous.comp (hF.comp (continuous_const.sub hin))
  · exact continuous_const

lemma phi_measurable_data (m : ℕ) (t : ℝ) : Measurable fun data : Fin m → Obs 1 => phi data t := by
  unfold phi negLogLik
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (obsNLL_measurable _).comp (measurable_pi_apply j)

def Box : Set ℝ := Set.Icc (-10) 10

noncomputable def argminSet {m : ℕ} (data : Fin m → Obs 1) : Set ℝ :=
  {t | t ∈ Box ∧ ∀ s ∈ Box, phi data t ≤ phi data s}

lemma argminSet_nonempty {m : ℕ} (data : Fin m → Obs 1) : (argminSet data).Nonempty := by
  obtain ⟨t, ht, hmin⟩ := (isCompact_Icc (a := (-10:ℝ)) (b := 10)).exists_isMinOn
    (Set.nonempty_Icc.mpr (by norm_num)) (phi_continuous data).continuousOn
  exact ⟨t, ht, fun s hs => hmin hs⟩

lemma argminSet_closed {m : ℕ} (data : Fin m → Obs 1) : IsClosed (argminSet data) := by
  have : argminSet data = Box ∩ ⋂ s ∈ Box, {t | phi data t ≤ phi data s} := by
    ext t; simp [argminSet]
  rw [this]
  refine isClosed_Icc.inter (isClosed_biInter fun s _ => ?_)
  exact isClosed_le (phi_continuous data) continuous_const

noncomputable def aMin {m : ℕ} (data : Fin m → Obs 1) : ℝ := sInf (argminSet data)

lemma argminSet_bdd {m : ℕ} (data : Fin m → Obs 1) : BddBelow (argminSet data) :=
  ⟨-10, fun t ht => ht.1.1⟩

lemma aMin_mem {m : ℕ} (data : Fin m → Obs 1) : aMin data ∈ argminSet data :=
  (argminSet_closed data).csInf_mem (argminSet_nonempty data) (argminSet_bdd data)

lemma aMin_trap {m : ℕ} (data : Fin m → Obs 1) (h : phi data (-10) = 0) : aMin data = -10 := by
  have hmem : (-10:ℝ) ∈ argminSet data :=
    ⟨⟨le_refl _, by norm_num⟩, fun s _ => by rw [h]; exact bot_le⟩
  have hle : aMin data ≤ -10 := csInf_le (argminSet_bdd data) hmem
  have hge : -10 ≤ aMin data := (aMin_mem data).1.1
  linarith

noncomputable def estU : Estimator 1 1 := fun _ _ data => EuclideanSpace.single 0 (aMin data)

lemma isCORPEstimator_estU : IsCORPEstimator fU 10 estU := by
  intro e i data
  have hm := aMin_mem data
  constructor
  · simp only [estU, Metric.mem_closedBall, dist_zero_right, PiLp.norm_single,
      Real.norm_eq_abs]
    exact abs_le.mpr ⟨hm.1.1, hm.1.2⟩
  · intro β hβ
    simp only [Metric.mem_closedBall, dist_zero_right, norm_ctx1] at hβ
    have hb : β 0 ∈ Box := ⟨(abs_le.mp hβ).1, (abs_le.mp hβ).2⟩
    have := hm.2 _ hb
    simp only [estU]
    rw [ctx1_eq β]
    exact this

/-- `⨅` over an interval equals `⨅` over its rational points (for continuous functions). -/
lemma iInf_Icc_eq_rat (g : ℝ → ℝ≥0∞) (hg : Continuous g) {a b : ℝ} (hab : a < b) :
    (⨅ t ∈ Set.Icc a b, g t) = ⨅ q : ℚ, ⨅ (_ : (q:ℝ) ∈ Set.Icc a b), g q := by
  apply le_antisymm
  · exact le_iInf fun q => le_iInf fun hq => iInf₂_le (q:ℝ) hq
  · refine le_iInf₂ fun t ht => ?_
    set m := ⨅ q : ℚ, ⨅ (_ : (q:ℝ) ∈ Set.Icc a b), g q
    have hcl : IsClosed {t | m ≤ g t} := isClosed_le continuous_const hg
    have hsub : Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ) ⊆ {t | m ≤ g t} := by
      rintro _ ⟨hI, q, rfl⟩
      have hq : (q:ℝ) ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hI
      show m ≤ g q
      exact le_trans (iInf_le (fun q : ℚ => ⨅ (_ : (q:ℝ) ∈ Set.Icc a b), g q) q)
        (iInf_le (fun _ : (q:ℝ) ∈ Set.Icc a b => g q) hq)
    have hcl2 : Set.Icc a b ⊆ closure (Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ)) := by
      have h1 : Set.Ioo a b ⊆ closure (Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ)) :=
        Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
      have h2 := closure_mono h1
      rw [closure_Ioo hab.ne, closure_closure] at h2
      exact h2
    exact hcl.closure_subset_iff.mpr hsub (hcl2 ht)

lemma iInf_Icc_measurable (m : ℕ) {a b : ℝ} (hab : a < b) :
    Measurable fun data : Fin m → Obs 1 => ⨅ t ∈ Set.Icc a b, phi data t := by
  have : (fun data : Fin m → Obs 1 => ⨅ t ∈ Set.Icc a b, phi data t) =
      fun data => ⨅ q : ℚ, ⨅ (_ : (q:ℝ) ∈ Set.Icc a b), phi data q := by
    funext data; exact iInf_Icc_eq_rat _ (phi_continuous data) hab
  rw [this]
  refine Measurable.iInf fun q => Measurable.iInf fun _ => phi_measurable_data m q

lemma aMin_le_iff {m : ℕ} (data : Fin m → Obs 1) {c : ℝ} (hc : -10 ≤ c) :
    aMin data ≤ c ↔ (⨅ t ∈ Set.Icc (-10) c, phi data t) ≤ ⨅ t ∈ Box, phi data t := by
  constructor
  · intro h
    have hm := aMin_mem data
    refine le_trans (iInf₂_le (aMin data) ⟨hm.1.1, h⟩) (le_iInf₂ fun s hs => hm.2 s hs)
  · intro h
    by_cases hc10 : 10 ≤ c
    · exact le_trans (aMin_mem data).1.2 hc10
    push Not at hc10
    obtain ⟨t, ht, hmin⟩ := (isCompact_Icc (a := (-10:ℝ)) (b := c)).exists_isMinOn
      (Set.nonempty_Icc.mpr hc) (phi_continuous data).continuousOn
    have htv : phi data t = ⨅ t ∈ Set.Icc (-10) c, phi data t := by
      apply le_antisymm
      · exact le_iInf₂ fun s hs => hmin hs
      · exact iInf₂_le t ht
    have hmem : t ∈ argminSet data := by
      refine ⟨⟨ht.1, by linarith [ht.2]⟩, fun s hs => ?_⟩
      rw [htv]; exact le_trans h (iInf₂_le s hs)
    exact le_trans (csInf_le (argminSet_bdd data) hmem) ht.2

lemma aMin_measurable (m : ℕ) : Measurable (aMin : (Fin m → Obs 1) → ℝ) := by
  apply measurable_of_Iic
  intro c
  rcases lt_trichotomy c (-10) with hc | hc | hc
  · have : (aMin : (Fin m → Obs 1) → ℝ) ⁻¹' Set.Iic c = ∅ := by
      ext data; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
        not_le]
      linarith [(aMin_mem data).1.1]
    rw [this]; exact MeasurableSet.empty
  · have : (aMin : (Fin m → Obs 1) → ℝ) ⁻¹' Set.Iic c =
        {data | phi data (-10) ≤ ⨅ t ∈ Box, phi data t} := by
      ext data
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
      rw [aMin_le_iff data hc.ge, hc, Set.Icc_self]
      simp
    rw [this]
    exact measurableSet_le (phi_measurable_data m _) (iInf_Icc_measurable m (by norm_num))
  · have : (aMin : (Fin m → Obs 1) → ℝ) ⁻¹' Set.Iic c =
        {data | (⨅ t ∈ Set.Icc (-10) c, phi data t) ≤ ⨅ t ∈ Box, phi data t} := by
      ext data
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
      exact aMin_le_iff data hc.le
    rw [this]
    exact measurableSet_le (iInf_Icc_measurable m hc) (iInf_Icc_measurable m (by norm_num))

lemma estU_measurable : EstimatorMeasurable estU := by
  intro e i
  unfold estU
  have hc : Continuous fun a : ℝ => (EuclideanSpace.single 0 a : Ctx 1) := by
    have : (fun a : ℝ => (EuclideanSpace.single 0 a : Ctx 1)) = fun a => a • e1 := by
      funext a; ext i; fin_cases i; simp [e1]
    rw [this]; fun_prop
  exact hc.measurable.comp (aMin_measurable _)

end CorpCE


open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

noncomputable def EM : Market 1 1 :=
  ⟨10, 1, fU, Measure.dirac e1, fun _ => 0, estU, resU⟩

abbrev σT : Strategy 1 1 := truthful 1 1

noncomputable def trapVec : Ctx 1 := EuclideanSpace.single 0 (-10)

section hist
variable {N d : ℕ} (E : Market N d) (σ : Strategy N d)

lemma hist_stable (ω : ℕ → Draw N d) (m : ℕ) : ∀ n, m < n → hist E σ ω n m = record E σ ω m := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
    · simp only [hist]; rw [Function.update_of_ne (by omega)]; exact ih h
    · subst h; rfl

lemma record_eq (ω : ℕ → Draw N d) (n : ℕ) :
    record E σ ω n = step E σ n (hist E σ ω n) (ω n) := by
  simp [record, hist]

lemma hist_congr (ω ω' : ℕ → Draw N d) : ∀ n, (∀ m < n, ω m = ω' m) →
    hist E σ ω n = hist E σ ω' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [hist]
    rw [ih (fun m hm => h m (by omega)), h n (by omega)]

end hist

lemma thresh_one (b r : Fin 1 → ℝ) : thresh b r 0 = r 0 := by
  unfold thresh
  have : (Finset.univ.erase (0 : Fin 1)) = ∅ := by decide
  simp [this]

lemma isTopBidder_one (b : Fin 1 → ℝ) : IsTopBidder b 0 := by
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · rw [Subsingleton.elim j 0]
  · exact absurd hj (by simp [Fin.lt_def])

lemma inner_e1_trap : ⟪e1, trapVec⟫ = -10 := by
  rw [e1, trapVec, inner_single_single]; norm_num

lemma episodeOf_zero : episodeOf 0 = 0 := by simp [episodeOf]

lemma one_le_episodeOf {n : ℕ} (hn : 1 ≤ n) : 1 ≤ episodeOf n := by
  unfold episodeOf
  exact Nat.le_log_of_pow_le (by norm_num) (by simpa using (by omega : 2 ≤ n + 1))

lemma pow_episodeOf_le (n : ℕ) : 2 ^ episodeOf n ≤ n + 1 :=
  Nat.pow_log_le_self 2 (by omega)

/-- The good event for one period's draw. -/
def Good (n : ℕ) (w : Draw 1 1) : Prop :=
  w.1 = e1 ∧ w.2.1 0 ≤ 1 ∧ 0 ≤ w.2.2.2.2.1 ∧ w.2.2.1 < 1 ∧
    ¬ (w.2.2.1 < 1 / (2:ℝ) ^ episodeOf n ∧ w.2.2.2.2.1 ≤ w.2.1 0)

lemma step_bid (n : ℕ) (H : ℕ → Record 1 1) (w : Draw 1 1) :
    (step EM σT n H w).bid 0 = w.2.1 0 := by
  simp only [step]
  split_ifs <;> simp [truthful, values, EM]

lemma record_bid (ω : ℕ → Draw 1 1) (n : ℕ) : (record EM σT ω n).bid 0 = (ω n).2.1 0 := by
  rw [record_eq]; exact step_bid _ _ _

lemma obs_zero (n : ℕ) (H : ℕ → Record 1 1) (w : Draw 1 1) (hg : Good n w)
    (htrap : 1 / (2:ℝ) ^ episodeOf n ≤ w.2.2.1 → estimateAt EM H (episodeOf n) 0 = trapVec) :
    obsNLL fU trapVec ((step EM σT n H w).obs 0) = 0 := by
  classical
  obtain ⟨hx, hz, hr, hu1, hnw⟩ := hg
  simp only [step, Record.obs]
  split_ifs with hu
  · have hnr : ¬ (w.2.2.2.2.1 ≤ w.2.1 0) := fun h => hnw ⟨hu, h⟩
    have : w.2.2.2.1 = 0 := Subsingleton.elim _ _
    simp [obsNLL, truthful, values, EM, thresh_one, hx, this, hnr, noiseCDF_fU',
      inner_e1_trap]
    rw [Fx_eq_one (by linarith), nll_one]
  · have ht := htrap (not_lt.mp hu)
    have hall : ∀ i, estimateAt EM H (episodeOf n) i = trapVec := fun i => by
      rw [Subsingleton.elim i 0]; exact ht
    simp only [hall]
    have h100 : EM.res ⟪w.1, trapVec⟫ = 100 := by
      rw [hx, inner_e1_trap]; simp [EM, resU]
    rw [decide_eq_false]
    swap
    · rintro ⟨_, h⟩
      simp only [hall, h100] at h
      simp [truthful, values, EM] at h; linarith
    simp only [h100]
    simp [obsNLL, truthful, values, EM, thresh_one, noiseCDF_fU', hx, inner_e1_trap]
    rw [Fx_eq_one (by norm_num), nll_one]

lemma trap_estimate (ω : ℕ → Draw 1 1) : ∀ n, (∀ m < n, Good m (ω m)) → 1 ≤ n →
    estimateAt EM (hist EM σT ω n) (episodeOf n) 0 = trapVec := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hg hn
  obtain ⟨e', he'⟩ : ∃ e', episodeOf n = e' + 1 :=
    ⟨episodeOf n - 1, by have := one_le_episodeOf hn; omega⟩
  have hpow := pow_episodeOf_le n
  rw [he'] at hpow ⊢
  simp only [estimateAt, EM, estU]
  rw [trapVec]
  congr 1
  apply aMin_trap
  simp only [phi, negLogLik]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj : 2 ^ e' - 1 + (j:ℕ) < n := by
    have := j.isLt; have : 2 ^ (e'+1) = 2 * 2^e' := by ring
    have : 1 ≤ 2 ^ e' := Nat.one_le_two_pow; omega
  set m := 2 ^ e' - 1 + (j:ℕ)
  rw [hist_stable _ _ _ _ _ hj, record_eq]
  rw [show (EuclideanSpace.single 0 (-10) : Ctx 1) = trapVec from rfl]
  apply obs_zero m _ _ (hg m hj)
  intro hu
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · exfalso
    have h1 : (ω 0).2.2.1 < 1 := by have := (hg m hj).2.2.2.1; rwa [h0] at this
    rw [h0, episodeOf_zero] at hu; simp at hu; linarith
  · exact ih m hj (fun k hk => hg k (by omega)) hpos

end CorpCE


open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

/-! ### the noise law -/

lemma noiseLaw_apply (S : Set ℝ) (hS : MeasurableSet S) :
    noiseLaw fU S = ENNReal.ofReal (1/2) * volume (S ∩ Set.Icc (-1) 1) := by
  unfold noiseLaw
  rw [withDensity_apply _ hS]
  have : (fun z => ENNReal.ofReal (fU z)) =
      (Set.Icc (-1:ℝ) 1).indicator (fun _ => ENNReal.ofReal (1/2)) := by
    funext z; unfold fU; by_cases h : z ∈ Set.Icc (-1:ℝ) 1 <;> simp [h]
  rw [this, lintegral_indicator_const measurableSet_Icc, Measure.restrict_apply measurableSet_Icc,
    Set.inter_comm]

instance noiseLaw_prob : IsProbabilityMeasure (noiseLaw fU) := by
  constructor
  rw [noiseLaw_apply _ MeasurableSet.univ, Set.univ_inter, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

lemma noiseLaw_Ioi_one : noiseLaw fU (Set.Ioi 1) = 0 := by
  rw [noiseLaw_apply _ measurableSet_Ioi]
  have : Set.Ioi (1:ℝ) ∩ Set.Icc (-1) 1 = ∅ := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_empty_iff_false,
      iff_false, not_and]; intro h1 _; linarith
  simp [this]

lemma noiseLaw_Ici_bound (ρ : ℝ) :
    ENNReal.ofReal ρ * noiseLaw fU (Set.Ici ρ) ≤ ENNReal.ofReal (1/8) := by
  rw [noiseLaw_apply _ measurableSet_Ici]
  rcases le_or_gt ρ 0 with h | h
  · simp [ENNReal.ofReal_of_nonpos h]
  rcases le_or_gt ρ 1 with h' | h'
  · have : Set.Ici ρ ∩ Set.Icc (-1) 1 = Set.Icc ρ 1 := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]; constructor
      · rintro ⟨a, b, c⟩; exact ⟨a, c⟩
      · rintro ⟨a, c⟩; exact ⟨a, by linarith, c⟩
    rw [this, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul h.le]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (2*ρ - 1)]
  · have : Set.Ici ρ ∩ Set.Icc (-1) 1 = ∅ := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_and]; intro h1 _; linarith
    simp [this]

lemma noiseLaw_Ici_100 : noiseLaw fU (Set.Ici 100) = 0 :=
  measure_mono_null (fun t (ht : (100:ℝ) ≤ t) => (show (1:ℝ) < t by linarith)) noiseLaw_Ioi_one

lemma noiseLaw_Ici_half : noiseLaw fU (Set.Ici (1/2)) = ENNReal.ofReal (1/4) := by
  rw [noiseLaw_apply _ measurableSet_Ici]
  have : Set.Ici (1/2:ℝ) ∩ Set.Icc (-1) 1 = Set.Icc (1/2) 1 := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]; constructor
    · rintro ⟨a, b, c⟩; exact ⟨a, c⟩
    · rintro ⟨a, c⟩; exact ⟨a, by linarith, c⟩
  rw [this, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- noise vector law on `Fin 1` -/
lemma piNoise_coord (A : Set ℝ) (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin 1 => noiseLaw fU) {z | z 0 ∈ A} = noiseLaw fU A := by
  have : {z : Fin 1 → ℝ | z 0 ∈ A} = Set.univ.pi (fun _ => A) := by
    ext z; simp [Fin.forall_fin_one]
  rw [this, Measure.pi_pi]; simp

/-! ### uniform laws -/

lemma unif_apply (a b : ℝ) (hab : a < b) (S : Set ℝ) :
    unif a b S = ENNReal.ofReal (b - a)⁻¹ * volume (Set.Icc a b ∩ S) := by
  unfold unif
  rw [cond_apply measurableSet_Icc, Real.volume_Icc, ENNReal.ofReal_inv_of_pos (by linarith)]

instance unif_prob (a b : ℝ) [Fact (a < b)] : IsProbabilityMeasure (unif a b) := by
  unfold unif
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]; simpa using (Fact.out : a < b)
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

instance : Fact ((0:ℝ) < 1) := ⟨by norm_num⟩
instance : Fact ((0:ℝ) < 11) := ⟨by norm_num⟩

lemma unif01_Iio (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) : unif 0 1 (Set.Iio c) = ENNReal.ofReal c := by
  rw [unif_apply 0 1 (by norm_num)]
  have : Set.Icc (0:ℝ) 1 ∩ Set.Iio c = Set.Ico 0 c := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]; constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, c⟩
    · rintro ⟨a, c⟩; exact ⟨⟨a, by linarith⟩, c⟩
  rw [this, Real.volume_Ico]; simp

lemma unif01_Ici (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    unif 0 1 (Set.Ici c) = ENNReal.ofReal (1 - c) := by
  rw [unif_apply 0 1 (by norm_num)]
  have : Set.Icc (0:ℝ) 1 ∩ Set.Ici c = Set.Icc c 1 := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]; constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨c, b⟩
    · rintro ⟨a, c⟩; exact ⟨⟨by linarith, c⟩, a⟩
  rw [this, Real.volume_Icc]; simp

lemma unif011_Iic1 : unif 0 11 (Set.Iic 1) = ENNReal.ofReal (1/11) := by
  rw [unif_apply 0 11 (by norm_num)]
  have : Set.Icc (0:ℝ) 11 ∩ Set.Iic 1 = Set.Icc 0 1 := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]; constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, c⟩
    · rintro ⟨a, c⟩; exact ⟨⟨a, by linarith⟩, c⟩
  rw [this, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]; norm_num

lemma unif011_Iio0 : unif 0 11 (Set.Iio 0) = 0 := by
  rw [unif_apply 0 11 (by norm_num)]
  have : Set.Icc (0:ℝ) 11 ∩ Set.Iio 0 = ∅ := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_empty_iff_false,
      iff_false, not_and]; intro h _; linarith [h.1]
  simp [this]

lemma unif01_Ici1 : unif 0 1 (Set.Ici 1) = 0 := by
  rw [unif01_Ici 1 (by norm_num) le_rfl]; simp

/-! ### the draw law -/

lemma EM_B : EM.B = 11 := by simp [Market.B, EM]; norm_num

instance drawLaw_prob : IsProbabilityMeasure (drawLaw EM) := by
  unfold drawLaw
  rw [EM_B]
  have : EM.D = Measure.dirac e1 := rfl
  have h2 : EM.f = fU := rfl
  rw [this, h2]
  infer_instance

lemma pathLaw_eq : pathLaw EM = Measure.infinitePi (fun _ : ℕ => drawLaw EM) := by
  unfold pathLaw; rw [dif_pos drawLaw_prob]

lemma drawLaw_rect (A : Set (Ctx 1)) (B : Set (Fin 1 → ℝ)) (C : Set ℝ) (D' : Set (Fin 1))
    (E' : Set ℝ) (F' : Set (Fin 1 → ℝ)) :
    drawLaw EM (A ×ˢ (B ×ˢ (C ×ˢ (D' ×ˢ (E' ×ˢ F'))))) =
      Measure.dirac e1 A * ((Measure.pi fun _ : Fin 1 => noiseLaw fU) B * (unif 0 1 C *
        (uniformOn (Set.univ : Set (Fin 1)) D' * (unif 0 11 E' *
          (Measure.pi fun _ : Fin 1 => unif 0 1) F')))) := by
  unfold drawLaw
  rw [EM_B]
  show ((Measure.dirac e1).prod ((Measure.pi fun _ : Fin 1 => noiseLaw fU).prod ((unif 0 1).prod
    ((uniformOn (Set.univ : Set (Fin 1))).prod ((unif 0 11).prod
      (Measure.pi fun _ : Fin 1 => unif 0 1)))))) _ = _
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    Measure.prod_prod]

end CorpCE


open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

section upd
variable {X : Type*} [MeasurableSpace X] (Q : Measure X) [IsProbabilityMeasure Q]

lemma map_update_infinitePi (n : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => Q).prod Q).map
      (fun p : (ℕ → X) × X => Function.update p.1 n p.2) = Measure.infinitePi fun _ : ℕ => Q := by
  apply Measure.eq_infinitePi
  intro s t ht
  have hmeas : Measurable (fun p : (ℕ → X) × X => Function.update p.1 n p.2) :=
    measurable_update'
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : (fun p : (ℕ → X) × X => Function.update p.1 n p.2) ⁻¹' (Set.pi (↑s) t) =
      (Set.pi (↑(s.erase n)) t) ×ˢ (if n ∈ s then t n else Set.univ) := by
    ext ⟨ω, b⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun i ⟨hin, his⟩ => ?_, ?_⟩
      · have := h i his; rwa [Function.update_of_ne hin] at this
      · split_ifs with hn
        · have := h n hn; rwa [Function.update_self] at this
        · trivial
    · rintro ⟨h1, h2⟩ i his
      by_cases hin : i = n
      · subst hin; rw [Function.update_self]; rw [if_pos his] at h2; exact h2
      · rw [Function.update_of_ne hin]; exact h1 i ⟨hin, his⟩
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i)]
  split_ifs with hn
  · exact Finset.prod_erase_mul s (fun i => Q (t i)) hn
  · rw [measure_univ, mul_one, Finset.erase_eq_of_notMem hn]

/-- Upper bound for the lintegral of a function of `(ω, ω n)` that only sees `ω` below `n`. -/
lemma lintegral_le_split (n : ℕ) (G : (ℕ → X) → ℝ≥0∞) :
    ∫⁻ ω, G ω ∂(Measure.infinitePi fun _ : ℕ => Q) ≤
      ∫⁻ ω, ∫⁻ b, G (Function.update ω n b) ∂Q ∂(Measure.infinitePi fun _ : ℕ => Q) := by
  conv_lhs => rw [← map_update_infinitePi Q n]
  refine le_trans (lintegral_map_le _ _) ?_
  exact lintegral_prod_le (fun p : (ℕ → X) × X => G (Function.update p.1 n p.2))

end upd

end CorpCE


open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

lemma piNoise_lt (a : ℝ) :
    (Measure.pi fun _ : Fin 1 => noiseLaw fU) {z | a < z 0} = noiseLaw fU (Set.Ioi a) :=
  piNoise_coord (Set.Ioi a) measurableSet_Ioi

lemma piNoise_le (a : ℝ) :
    (Measure.pi fun _ : Fin 1 => noiseLaw fU) {z | a ≤ z 0} = noiseLaw fU (Set.Ici a) :=
  piNoise_coord (Set.Ici a) measurableSet_Ici

noncomputable def cE (n : ℕ) : ℝ := 1 / (2:ℝ) ^ episodeOf n

lemma cE_pos (n : ℕ) : 0 < cE n := by unfold cE; positivity
lemma cE_le_one (n : ℕ) : cE n ≤ 1 := by
  unfold cE; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
lemma cE_le_half {n : ℕ} (hn : 1 ≤ n) : cE n ≤ 1/2 := by
  unfold cE
  have := one_le_episodeOf hn
  have h2 : (2:ℝ) ≤ 2 ^ episodeOf n := by
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ episodeOf n := pow_le_pow_right₀ (by norm_num) this
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

lemma resU_pos (θ : ℝ) : 0 < resU θ := by
  unfold resU; split_ifs with h1 h2
  · norm_num
  · push Not at h1; linarith
  · push Not at h1 h2; linarith

noncomputable def rhoE (n : ℕ) (H : ℕ → Record 1 1) : ℝ :=
  resU ⟪e1, estimateAt EM H (episodeOf n) 0⟫

open Set in
noncomputable def payBd (n : ℕ) (H : ℕ → Record 1 1) (w : Draw 1 1) : ℝ≥0∞ :=
  (univ ×ˢ (univ ×ˢ (Iio (cE n) ×ˢ (univ ×ˢ (Iic 1 ×ˢ univ))))).indicator (fun _ => 1) w +
  (univ ×ˢ ({z : Fin 1 → ℝ | 1 < z 0} ×ˢ (univ ×ˢ (univ ×ˢ (univ ×ˢ univ))))).indicator
    (fun _ => ⊤) w +
  (({e1}ᶜ : Set (Ctx 1)) ×ˢ (univ ×ˢ (univ ×ˢ (univ ×ˢ (univ ×ˢ univ))))).indicator
    (fun _ => ⊤) w +
  (univ ×ˢ (univ ×ˢ (univ ×ˢ (univ ×ˢ (Iio 0 ×ˢ univ))))).indicator (fun _ => ⊤) w +
  (univ ×ˢ ({z : Fin 1 → ℝ | rhoE n H ≤ z 0} ×ˢ (Ici (cE n) ×ˢ (univ ×ˢ (univ ×ˢ univ))))).indicator
    (fun _ => ENNReal.ofReal (rhoE n H)) w

lemma pay_le_payBd (n : ℕ) (H : ℕ → Record 1 1) (w : Draw 1 1) :
    ‖(step EM σT n H w).pay 0‖ₑ ≤ payBd n H w := by
  classical
  obtain ⟨x, z, u, i0, r, s⟩ := w
  simp only [step]
  split_ifs with hu
  · -- exploration
    simp only [truthful, values, EM, inner_zero_right, zero_add]
    have hi0 : (0 : Fin 1) = i0 := Subsingleton.elim _ _
    by_cases hrz : r ≤ z 0
    · rw [if_pos ⟨hi0, hrz⟩]
      by_cases hr0 : r < 0
      · have : (x, z, u, i0, r, s) ∈ (Set.univ ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ
            (Set.Iio 0 ×ˢ Set.univ)))) : Set (Draw 1 1)) := by simp [hr0]
        unfold payBd; rw [Set.indicator_of_mem this]; simp
      by_cases hz1 : 1 < z 0
      · have : (x, z, u, i0, r, s) ∈ (Set.univ ×ˢ ({z : Fin 1 → ℝ | 1 < z 0} ×ˢ (Set.univ ×ˢ
            (Set.univ ×ˢ (Set.univ ×ˢ Set.univ)))) : Set (Draw 1 1)) := by simp [hz1]
        unfold payBd; rw [Set.indicator_of_mem this (f := fun _ => ⊤)]; simp
      · push Not at hr0 hz1
        have : (x, z, u, i0, r, s) ∈ (Set.univ ×ˢ (Set.univ ×ˢ (Set.Iio (cE n) ×ˢ (Set.univ ×ˢ
            (Set.Iic 1 ×ˢ Set.univ)))) : Set (Draw 1 1)) := by
          simp only [Set.mem_prod, Set.mem_univ, Set.mem_Iio, Set.mem_Iic, true_and, and_true]
          exact ⟨hu, by linarith⟩
        unfold payBd; rw [Set.indicator_of_mem this]
        refine le_trans ?_ (le_add_right (le_add_right (le_add_right (le_add_right le_rfl))))
        rw [Real.enorm_eq_ofReal hr0]
        simpa using (show r ≤ 1 by linarith)
    · rw [if_neg (fun h => hrz h.2)]; simp
  · -- exploitation
    simp only [lazyPay]
    split_ifs with hw
    · rw [thresh_one]
      by_cases hx : x = e1
      · subst hx
        have hρ : EM.res ⟪e1, estimateAt EM H (episodeOf n) 0⟫ = rhoE n H := rfl
        rw [hρ]
        have hwin := hw.2
        simp only [hρ, truthful, values, EM, inner_zero_right, zero_add] at hwin
        have : (e1, z, u, i0, r, s) ∈ (Set.univ ×ˢ ({z : Fin 1 → ℝ | rhoE n H ≤ z 0} ×ˢ
            (Set.Ici (cE n) ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ Set.univ)))) : Set (Draw 1 1)) := by
          simp only [Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, Set.mem_Ici, true_and, and_true]
          exact ⟨hwin, by push Not at hu; exact hu⟩
        unfold payBd; rw [Set.indicator_of_mem this]
        rw [Real.enorm_eq_ofReal (show 0 ≤ rhoE n H from (resU_pos _).le)]
        exact le_add_left le_rfl
      · have : (x, z, u, i0, r, s) ∈ (({e1}ᶜ : Set (Ctx 1)) ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ
            (Set.univ ×ˢ (Set.univ ×ˢ Set.univ)))) : Set (Draw 1 1)) := by simp [hx]
        unfold payBd; rw [Set.indicator_of_mem this (f := fun _ => ⊤)]; simp
    · simp

lemma lintegral_payBd (n : ℕ) (H : ℕ → Record 1 1) :
    ∫⁻ w, payBd n H w ∂(drawLaw EM) =
      ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) +
        ENNReal.ofReal (rhoE n H) * (noiseLaw fU (Set.Ici (rhoE n H)) *
          ENNReal.ofReal (1 - cE n)) := by
  have hc0 := (cE_pos n).le
  have hc1 := cE_le_one n
  have m1 : MeasurableSet {z : Fin 1 → ℝ | 1 < z 0} :=
    measurableSet_lt measurable_const (measurable_pi_apply 0)
  have m2 : MeasurableSet {z : Fin 1 → ℝ | rhoE n H ≤ z 0} :=
    measurableSet_le measurable_const (measurable_pi_apply 0)
  unfold payBd
  rw [lintegral_add_left (by measurability), lintegral_add_left (by measurability),
    lintegral_add_left (by measurability), lintegral_add_left (by measurability)]
  rw [lintegral_indicator_const (by measurability), lintegral_indicator_const (by measurability),
    lintegral_indicator_const (by measurability), lintegral_indicator_const (by measurability),
    lintegral_indicator_const (by measurability)]
  rw [drawLaw_rect, drawLaw_rect, drawLaw_rect, drawLaw_rect, drawLaw_rect]
  have hpi1 : (Measure.pi fun _ : Fin 1 => noiseLaw fU) {z : Fin 1 → ℝ | 1 < z 0} = 0 := by
    rw [piNoise_lt]; exact noiseLaw_Ioi_one
  rw [hpi1, piNoise_le, unif01_Iio _ hc0 hc1, unif01_Ici _ hc0 hc1,
    unif011_Iic1, unif011_Iio0]
  simp [Measure.dirac_apply' _ (measurableSet_singleton e1).compl]

end CorpCE


open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

def GoodSet (m : ℕ) : Set (Draw 1 1) := {w | Good m w}

lemma goodSet_measurable (m : ℕ) : MeasurableSet (GoodSet m) := by
  unfold GoodSet Good
  have hx : Measurable fun w : Draw 1 1 => w.1 := measurable_fst
  have hz : Measurable fun w : Draw 1 1 => w.2.1 0 := by fun_prop
  have hu : Measurable fun w : Draw 1 1 => w.2.2.1 := by fun_prop
  have hr : Measurable fun w : Draw 1 1 => w.2.2.2.2.1 := by fun_prop
  refine MeasurableSet.inter (measurableSet_eq_fun hx measurable_const) ?_
  refine MeasurableSet.inter (measurableSet_le hz measurable_const) ?_
  refine MeasurableSet.inter (measurableSet_le measurable_const hr) ?_
  refine MeasurableSet.inter (measurableSet_lt hu measurable_const) ?_
  refine MeasurableSet.compl ?_
  exact (measurableSet_lt hu measurable_const).inter (measurableSet_le hr hz)

def TrapSet (n : ℕ) : Set (ℕ → Draw 1 1) := Set.pi (↑(Finset.range n)) GoodSet

lemma mem_trapSet {n : ℕ} {ω : ℕ → Draw 1 1} : ω ∈ TrapSet n ↔ ∀ m < n, Good m (ω m) := by
  simp [TrapSet, GoodSet]

lemma trapSet_measurable (n : ℕ) : MeasurableSet (TrapSet n) :=
  MeasurableSet.pi (Finset.range n).countable_toSet fun m _ => goodSet_measurable m

lemma goodSet_compl_le (m : ℕ) : drawLaw EM (GoodSet m)ᶜ ≤ ENNReal.ofReal (cE m / 11) := by
  have hc0 := (cE_pos m).le
  have hc1 := cE_le_one m
  have hsub : (GoodSet m)ᶜ ⊆
      ((({e1}ᶜ : Set (Ctx 1)) ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ Set.univ))))) ∪
      (Set.univ ×ˢ ({z : Fin 1 → ℝ | 1 < z 0} ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ Set.univ)))))) ∪
      ((Set.univ ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ (Set.Iio 0 ×ˢ Set.univ))))) ∪
      (Set.univ ×ˢ (Set.univ ×ˢ (Set.Ici 1 ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ Set.univ)))))) ∪
      (Set.univ ×ˢ (Set.univ ×ˢ (Set.Iio (cE m) ×ˢ (Set.univ ×ˢ (Set.Iic 1 ×ˢ Set.univ))))) := by
    rintro ⟨x, z, u, i0, r, s⟩ hw
    simp only [GoodSet, Good, Set.mem_compl_iff, Set.mem_setOf_eq] at hw
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_univ, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_Ici, Set.mem_Iic, true_and, and_true]
    by_cases h1 : x = e1
    swap; · exact Or.inl (Or.inl (Or.inl h1))
    by_cases h2 : 1 < z 0
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : r < 0
    · exact Or.inl (Or.inr (Or.inl h3))
    by_cases h4 : 1 ≤ u
    · exact Or.inl (Or.inr (Or.inr h4))
    right
    push Not at h2 h3 h4
    by_contra h5
    apply hw
    refine ⟨h1, h2, h3, h4, ?_⟩
    rintro ⟨hu, hr⟩
    exact h5 ⟨by simpa [cE] using hu, by linarith⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add_left (le_refl _) _) ?_
  refine le_trans (add_le_add (measure_union_le _ _) le_rfl) ?_
  refine le_trans (add_le_add (add_le_add (measure_union_le _ _) (measure_union_le _ _)) le_rfl) ?_
  rw [drawLaw_rect, drawLaw_rect, drawLaw_rect, drawLaw_rect, drawLaw_rect]
  have hpi1 : (Measure.pi fun _ : Fin 1 => noiseLaw fU) {z : Fin 1 → ℝ | 1 < z 0} = 0 := by
    rw [piNoise_lt]; exact noiseLaw_Ioi_one
  rw [hpi1, unif01_Iio _ hc0 hc1, unif011_Iic1, unif011_Iio0, unif01_Ici1]
  simp [Measure.dirac_apply' _ (measurableSet_singleton e1).compl]
  rw [ENNReal.ofReal_div_of_pos (by norm_num), div_eq_mul_inv]; simp

lemma goodSet_ge (m : ℕ) : ENNReal.ofReal (1 - cE m / 11) ≤ drawLaw EM (GoodSet m) := by
  have h := goodSet_compl_le m
  have he : drawLaw EM (GoodSet m) = 1 - drawLaw EM (GoodSet m)ᶜ := by
    have := prob_compl_eq_one_sub (μ := drawLaw EM) (goodSet_measurable m).compl
    rwa [compl_compl] at this
  rw [he, ENNReal.ofReal_sub _ (by have := (cE_pos m).le; positivity), ENNReal.ofReal_one]
  exact tsub_le_tsub_left h 1

end CorpCE


open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

instance pathLaw_prob : IsProbabilityMeasure (pathLaw EM) := by
  rw [pathLaw_eq]; infer_instance

lemma record_update (ω : ℕ → Draw 1 1) (n : ℕ) (b : Draw 1 1) :
    record EM σT (Function.update ω n b) n = step EM σT n (hist EM σT ω n) b := by
  rw [record_eq, Function.update_self]
  congr 1
  exact hist_congr _ _ _ _ n (fun m hm => Function.update_of_ne (by omega) _ _)

/-- the key bound: `ofReal (rev_n) ≤ ∫⁻ ω, (bound from the inner integral)`. -/
lemma revenue_le_lintegral (n : ℕ) :
    ENNReal.ofReal (revenue EM σT n) ≤
      ∫⁻ ω, (ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) +
        ENNReal.ofReal (rhoE n (hist EM σT ω n)) *
          (noiseLaw fU (Set.Ici (rhoE n (hist EM σT ω n))) * ENNReal.ofReal (1 - cE n)))
        ∂(pathLaw EM) := by
  unfold revenue
  simp only [Fin.sum_univ_one]
  refine le_trans (ENNReal.ofReal_le_ofReal (le_abs_self _)) ?_
  rw [← Real.enorm_eq_ofReal_abs]
  refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
  rw [pathLaw_eq]
  refine le_trans (lintegral_le_split (drawLaw EM) n _) ?_
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_payBd]
  refine lintegral_mono fun b => ?_
  rw [record_update]
  exact pay_le_payBd n _ b

lemma rho_trap {n : ℕ} (hn : 1 ≤ n) {ω : ℕ → Draw 1 1} (hω : ω ∈ TrapSet n) :
    rhoE n (hist EM σT ω n) = 100 := by
  unfold rhoE
  rw [trap_estimate ω n (mem_trapSet.mp hω) hn, inner_e1_trap]
  simp [resU]

lemma revenue_bound (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (revenue EM σT n) ≤
      ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) +
        ENNReal.ofReal (1/8) * ENNReal.ofReal (1 - cE n) * pathLaw EM (TrapSet n)ᶜ := by
  refine le_trans (revenue_le_lintegral n) ?_
  have hpt : ∀ ω, (ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) +
        ENNReal.ofReal (rhoE n (hist EM σT ω n)) *
          (noiseLaw fU (Set.Ici (rhoE n (hist EM σT ω n))) * ENNReal.ofReal (1 - cE n))) ≤
      ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) +
        (TrapSet n)ᶜ.indicator (fun _ => ENNReal.ofReal (1/8) * ENNReal.ofReal (1 - cE n)) ω := by
    intro ω
    gcongr
    by_cases hω : ω ∈ TrapSet n
    · rw [rho_trap hn hω, noiseLaw_Ici_100]; simp
    · rw [Set.indicator_of_mem (Set.mem_compl hω), ← mul_assoc]
      exact mul_le_mul_left (noiseLaw_Ici_bound _) _
  refine le_trans (lintegral_mono hpt) ?_
  rw [lintegral_add_left measurable_const, lintegral_const,
    lintegral_indicator_const (trapSet_measurable n).compl, measure_univ, mul_one]

lemma revenue_bound0 (n : ℕ) :
    ENNReal.ofReal (revenue EM σT n) ≤
      ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) +
        ENNReal.ofReal (1/8) * ENNReal.ofReal (1 - cE n) := by
  refine le_trans (revenue_le_lintegral n) ?_
  have hpt : ∀ ω, (ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) +
        ENNReal.ofReal (rhoE n (hist EM σT ω n)) *
          (noiseLaw fU (Set.Ici (rhoE n (hist EM σT ω n))) * ENNReal.ofReal (1 - cE n))) ≤
      ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) +
        ENNReal.ofReal (1/8) * ENNReal.ofReal (1 - cE n) := by
    intro ω
    refine add_le_add le_rfl ?_
    rw [← mul_assoc]
    exact mul_le_mul_left (noiseLaw_Ici_bound _) _
  refine le_trans (lintegral_mono hpt) ?_
  rw [lintegral_const, measure_univ, mul_one]

/-- real form -/
lemma revenue_le_real (n : ℕ) (hn : 1 ≤ n) :
    revenue EM σT n ≤ cE n / 11 + (1/8) * (1 - cE n) * (1 - (pathLaw EM (TrapSet n)).toReal) := by
  have hc0 := (cE_pos n).le
  have hc1 := cE_le_one n
  have h := revenue_bound n hn
  rw [prob_compl_eq_one_sub (trapSet_measurable n)] at h
  have hP : pathLaw EM (TrapSet n) = ENNReal.ofReal (pathLaw EM (TrapSet n)).toReal :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hp1 : (pathLaw EM (TrapSet n)).toReal ≤ 1 := by
    have := prob_le_one (μ := pathLaw EM) (s := TrapSet n)
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using this)
  have hp0 : 0 ≤ (pathLaw EM (TrapSet n)).toReal := ENNReal.toReal_nonneg
  have e1' : ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) = ENNReal.ofReal (cE n / 11) := by
    rw [← ENNReal.ofReal_mul hc0]; ring_nf
  set p := (pathLaw EM (TrapSet n)).toReal
  have e2 : ENNReal.ofReal (1/8) * ENNReal.ofReal (1 - cE n) * (1 - pathLaw EM (TrapSet n)) =
      ENNReal.ofReal ((1/8) * (1 - cE n) * (1 - p)) := by
    rw [hP, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp0,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/8),
      ← ENNReal.ofReal_mul (by nlinarith : (0:ℝ) ≤ 1/8 * (1 - cE n))]
  have hnn : 0 ≤ (1/8) * (1 - cE n) * (1 - p) := by
    apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  rw [e1', e2, ← ENNReal.ofReal_add (by positivity) hnn,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (by positivity) hnn)] at h
  exact h

lemma revenue_le_real0 (n : ℕ) : revenue EM σT n ≤ cE n / 11 + (1/8) * (1 - cE n) := by
  have hc0 := (cE_pos n).le
  have hc1 := cE_le_one n
  have h := revenue_bound0 n
  have e1' : ENNReal.ofReal (cE n) * ENNReal.ofReal (1/11) = ENNReal.ofReal (cE n / 11) := by
    rw [← ENNReal.ofReal_mul hc0]; ring_nf
  have e2 : ENNReal.ofReal (1/8) * ENNReal.ofReal (1 - cE n) =
      ENNReal.ofReal ((1/8) * (1 - cE n)) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/8)]
  have hnn : 0 ≤ (1/8) * (1 - cE n) := by nlinarith
  rw [e1', e2, ← ENNReal.ofReal_add (by positivity) hnn,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (by positivity) hnn)] at h
  exact h

end CorpCE


open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

lemma resU_zero : resU 0 = 1/2 := by simp [resU]

lemma bench_eq : benchmarkRevenue EM = 1/8 := by
  classical
  unfold benchmarkRevenue
  have hfun : (fun xz : Ctx 1 × (Fin 1 → ℝ) =>
      lazyRevenue (values xz.1 EM.β xz.2) (fun i => EM.res ⟪xz.1, EM.β i⟫)) =
      (Set.univ ×ˢ {z : Fin 1 → ℝ | 1/2 ≤ z 0}).indicator (fun _ => (1/2:ℝ)) := by
    funext ⟨x, z⟩
    have hr : EM.res ⟪x, EM.β 0⟫ = 1/2 := by simp [EM, resU_zero]
    simp only [lazyRevenue, Fin.sum_univ_one, lazyPay, thresh_one, LazyWins]
    by_cases h : 1/2 ≤ z 0
    · rw [if_pos ⟨isTopBidder_one _, by simp [values, EM, resU_zero] at h ⊢; linarith⟩,
        Set.indicator_of_mem (by simp only [Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, true_and]; exact h)]
      simp [hr]
    · rw [if_neg (by rintro ⟨_, h'⟩; simp [values, EM, resU_zero] at h'; linarith),
        Set.indicator_of_notMem (by simp only [Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, true_and]; exact h)]
  rw [hfun, integral_indicator_const _ (MeasurableSet.univ.prod
    (measurableSet_le measurable_const (measurable_pi_apply 0)))]
  rw [measureReal_def]
  show (((Measure.dirac e1).prod (Measure.pi fun _ : Fin 1 => noiseLaw fU))
    (Set.univ ×ˢ {z : Fin 1 → ℝ | 1/2 ≤ z 0})).toReal • (1/2:ℝ) = 1/8
  rw [Measure.prod_prod, piNoise_le, noiseLaw_Ici_half]
  simp; norm_num

/-! ### trap probability -/

lemma trap_prob_ge (n : ℕ) :
    ∏ m ∈ Finset.range n, (1 - cE m / 11) ≤ (pathLaw EM (TrapSet n)).toReal := by
  rw [pathLaw_eq, TrapSet, Measure.infinitePi_pi _ (fun m _ => goodSet_measurable m),
    ENNReal.toReal_prod]
  refine Finset.prod_le_prod (fun m _ => ?_) (fun m _ => ?_)
  · have := cE_le_one m; linarith
  · have h := goodSet_ge m
    have := cE_le_one m
    rw [← ENNReal.toReal_ofReal (show 0 ≤ 1 - cE m / 11 by linarith)]
    exact ENNReal.toReal_mono (measure_ne_top _ _) h

lemma prod_antitone (a : ℕ → ℝ) (h0 : ∀ m, 0 ≤ a m) (h1 : ∀ m, a m ≤ 1) {n n' : ℕ} (h : n ≤ n') :
    ∏ m ∈ Finset.range n', a m ≤ ∏ m ∈ Finset.range n, a m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [Finset.prod_range_succ]
    exact le_trans (mul_le_of_le_one_right (Finset.prod_nonneg fun m _ => h0 m) (h1 _)) ih

lemma episodeOf_block (K j : ℕ) (hj : j < 2 ^ K) : episodeOf (2 ^ K - 1 + j) = K := by
  unfold episodeOf
  have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  rw [show 2 ^ K - 1 + j + 1 = 2 ^ K + j by omega]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · rw [pow_succ]; omega

lemma prod_block_ge (K : ℕ) :
    (10/11:ℝ) ^ K ≤ ∏ m ∈ Finset.range (2 ^ K - 1), (1 - cE m / 11) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    rw [show 2 ^ (K+1) - 1 = (2 ^ K - 1) + 2 ^ K by rw [pow_succ]; omega, Finset.prod_range_add]
    have hblock : ∏ j ∈ Finset.range (2 ^ K), (1 - cE (2 ^ K - 1 + j) / 11) =
        (1 - 1 / ((2:ℝ) ^ K * 11)) ^ (2 ^ K) := by
      rw [Finset.prod_congr rfl (g := fun _ => (1 - 1 / ((2:ℝ) ^ K * 11)))]
      · simp
      · intro j hj
        rw [cE, episodeOf_block K j (Finset.mem_range.mp hj)]; ring
    rw [hblock, pow_succ]
    have hb : (10/11:ℝ) ≤ (1 - 1 / ((2:ℝ) ^ K * 11)) ^ (2 ^ K) := by
      have hpos : (0:ℝ) < 2 ^ K := by positivity
      have := one_add_mul_le_pow (a := -(1 / ((2:ℝ) ^ K * 11))) (by
        have : 1 / ((2:ℝ) ^ K * 11) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := K)]
        linarith) (2 ^ K)
      rw [← sub_eq_add_neg] at this
      refine le_trans ?_ this
      push_cast
      have : (2:ℝ) ^ K * (1 / (2 ^ K * 11)) = 1/11 := by field_simp
      rw [mul_neg, this]; norm_num
    have hnn : (0:ℝ) ≤ (10/11) ^ K := by positivity
    calc (10/11:ℝ) ^ K * (10/11) ≤ (∏ m ∈ Finset.range (2 ^ K - 1), (1 - cE m / 11)) * (10/11) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg fun m _ => by
          have := cE_le_one m; linarith)

lemma trap_prob_K {K n : ℕ} (hn : n < 2 ^ K) : (10/11:ℝ) ^ K ≤ (pathLaw EM (TrapSet n)).toReal := by
  refine le_trans (prod_block_ge K) (le_trans ?_ (trap_prob_ge n))
  apply prod_antitone _ (fun m => by have := cE_le_one m; linarith)
    (fun m => by have := (cE_pos m).le; linarith)
  omega

/-! ### regret lower bound -/

lemma regret_ge (K : ℕ) :
    ((2:ℝ) ^ K - 1) * ((10/11:ℝ) ^ K / 16) ≤ regret EM σT (2 ^ K) := by
  unfold regret
  rw [bench_eq]
  have hterm : ∀ n ∈ Finset.range (2 ^ K),
      (if n = 0 then (0:ℝ) else (10/11:ℝ) ^ K / 16) ≤ 1/8 - revenue EM σT n := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    have hc0 := (cE_pos n).le
    have hc1 := cE_le_one n
    split_ifs with h0
    · have := revenue_le_real0 n; nlinarith
    · have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
      have := revenue_le_real n h1
      have hp := trap_prob_K (K := K) hn'
      have hch := cE_le_half h1
      set p := (pathLaw EM (TrapSet n)).toReal
      have hp0 : 0 ≤ p := le_trans (by positivity) hp
      have key : p / 2 ≤ (1 - cE n) * p := by nlinarith
      nlinarith
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  have : (Finset.filter (fun n => ¬n = 0) (Finset.range (2 ^ K))).card = 2 ^ K - 1 := by
    have : Finset.filter (fun n => ¬n = 0) (Finset.range (2 ^ K)) = (Finset.range (2^K)).erase 0 := by
      ext n; simp [and_comm]
    rw [this, Finset.card_erase_of_mem (by simp), Finset.card_range]
  rw [this, Nat.cast_sub Nat.one_le_two_pow]
  push_cast; exact le_rfl

end CorpCE


open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CorpCE
open IncentiveAwarePricing.CORP

lemma bidsBounded_EM : BidsBounded EM 1 σT := by
  intro n i
  rw [Subsingleton.elim i 0, pathLaw_eq, ae_iff]
  have hset : {ω : ℕ → Draw 1 1 | ¬ (record EM σT ω n).bid 0 ≤ 1} =
      (fun ω : ℕ → Draw 1 1 => ω n) ⁻¹'
        (Set.univ ×ˢ ({z : Fin 1 → ℝ | 1 < z 0} ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ
          (Set.univ ×ˢ Set.univ))))) := by
    ext ω; simp [record_bid]
  rw [hset, (measurePreserving_eval_infinitePi (fun _ : ℕ => drawLaw EM) n).measure_preimage
    (by measurability)]
  rw [drawLaw_rect, piNoise_lt, noiseLaw_Ioi_one]; simp

lemma deviate_truthful (i : Fin 1) (e : ℕ) : deviate σT i e = σT := by
  unfold deviate
  apply Function.update_eq_self_iff.mpr
  funext n h x v s
  simp [truthful]

lemma utilityMaximizing_EM (γ : ℝ) : UtilityMaximizing EM γ σT := by
  intro i e U' hU'
  rw [deviate_truthful] at hU'
  exact ⟨U', hU', le_rfl⟩

lemma strategyMeasurable_T : StrategyMeasurable σT := by
  intro i n
  simp only [truthful]
  fun_prop

lemma bidsDistinct_EM : BidsDistinct EM σT := by
  intro n i j hij
  exact absurd (Subsingleton.elim i j) hij

lemma exists_K (C : ℝ) (hC : 0 < C) :
    ∃ K : ℕ, 1 ≤ K ∧ 64 * C * (K:ℝ) ^ 2 < (20/11:ℝ) ^ K := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 (show (1:ℝ) < 20/11 by norm_num)
  have hev := (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 / (64 * C) by positivity)))
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp hev
  refine ⟨max K0 1, le_max_right _ _, ?_⟩
  have h := hK0 (max K0 1) (le_max_left _ _)
  have hpos : (0:ℝ) < (20/11) ^ (max K0 1) := by positivity
  rw [div_lt_div_iff₀ hpos (by positivity)] at h
  nlinarith

end CorpCE

open CorpCE IncentiveAwarePricing.CORP in
theorem solution : ¬ (∀ (Bp Bn M cmin cmax : ℝ) (f : ℝ → ℝ),
    0 < Bp → 0 < M → 0 < cmin → 0 < cmax → NoiseStanding Bn f → Assumption1 Bn f →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N d T : ℕ) (γ : ℝ), 1 ≤ N → 1 ≤ d → 2 ≤ T → 0 < γ → γ < 1 →
      ∀ D : Measure (Ctx d), FeatureLaw d cmin cmax D →
      ∀ β : Fin N → Ctx d, (∀ i, ‖β i‖ ≤ Bp) →
      ∀ (est : Estimator N d) (res : ℝ → ℝ),
        IsCORPEstimator f Bp est → EstimatorMeasurable est →
        IsReserveRule f res → Measurable res →
      ∀ σ : Strategy N d, StrategyMeasurable σ →
        BidsBounded ⟨Bp, Bn, f, D, β, est, res⟩ M σ →
        BidsDistinct ⟨Bp, Bn, f, D, β, est, res⟩ σ →
        UtilityMaximizing ⟨Bp, Bn, f, D, β, est, res⟩ γ σ →
        regret ⟨Bp, Bn, f, D, β, est, res⟩ σ T ≤
          C * N * d * (Real.log (T * d) * Real.log T +
            Real.log T ^ 2 / Real.log (1 / γ) ^ 2)) := by
  intro h
  obtain ⟨C, hC, hbound⟩ := h 10 1 1 (1/2) 2 fU (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) noiseStanding_fU assumption1_fU
  obtain ⟨K, hK1, hK⟩ := exists_K C hC
  have hT : 2 ≤ 2 ^ K := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK1
  have hb := hbound 1 1 (2 ^ K) (1/2) le_rfl le_rfl hT (by norm_num) (by norm_num)
    (Measure.dirac e1) featureLaw_dirac (fun _ => 0) (fun _ => by simp) estU resU
    isCORPEstimator_estU estU_measurable isReserveRule_resU resU_measurable
    σT strategyMeasurable_T bidsBounded_EM bidsDistinct_EM (utilityMaximizing_EM _)
  have hreg := regret_ge K
  change regret EM σT (2 ^ K) ≤ _ at hb
  -- compute the right-hand side
  have hL : Real.log (((2 ^ K : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) = K * Real.log 2 := by
    push_cast; rw [mul_one, Real.log_pow]
  have hL' : Real.log (((2 ^ K : ℕ) : ℝ)) = K * Real.log 2 := by
    push_cast; rw [Real.log_pow]
  have hg : Real.log (1 / (1/2 : ℝ)) = Real.log 2 := by norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  rw [hL, hL', hg] at hb
  have hrhs : ((K:ℝ) * Real.log 2 * (K * Real.log 2) +
      ((K:ℝ) * Real.log 2) ^ 2 / Real.log 2 ^ 2) = (K:ℝ)^2 * (Real.log 2 ^ 2 + 1) := by
    field_simp
  rw [hrhs] at hb
  push_cast at hb
  have hK2 : (2:ℝ) ^ K / 2 ≤ (2:ℝ) ^ K - 1 := by
    have : (2:ℝ) ≤ 2 ^ K := by exact_mod_cast hT
    linarith
  have hpow : ((2:ℝ) ^ K) * (10/11) ^ K = (20/11) ^ K := by
    rw [← mul_pow]; norm_num
  have hA : (20/11:ℝ) ^ K / 32 ≤ ((2:ℝ) ^ K - 1) * ((10/11:ℝ) ^ K / 16) := by
    have h0 : (0:ℝ) ≤ (10/11) ^ K / 16 := by positivity
    calc (20/11:ℝ) ^ K / 32 = ((2:ℝ) ^ K / 2) * ((10/11:ℝ) ^ K / 16) := by
          rw [← hpow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK2 h0
  have hB : C * 1 * 1 * ((K:ℝ) ^ 2 * (Real.log 2 ^ 2 + 1)) ≤ 2 * C * (K:ℝ) ^ 2 := by
    have : Real.log 2 ^ 2 ≤ 1 := by nlinarith
    have hK0 : (0:ℝ) ≤ (K:ℝ) ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left this (mul_nonneg hC.le hK0)
    nlinarith [h3]
  linarith
