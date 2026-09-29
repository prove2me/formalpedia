-- Prove2me | solution 1 for MeasureTheory.contDiffOn_integral_mul_log_sq_add_sq_halfSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/74e0f733-fd9d-5dee-884d-c88760b46fd3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_contDiffOn_integral_mul_log_sq_add_sq_halfSpace

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Set Filter Real
open scoped Topology

noncomputable section

namespace LogPot

def Lk (s ρ : ℝ) : ℝ := Real.log (s ^ 2 + ρ ^ 2)

noncomputable def θk (s ρ : ℝ) : ℝ := if 0 < ρ then π / 2 - Real.arctan (s / ρ) else (if s < 0 then π else 0)

def dLk (s ρ : ℝ) : ℝ := 2 * ρ / (s ^ 2 + ρ ^ 2)

def dθk (s ρ : ℝ) : ℝ := s / (s ^ 2 + ρ ^ 2)

theorem abs_θk_le (s ρ : ℝ) : |θk s ρ| ≤ π := by
  unfold θk
  split_ifs with h h'
  · have h1 := Real.arctan_lt_pi_div_two (s / ρ)
    have h2 := Real.neg_pi_div_two_lt_arctan (s / ρ)
    rw [abs_le]; constructor <;> linarith [Real.pi_pos]
  · rw [abs_of_nonneg Real.pi_pos.le]
  · simp [Real.pi_pos.le]

theorem abs_Lk_le {s ρ M : ℝ} (hs : s ≠ 0) (hρ : |ρ| ≤ M) :
    |Lk s ρ| ≤ |Real.log (s ^ 2)| + Real.log (1 + s ^ 2) + Real.log (1 + M ^ 2) := by
  have hs2 : 0 < s ^ 2 := by positivity
  have h1 : 0 ≤ Real.log (1 + s ^ 2) := Real.log_nonneg (by nlinarith)
  have h2 : 0 ≤ Real.log (1 + M ^ 2) := Real.log_nonneg (by nlinarith)
  unfold Lk
  by_cases hle : s ^ 2 + ρ ^ 2 < 1
  · have hlt0 : Real.log (s ^ 2 + ρ ^ 2) ≤ 0 := Real.log_nonpos (by positivity) hle.le
    have hge : Real.log (s ^ 2) ≤ Real.log (s ^ 2 + ρ ^ 2) := Real.log_le_log hs2 (by nlinarith)
    rw [abs_of_nonpos hlt0]
    have : |Real.log (s ^ 2)| = -Real.log (s ^ 2) := abs_of_nonpos (hge.trans hlt0)
    linarith
  · push Not at hle
    have hpos : 0 ≤ Real.log (s ^ 2 + ρ ^ 2) := Real.log_nonneg hle
    rw [abs_of_nonneg hpos]
    have hρ2 : ρ ^ 2 ≤ M ^ 2 := by
      have : |ρ| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hρ 2
      simpa [sq_abs] using this
    have hprod : s ^ 2 + ρ ^ 2 ≤ (1 + s ^ 2) * (1 + M ^ 2) := by nlinarith
    calc Real.log (s ^ 2 + ρ ^ 2) ≤ Real.log ((1 + s ^ 2) * (1 + M ^ 2)) :=
          Real.log_le_log (by linarith) hprod
      _ = Real.log (1 + s ^ 2) + Real.log (1 + M ^ 2) := Real.log_mul (by positivity) (by positivity)
      _ ≤ _ := by linarith [abs_nonneg (Real.log (s ^ 2))]

theorem integrableOn_logBound (R M : ℝ) :
    IntegrableOn (fun s : ℝ => |Real.log (s ^ 2)| + Real.log (1 + s ^ 2) + Real.log (1 + M ^ 2)) (Set.Icc (-R) R) := by
  have h1 : IntervalIntegrable (fun s : ℝ => |Real.log (s ^ 2)|) volume (-R) R := by
    have : (fun s : ℝ => |Real.log (s ^ 2)|) = fun s => |(2 : ℝ) * Real.log s| := by
      funext s; rw [Real.log_pow]; norm_num
    rw [this]
    exact (intervalIntegral.intervalIntegrable_log'.const_mul 2).abs
  have hc : Continuous fun s : ℝ => Real.log (1 + s ^ 2) + Real.log (1 + M ^ 2) := by
    refine Continuous.add ?_ continuous_const
    refine continuous_iff_continuousAt.mpr fun s => ?_
    exact (Real.continuousAt_log (by positivity)).comp (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2).continuousAt
  have h2 : IntervalIntegrable (fun s : ℝ => Real.log (1 + s ^ 2) + Real.log (1 + M ^ 2)) volume (-R) R :=
    hc.intervalIntegrable _ _
  by_cases hR : 0 ≤ R
  · have := (h1.add h2)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at this
    simpa [add_assoc] using this
  · rw [Set.Icc_eq_empty (by linarith)]
    exact integrableOn_empty

end LogPot

namespace LogPot

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem exists_bounds (k : E × ℝ → V) (hk : Continuous k) (hkc : HasCompactSupport k) :
    ∃ R C : ℝ, 0 ≤ C ∧ (∀ (e : E) (s : ℝ), R < |s| → k (e, s) = 0) ∧ ∀ p, ‖k p‖ ≤ C := by
  obtain ⟨C, hC⟩ := hk.bounded_above_of_compact_support hkc
  obtain ⟨R, hR⟩ := ((hkc.image continuous_snd).isBounded).subset_closedBall (0 : ℝ)
  refine ⟨R, max C 0, le_max_right _ _, fun e s hs => ?_, fun p => (hC p).trans (le_max_left _ _)⟩
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have : s ∈ Metric.closedBall (0 : ℝ) R := hR ⟨(e, s), h, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith

theorem measurable_Lk (ρ : ℝ) : Measurable fun s : ℝ => Lk s ρ :=
  Real.measurable_log.comp (by fun_prop)

theorem continuous_Lk_left {s : ℝ} (hs : s ≠ 0) : Continuous fun ρ : ℝ => Lk s ρ := by
  refine continuous_iff_continuousAt.mpr fun ρ => ?_
  exact (Real.continuousAt_log (by positivity)).comp
    (by fun_prop : Continuous fun ρ : ℝ => s ^ 2 + ρ ^ 2).continuousAt

theorem continuous_Lk_right {ρ : ℝ} (hρ : ρ ≠ 0) : Continuous fun s : ℝ => Lk s ρ := by
  refine continuous_iff_continuousAt.mpr fun s => ?_
  exact (Real.continuousAt_log (by positivity)).comp
    (by fun_prop : Continuous fun s : ℝ => s ^ 2 + ρ ^ 2).continuousAt

theorem θk_of_pos {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) : θk s ρ = π / 2 - Real.arctan (s / ρ) := if_pos hρ

theorem measurable_θk (ρ : ℝ) : Measurable fun s : ℝ => θk s ρ := by
  by_cases h : 0 < ρ
  · simp only [θk_of_pos h]
    exact (continuous_const.sub (Real.continuous_arctan.comp (continuous_id.div_const ρ))).measurable
  · have : (fun s : ℝ => θk s ρ) = fun s => if s < 0 then π else 0 := by
      funext s; exact if_neg h
    rw [this]
    exact Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem continuous_θk_right {ρ : ℝ} (hρ : 0 < ρ) : Continuous fun s : ℝ => θk s ρ := by
  simp only [θk_of_pos hρ]
  exact continuous_const.sub (Real.continuous_arctan.comp (continuous_id.div_const ρ))

theorem continuousWithinAt_θk {s : ℝ} (hs : s ≠ 0) {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) :
    ContinuousWithinAt (fun ρ : ℝ => θk s ρ) (Set.Ici 0) ρ₀ := by
  have hform : ∀ ρ : ℝ, 0 < ρ → θk s ρ = π / 2 - Real.arctan (s * ρ⁻¹) := fun ρ hρ => by
    rw [θk_of_pos hρ, ← div_eq_mul_inv]
  rcases hρ₀.eq_or_lt with h0 | hpos
  · subst h0
    rw [← continuousWithinAt_Ioi_iff_Ici]
    show Tendsto (fun ρ : ℝ => θk s ρ) (𝓝[Set.Ioi 0] 0) (𝓝 (θk s 0))
    have hev : (fun ρ : ℝ => π / 2 - Real.arctan (s * ρ⁻¹)) =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)] fun ρ => θk s ρ :=
      eventually_nhdsWithin_of_forall fun ρ hρ => (hform ρ hρ).symm
    refine Tendsto.congr' hev ?_
    have h0 : θk s 0 = if s < 0 then π else 0 := if_neg (lt_irrefl 0)
    rw [h0]
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · rw [if_pos hneg]
      have h1 : Tendsto (fun ρ : ℝ => s * ρ⁻¹) (𝓝[Set.Ioi 0] 0) atBot :=
        (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop_of_neg hneg
      have h2 : Tendsto (fun ρ : ℝ => Real.arctan (s * ρ⁻¹)) (𝓝[Set.Ioi 0] 0) (𝓝 (-(π / 2))) :=
        tendsto_nhds_of_tendsto_nhdsWithin (Real.tendsto_arctan_atBot.comp h1)
      have := (tendsto_const_nhds (x := π / 2)).sub h2
      convert this using 2 <;> try rfl
      ring
    · rw [if_neg (not_lt.mpr hpos.le)]
      have h1 : Tendsto (fun ρ : ℝ => s * ρ⁻¹) (𝓝[Set.Ioi 0] 0) atTop :=
        (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hpos
      have h2 : Tendsto (fun ρ : ℝ => Real.arctan (s * ρ⁻¹)) (𝓝[Set.Ioi 0] 0) (𝓝 (π / 2)) :=
        tendsto_nhds_of_tendsto_nhdsWithin (Real.tendsto_arctan_atTop.comp h1)
      have := (tendsto_const_nhds (x := π / 2)).sub h2
      convert this using 2 <;> try rfl
      ring
  · have hev : (fun ρ : ℝ => π / 2 - Real.arctan (s * ρ⁻¹)) =ᶠ[𝓝 ρ₀] fun ρ => θk s ρ :=
      (lt_mem_nhds hpos).mono fun ρ hρ => (hform ρ hρ).symm
    have hc : ContinuousAt (fun ρ : ℝ => π / 2 - Real.arctan (s * ρ⁻¹)) ρ₀ :=
      continuousAt_const.sub ((Real.continuous_arctan.continuousAt).comp
        (continuousAt_const.mul (continuousAt_inv₀ hpos.ne')))
    exact (hc.congr hev).continuousWithinAt

end LogPot

namespace LogPot

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem ae_ne_zero : ∀ᵐ a : ℝ, a ≠ 0 := by
  rw [ae_iff]
  have : {a : ℝ | ¬a ≠ 0} = {0} := by ext a; simp
  rw [this, measure_singleton]

theorem lt_abs_of_not_mem_Icc {R a : ℝ} (h : a ∉ Set.Icc (-R) R) : R < |a| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs a)
  · exact h.trans_le (le_abs_self a)

theorem log_dom {k : E × ℝ → V} {R C : ℝ} (hC : 0 ≤ C) (hR : ∀ (e : E) (s : ℝ), R < |s| → k (e, s) = 0)
    (hCk : ∀ p, ‖k p‖ ≤ C) {M : ℝ} (x : E × ℝ) (hx : |x.2| ≤ M) :
    ∀ᵐ a : ℝ, ‖(Lk a x.2) • k (x.1, a)‖ ≤
      (Set.Icc (-R) R).indicator (fun a => C * (|Real.log (a ^ 2)| + Real.log (1 + a ^ 2) + Real.log (1 + M ^ 2))) a := by
  filter_upwards [ae_ne_zero] with a ha
  by_cases hmem : a ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hmem, norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (hCk _) (abs_Lk_le ha hx) (abs_nonneg _) hC
  · rw [Set.indicator_of_notMem hmem, hR _ _ (lt_abs_of_not_mem_Icc hmem), smul_zero, norm_zero]

theorem theta_dom {k : E × ℝ → V} {R C : ℝ} (hC : 0 ≤ C) (hR : ∀ (e : E) (s : ℝ), R < |s| → k (e, s) = 0)
    (hCk : ∀ p, ‖k p‖ ≤ C) (x : E × ℝ) :
    ∀ a : ℝ, ‖(θk a x.2) • k (x.1, a)‖ ≤ (Set.Icc (-R) R).indicator (fun _ => π * C) a := by
  intro a
  by_cases hmem : a ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hmem, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_θk_le _ _) (hCk _) (norm_nonneg _) Real.pi_pos.le
  · rw [Set.indicator_of_notMem hmem, hR _ _ (lt_abs_of_not_mem_Icc hmem), smul_zero, norm_zero]

omit [CompleteSpace V] in
theorem aesm_Lk (k : E × ℝ → V) (hk : Continuous k) (x : E × ℝ) :
    AEStronglyMeasurable (fun a : ℝ => (Lk a x.2) • k (x.1, a)) volume :=
  (measurable_Lk x.2).aestronglyMeasurable.smul
    (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

omit [CompleteSpace V] in
theorem aesm_θk (k : E × ℝ → V) (hk : Continuous k) (x : E × ℝ) :
    AEStronglyMeasurable (fun a : ℝ => (θk a x.2) • k (x.1, a)) volume :=
  (measurable_θk x.2).aestronglyMeasurable.smul
    (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

theorem integrable_logBound (R M C : ℝ) :
    Integrable ((Set.Icc (-R) R).indicator
      (fun a : ℝ => C * (|Real.log (a ^ 2)| + Real.log (1 + a ^ 2) + Real.log (1 + M ^ 2)))) volume := by
  have h : IntegrableOn (fun a : ℝ => C * (|Real.log (a ^ 2)| + Real.log (1 + a ^ 2) + Real.log (1 + M ^ 2)))
      (Set.Icc (-R) R) := (integrableOn_logBound R M).const_mul C
  exact h.integrable_indicator measurableSet_Icc

theorem integrable_Lk_smul (k : E × ℝ → V) (hk : Continuous k) (hkc : HasCompactSupport k) (x : E × ℝ) :
    Integrable (fun a : ℝ => (Lk a x.2) • k (x.1, a)) volume := by
  obtain ⟨R, C, hC, hR, hCk⟩ := exists_bounds k hk hkc
  exact (integrable_logBound R |x.2| C).mono' (aesm_Lk k hk x) (log_dom hC hR hCk x le_rfl)

theorem integrable_θk_smul (k : E × ℝ → V) (hk : Continuous k) (hkc : HasCompactSupport k) (x : E × ℝ) :
    Integrable (fun a : ℝ => (θk a x.2) • k (x.1, a)) volume := by
  obtain ⟨R, C, hC, hR, hCk⟩ := exists_bounds k hk hkc
  refine Integrable.mono' (g := (Set.Icc (-R) R).indicator fun _ => π * C) ?_ (aesm_θk k hk x)
    (Filter.Eventually.of_forall (theta_dom hC hR hCk x))
  exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc

theorem continuousAt_FL (k : E × ℝ → V) (hk : Continuous k) (hkc : HasCompactSupport k) (p₀ : E × ℝ) :
    ContinuousAt (fun p : E × ℝ => ∫ s, (Lk s p.2) • k (p.1, s)) p₀ := by
  obtain ⟨R, C, hC, hR, hCk⟩ := exists_bounds k hk hkc
  set M : ℝ := |p₀.2| + 1 with hM
  have hnear : ∀ᶠ x in 𝓝 p₀, |x.2| ≤ M := by
    have hc : ContinuousAt (fun x : E × ℝ => |x.2|) p₀ := (continuous_abs.comp continuous_snd).continuousAt
    have : ∀ᶠ x in 𝓝 p₀, |x.2| < M := hc.eventually_lt continuousAt_const (by simp [M])
    exact this.mono fun x hx => hx.le
  refine continuousAt_of_dominated (Filter.Eventually.of_forall fun x => aesm_Lk k hk x)
    (hnear.mono fun x hx => log_dom hC hR hCk x hx) (integrable_logBound R M C) ?_
  filter_upwards [ae_ne_zero] with a ha
  exact (((continuous_Lk_left ha).comp continuous_snd).smul
    (hk.comp (continuous_fst.prodMk continuous_const))).continuousAt

theorem continuousWithinAt_FT (k : E × ℝ → V) (hk : Continuous k) (hkc : HasCompactSupport k) (p₀ : E × ℝ)
    (hp₀ : 0 ≤ p₀.2) :
    ContinuousWithinAt (fun p : E × ℝ => ∫ s, (θk s p.2) • k (p.1, s)) {p : E × ℝ | 0 ≤ p.2} p₀ := by
  obtain ⟨R, C, hC, hR, hCk⟩ := exists_bounds k hk hkc
  refine continuousWithinAt_of_dominated (Filter.Eventually.of_forall fun x => aesm_θk k hk x)
    (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall (theta_dom hC hR hCk x))
    ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc) ?_
  filter_upwards [ae_ne_zero] with a ha
  refine ContinuousWithinAt.smul ?_ (hk.comp (continuous_fst.prodMk continuous_const)).continuousWithinAt
  exact (continuousWithinAt_θk ha hp₀).comp continuous_snd.continuousWithinAt fun x hx => hx

end LogPot

namespace LogPot

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dsh (h : E × ℝ → ℂ) : E × ℝ → ℂ := fun q => fderiv ℝ h q ((0 : E), (1 : ℝ))

def Deh (h : E × ℝ → ℂ) : E × ℝ → (E →L[ℝ] ℂ) := fun q => (fderiv ℝ h q).comp (ContinuousLinearMap.inl ℝ E ℝ)

theorem contDiff_dsh {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) : ContDiff ℝ (⊤ : ℕ∞) (dsh h) :=
  (hh.fderiv_right (by exact_mod_cast le_top)).clm_apply contDiff_const

theorem hasCompactSupport_dsh {h : E × ℝ → ℂ} (hhc : HasCompactSupport h) : HasCompactSupport (dsh h) :=
  (hhc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E × ℝ →L[ℝ] ℂ => L ((0 : E), (1 : ℝ))) rfl

theorem continuous_Deh {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) : Continuous (Deh h) :=
  (hh.continuous_fderiv (by simp)).clm_comp continuous_const

theorem hasCompactSupport_Deh {h : E × ℝ → ℂ} (hhc : HasCompactSupport h) : HasCompactSupport (Deh h) :=
  (hhc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E × ℝ →L[ℝ] ℂ => L.comp (ContinuousLinearMap.inl ℝ E ℝ))
    (ContinuousLinearMap.zero_comp _)

theorem Deh_apply (h : E × ℝ → ℂ) (q : E × ℝ) (u : E) : Deh h q u = fderiv ℝ h q ((u, 0) : E × ℝ) := by
  simp [Deh]

def deh (h : E × ℝ → ℂ) (u : E) : E × ℝ → ℂ := fun q => fderiv ℝ h q ((u, 0) : E × ℝ)

theorem contDiff_deh {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (u : E) : ContDiff ℝ (⊤ : ℕ∞) (deh h u) :=
  (hh.fderiv_right (by exact_mod_cast le_top)).clm_apply contDiff_const

theorem hasCompactSupport_deh {h : E × ℝ → ℂ} (hhc : HasCompactSupport h) (u : E) : HasCompactSupport (deh h u) :=
  (hhc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E × ℝ →L[ℝ] ℂ => L ((u, 0) : E × ℝ)) rfl

theorem hasDerivAt_Lk_right {a ρ : ℝ} (h : a ^ 2 + ρ ^ 2 ≠ 0) :
    HasDerivAt (fun ρ : ℝ => Lk a ρ) (dLk a ρ) ρ := by
  have h1 : HasDerivAt (fun ρ : ℝ => a ^ 2 + ρ ^ 2) (2 * ρ) ρ := by
    simpa using ((hasDerivAt_pow 2 ρ).const_add (a ^ 2))
  have := h1.log h
  unfold Lk dLk
  convert this using 1 <;> try rfl

theorem hasDerivAt_Lk_left {a ρ : ℝ} (h : a ^ 2 + ρ ^ 2 ≠ 0) :
    HasDerivAt (fun a : ℝ => Lk a ρ) (2 * a / (a ^ 2 + ρ ^ 2)) a := by
  have h1 : HasDerivAt (fun a : ℝ => a ^ 2 + ρ ^ 2) (2 * a) a := by
    simpa using ((hasDerivAt_pow 2 a).add_const (ρ ^ 2))
  have := h1.log h
  unfold Lk
  convert this using 1 <;> try rfl

theorem hasDerivAt_θk_left {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ) :
    HasDerivAt (fun a : ℝ => θk a ρ) (-(ρ / (a ^ 2 + ρ ^ 2))) a := by
  simp only [θk_of_pos hρ]
  have h1 : HasDerivAt (fun a : ℝ => Real.arctan (a / ρ)) (1 / (1 + (a / ρ) ^ 2) * (1 / ρ)) a :=
    ((hasDerivAt_id a).div_const ρ).arctan
  have h2 := h1.const_sub (π / 2)
  convert h2 using 1 <;> first | rfl | ring1 | (field_simp; ring1)

theorem hasDerivAt_θk_right {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ) :
    HasDerivAt (fun ρ : ℝ => θk a ρ) (dθk a ρ) ρ := by
  have hev : (fun ρ : ℝ => π / 2 - Real.arctan (a * ρ⁻¹)) =ᶠ[𝓝 ρ] fun ρ => θk a ρ :=
    (lt_mem_nhds hρ).mono fun ρ' hρ' => by
      show π / 2 - Real.arctan (a * ρ'⁻¹) = θk a ρ'
      rw [θk_of_pos hρ' a, ← div_eq_mul_inv]
  have h1 : HasDerivAt (fun ρ : ℝ => Real.arctan (a * ρ⁻¹)) (1 / (1 + (a * ρ⁻¹) ^ 2) * (a * (-(ρ ^ 2)⁻¹))) ρ :=
    ((hasDerivAt_inv hρ.ne').const_mul a).arctan
  have h2 := h1.const_sub (π / 2)
  refine (h2.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  unfold dθk
  field_simp
  ring

end LogPot

namespace LogPot

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_slice {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (e : E) (a : ℝ) :
    HasDerivAt (fun a : ℝ => h (e, a)) (dsh h (e, a)) a := by
  have hc : HasDerivAt (fun a : ℝ => ((e, a) : E × ℝ)) ((0 : E), (1 : ℝ)) a :=
    (hasDerivAt_const a e).prodMk (hasDerivAt_id a)
  exact ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt a hc

theorem integral_eq_intervalIntegral {f : ℝ → ℂ} {R : ℝ} (hf : ∀ a, R < |a| → f a = 0) :
    ∫ a, f a = ∫ a in (-(|R| + 1))..(|R| + 1), f a := by
  rw [intervalIntegral.integral_of_le (by linarith [abs_nonneg R]), setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro a ha
  apply hf
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at ha
  rcases ha with ha | ha
  · calc R ≤ |R| := le_abs_self R
      _ < |R| + 1 := by linarith
      _ ≤ -a := by linarith
      _ ≤ |a| := neg_le_abs a
  · calc R ≤ |R| := le_abs_self R
      _ < a := by linarith
      _ ≤ |a| := le_abs_self a

theorem ibp {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (e : E)
    (v v' : ℝ → ℝ) (hv : ∀ a, HasDerivAt v (v' a) a) (hvc : Continuous v) (hv'c : Continuous v') :
    ∫ a, (v' a) • h (e, a) = -∫ a, (v a) • dsh h (e, a) := by
  obtain ⟨R₁, C₁, -, hR₁, -⟩ := exists_bounds h hh.continuous hhc
  obtain ⟨R₂, C₂, -, hR₂, -⟩ := exists_bounds (dsh h) (contDiff_dsh hh).continuous (hasCompactSupport_dsh hhc)
  set R : ℝ := max |R₁| |R₂| with hRdef
  have h1 : ∀ a, R < |a| → h (e, a) = 0 := fun a ha =>
    hR₁ e a (lt_of_le_of_lt ((le_abs_self R₁).trans (le_max_left _ _)) ha)
  have h2 : ∀ a, R < |a| → dsh h (e, a) = 0 := fun a ha =>
    hR₂ e a (lt_of_le_of_lt ((le_abs_self R₂).trans (le_max_right _ _)) ha)
  set A : ℝ := |R| + 1 with hA
  have hA1 : R < |A| := by rw [hA, abs_of_nonneg (by positivity)]; linarith [le_abs_self R]
  have hA2 : R < |(-A)| := by rw [abs_neg]; exact hA1
  have lhs : ∫ a, (v' a) • h (e, a) = ∫ a in (-A)..A, h (e, a) * ((v' a : ℝ) : ℂ) := by
    rw [integral_eq_intervalIntegral (R := R) (f := fun a => (v' a) • h (e, a))
      (fun a ha => by show (v' a) • h (e, a) = 0; rw [h1 a ha, smul_zero])]
    congr 1; funext a; rw [Complex.real_smul, mul_comm]
  have rhs : ∫ a, (v a) • dsh h (e, a) = ∫ a in (-A)..A, dsh h (e, a) * ((v a : ℝ) : ℂ) := by
    rw [integral_eq_intervalIntegral (R := R) (f := fun a => (v a) • dsh h (e, a))
      (fun a ha => by show (v a) • dsh h (e, a) = 0; rw [h2 a ha, smul_zero])]
    congr 1; funext a; rw [Complex.real_smul, mul_comm]
  rw [lhs, rhs, intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun a => h (e, a))
    (u' := fun a => dsh h (e, a)) (v := fun a => ((v a : ℝ) : ℂ)) (v' := fun a => ((v' a : ℝ) : ℂ))
    (fun a _ => hasDerivAt_slice hh e a) (fun a _ => (hv a).ofReal_comp)
    (((contDiff_dsh hh).continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    ((Complex.continuous_ofReal.comp hv'c).intervalIntegrable _ _),
    h1 A hA1, h1 (-A) hA2]
  simp

theorem ibp_dLk {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (e : E)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ a, (dLk a ρ) • h (e, a) = (2 : ℝ) • ∫ a, (θk a ρ) • dsh h (e, a) := by
  have key := ibp hh hhc e (fun a => θk a ρ) (fun a => -(ρ / (a ^ 2 + ρ ^ 2))) (hasDerivAt_θk_left hρ)
    (continuous_θk_right hρ) ?_
  · have : (fun a : ℝ => (dLk a ρ) • h (e, a)) = fun a => (-2 : ℝ) • ((-(ρ / (a ^ 2 + ρ ^ 2))) • h (e, a)) := by
      funext a; rw [smul_smul]; congr 1; unfold dLk; ring
    rw [this, integral_smul, key, smul_neg, neg_smul, neg_neg]
  · exact Continuous.neg (continuous_const.div (by fun_prop) fun a => by positivity)

theorem ibp_dθk {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (e : E)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ a, (dθk a ρ) • h (e, a) = (-(1 / 2) : ℝ) • ∫ a, (Lk a ρ) • dsh h (e, a) := by
  have hne : ∀ a : ℝ, a ^ 2 + ρ ^ 2 ≠ 0 := fun a => by positivity
  have key := ibp hh hhc e (fun a => (1 / 2) * Lk a ρ) (fun a => dθk a ρ)
    (fun a => by
      have := (hasDerivAt_Lk_left (ρ := ρ) (hne a)).const_mul (1 / 2)
      refine this.congr_deriv ?_
      unfold dθk; field_simp)
    ((continuous_Lk_right hρ.ne').const_smul (1 / 2 : ℝ) |>.congr fun a => by simp [smul_eq_mul])
    (continuous_id.div (by fun_prop) hne |>.congr fun a => by simp [dθk])
  rw [key, ← integral_smul, ← integral_neg]
  congr 1; funext a
  show -(((1 / 2 : ℝ) * Lk a ρ) • dsh h (e, a)) = _
  rw [smul_smul, ← neg_smul]
  congr 1; ring

end LogPot

namespace LogPot

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sndC : E × ℝ →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ E ℝ)

theorem sndC_apply (v : E × ℝ) : (sndC : E × ℝ →L[ℝ] ℂ) v = (v.2 : ℂ) := rfl

theorem norm_sndC_le : ‖(sndC : E × ℝ →L[ℝ] ℂ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [sndC_apply, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |v.2| = ‖v.2‖ := rfl
    _ ≤ ‖v‖ := norm_snd_le v

theorem hasFDerivAt_op (K dK : ℝ → ℝ → ℝ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hKc : ∀ ρ : ℝ, 0 < ρ → Continuous fun a : ℝ => K a ρ)
    (hdKc : ∀ ρ : ℝ, 0 < ρ → Continuous fun a : ℝ => dK a ρ)
    (hKd : ∀ (a ρ : ℝ), 0 < ρ → HasDerivAt (fun ρ : ℝ => K a ρ) (dK a ρ) ρ)
    (B : ℝ → ℝ) (hB : ∀ R : ℝ, IntegrableOn B (Set.Icc (-R) R) volume)
    (hKB : ∀ᵐ a : ℝ, ∀ ρ : ℝ, ρ₀ / 2 < ρ → ρ < ρ₀ + ρ₀ / 2 → |K a ρ| ≤ B a)
    (hdKB : ∀ (a ρ : ℝ), 0 < ρ → |dK a ρ| ≤ 2 / ρ)
    {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (e : E) :
    HasFDerivAt (fun p : E × ℝ => ∫ a, (K a p.2) • h (p.1, a))
      ((∫ a, (K a ρ₀) • Deh h (e, a)).comp (ContinuousLinearMap.fst ℝ E ℝ) +
        (∫ a, (dK a ρ₀) • h (e, a)) • (sndC : E × ℝ →L[ℝ] ℂ)) (e, ρ₀) := by

  obtain ⟨R₁, C₁, hC₁, hR₁, hCk₁⟩ := exists_bounds h hh.continuous hhc
  obtain ⟨R₂, C₂, hC₂, hR₂, hCk₂⟩ := exists_bounds (Deh h) (continuous_Deh hh) (hasCompactSupport_Deh hhc)
  set R : ℝ := max |R₁| |R₂| with hRdef
  have hz1 : ∀ (e' : E) (a : ℝ), R < |a| → h (e', a) = 0 := fun e' a ha =>
    hR₁ e' a (lt_of_le_of_lt ((le_abs_self R₁).trans (le_max_left _ _)) ha)
  have hz2 : ∀ (e' : E) (a : ℝ), R < |a| → Deh h (e', a) = 0 := fun e' a ha =>
    hR₂ e' a (lt_of_le_of_lt ((le_abs_self R₂).trans (le_max_right _ _)) ha)

  set p₀ : E × ℝ := (e, ρ₀) with hp₀
  set s : Set (E × ℝ) := Metric.ball p₀ (ρ₀ / 2) with hsdef
  have hs : s ∈ 𝓝 p₀ := Metric.ball_mem_nhds p₀ (by linarith)
  have hs2 : ∀ x ∈ s, ρ₀ / 2 < x.2 ∧ x.2 < ρ₀ + ρ₀ / 2 := by
    intro x hx
    have h1 : dist x.2 ρ₀ < ρ₀ / 2 := lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hx
    rw [Real.dist_eq, abs_lt] at h1
    constructor <;> linarith
  have hspos : ∀ x ∈ s, 0 < x.2 := fun x hx => by linarith [(hs2 x hx).1]

  set F' : E × ℝ → ℝ → (E × ℝ →L[ℝ] ℂ) := fun x a =>
    (K a x.2) • ((Deh h (x.1, a)).comp (ContinuousLinearMap.fst ℝ E ℝ)) +
      (dK a x.2) • ((h (x.1, a)) • (sndC : E × ℝ →L[ℝ] ℂ)) with hF'
  have hdiff : ∀ (a : ℝ) (x : E × ℝ), 0 < x.2 →
      HasFDerivAt (fun y : E × ℝ => (K a y.2) • h (y.1, a)) (F' x a) x := by
    intro a x hx
    have hK : HasFDerivAt (fun y : E × ℝ => K a y.2)
        ((dK a x.2) • (ContinuousLinearMap.snd ℝ E ℝ)) x := by
      have := ((hKd a x.2 hx).hasFDerivAt).comp x (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
      refine this.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      simp [mul_comm]
    have hH : HasFDerivAt (fun y : E × ℝ => h (y.1, a))
        ((Deh h (x.1, a)).comp (ContinuousLinearMap.fst ℝ E ℝ)) x := by
      have hi : HasFDerivAt (fun y : E × ℝ => ((y.1, a) : E × ℝ))
          ((ContinuousLinearMap.fst ℝ E ℝ).prod (0 : E × ℝ →L[ℝ] ℝ)) x :=
        hasFDerivAt_fst.prodMk (hasFDerivAt_const a x)
      have := ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x hi
      refine this.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      simp [Deh]
    have := hK.smul hH
    refine this.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [F', sndC_apply]
    ring

  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F := fun (x : E × ℝ) (a : ℝ) => (K a x.2) • h (x.1, a)) (F' := F') (x₀ := p₀)
    (bound := (Set.Icc (-R) R).indicator fun a => B a * C₂ + (4 / ρ₀) * C₁) hs ?_ ?_ ?_ ?_ ?_ ?_
  ·
    refine key.congr_fderiv ?_
    have hint1 : Integrable (fun a : ℝ => (K a ρ₀) • ((Deh h (e, a)).comp (ContinuousLinearMap.fst ℝ E ℝ))) := by
      refine Continuous.integrable_of_hasCompactSupport
        (((hKc ρ₀ hρ₀).smul (((continuous_Deh hh).comp (continuous_const.prodMk continuous_id)).clm_comp
          continuous_const))) ?_
      exact HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-R) R)) fun a ha => by
        show (K a ρ₀) • ((Deh h (e, a)).comp (ContinuousLinearMap.fst ℝ E ℝ)) = 0
        exact ContinuousLinearMap.ext fun v => by simp [hz2 e a (lt_abs_of_not_mem_Icc ha)]
    have hint2 : Integrable (fun a : ℝ => (dK a ρ₀) • ((h (e, a)) • (sndC : E × ℝ →L[ℝ] ℂ))) := by
      refine Continuous.integrable_of_hasCompactSupport
        ((hdKc ρ₀ hρ₀).smul ((hh.continuous.comp (continuous_const.prodMk continuous_id)).smul
          continuous_const)) ?_
      exact HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-R) R)) fun a ha => by
        show (dK a ρ₀) • ((h (e, a)) • (sndC : E × ℝ →L[ℝ] ℂ)) = 0
        exact ContinuousLinearMap.ext fun v => by simp [hz1 e a (lt_abs_of_not_mem_Icc ha)]
    show (∫ a, F' p₀ a) = _
    simp only [hF', hp₀]
    rw [integral_add hint1 hint2]
    congr 1
    · have hint0 : Integrable (fun a : ℝ => (K a ρ₀) • Deh h (e, a)) := by
        refine Continuous.integrable_of_hasCompactSupport
          ((hKc ρ₀ hρ₀).smul ((continuous_Deh hh).comp (continuous_const.prodMk continuous_id))) ?_
        exact HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-R) R)) fun a ha => by
          show (K a ρ₀) • Deh h (e, a) = 0
          exact ContinuousLinearMap.ext fun v => by simp [hz2 e a (lt_abs_of_not_mem_Icc ha)]
      have := ((ContinuousLinearMap.compL ℝ (E × ℝ) E ℂ).flip (ContinuousLinearMap.fst ℝ E ℝ)).integral_comp_comm
        hint0
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, map_smul] at this
      exact this
    · simp_rw [← smul_assoc]
      rw [integral_smul_const]
  ·
    filter_upwards [hs] with x hx
    exact ((hKc x.2 (hspos x hx)).smul (hh.continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  ·
    refine Continuous.integrable_of_hasCompactSupport
      ((hKc ρ₀ hρ₀).smul (hh.continuous.comp (continuous_const.prodMk continuous_id))) ?_
    exact HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-R) R)) fun a ha => by
      show (K a ρ₀) • h (e, a) = 0
      rw [hz1 e a (lt_abs_of_not_mem_Icc ha), smul_zero]
  ·
    haveI : SecondCountableTopologyEither ℝ (E × ℝ →L[ℝ] ℂ) := secondCountableTopologyEither_of_left ℝ _
    have hc : Continuous fun a : ℝ => (K a ρ₀) • ((Deh h (e, a)).comp (ContinuousLinearMap.fst ℝ E ℝ)) +
        (dK a ρ₀) • ((h (e, a)) • (sndC : E × ℝ →L[ℝ] ℂ)) :=
      ((hKc ρ₀ hρ₀).smul (((continuous_Deh hh).comp (continuous_const.prodMk continuous_id)).clm_comp
        continuous_const)).add
        ((hdKc ρ₀ hρ₀).smul ((hh.continuous.comp (continuous_const.prodMk continuous_id)).smul continuous_const))
    exact hc.aestronglyMeasurable
  ·
    filter_upwards [hKB] with a haK
    intro x hx
    obtain ⟨hx1, hx2⟩ := hs2 x hx
    have hxpos := hspos x hx
    by_cases hmem : a ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hmem]
      show ‖(K a x.2) • ((Deh h (x.1, a)).comp (ContinuousLinearMap.fst ℝ E ℝ)) +
        (dK a x.2) • ((h (x.1, a)) • (sndC : E × ℝ →L[ℝ] ℂ))‖ ≤ B a * C₂ + 4 / ρ₀ * C₁
      have hBa : |K a x.2| ≤ B a := haK x.2 hx1 hx2
      have hBnn : 0 ≤ B a := (abs_nonneg _).trans hBa
      have hd : |dK a x.2| ≤ 4 / ρ₀ := by
        refine (hdKB a x.2 hxpos).trans ?_
        rw [div_le_div_iff₀ hxpos hρ₀]
        linarith
      have h1 : ‖(K a x.2) • ((Deh h (x.1, a)).comp (ContinuousLinearMap.fst ℝ E ℝ))‖ ≤ B a * C₂ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hBnn hC₂) fun v => ?_
        show ‖(K a x.2) • (Deh h (x.1, a) v.1)‖ ≤ B a * C₂ * ‖v‖
        rw [norm_smul, Real.norm_eq_abs]
        calc |K a x.2| * ‖Deh h (x.1, a) v.1‖ ≤ B a * (‖Deh h (x.1, a)‖ * ‖v.1‖) :=
              mul_le_mul hBa (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) hBnn
          _ ≤ B a * (C₂ * ‖v‖) := by
              gcongr
              · exact hCk₂ _
              · exact norm_fst_le v
          _ = B a * C₂ * ‖v‖ := by ring
      have h2 : ‖(dK a x.2) • ((h (x.1, a)) • (sndC : E × ℝ →L[ℝ] ℂ))‖ ≤ 4 / ρ₀ * C₁ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        show ‖(dK a x.2) • ((h (x.1, a)) • ((sndC : E × ℝ →L[ℝ] ℂ) v))‖ ≤ 4 / ρ₀ * C₁ * ‖v‖
        rw [norm_smul, norm_smul, Real.norm_eq_abs, sndC_apply, Complex.norm_real, Real.norm_eq_abs]
        calc |dK a x.2| * (‖h (x.1, a)‖ * |v.2|) ≤ 4 / ρ₀ * (C₁ * ‖v‖) := by
              refine mul_le_mul hd (mul_le_mul (hCk₁ _) ?_ (abs_nonneg _) hC₁) (by positivity) (by positivity)
              exact (norm_snd_le v)
          _ = 4 / ρ₀ * C₁ * ‖v‖ := by ring
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    · rw [Set.indicator_of_notMem hmem]
      have hlt := lt_abs_of_not_mem_Icc hmem
      have hzero : F' x a = 0 := ContinuousLinearMap.ext fun v => by
        show (K a x.2) • (Deh h (x.1, a) v.1) + (dK a x.2) • ((h (x.1, a)) • ((sndC : E × ℝ →L[ℝ] ℂ) v)) = 0
        rw [hz1 x.1 a hlt, hz2 x.1 a hlt, ContinuousLinearMap.zero_apply, smul_zero, zero_smul, smul_zero, add_zero]
      rw [hzero, norm_zero]
  ·
    have hI : IntegrableOn (fun a : ℝ => B a * C₂ + 4 / ρ₀ * C₁) (Set.Icc (-R) R) volume :=
      ((hB R).mul_const C₂).add (integrableOn_const (by simp))
    exact hI.integrable_indicator measurableSet_Icc
  ·
    exact Filter.Eventually.of_forall fun a x hx => hdiff a x (hspos x hx)

end LogPot

namespace LogPot

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def FLs (h : E × ℝ → ℂ) (p : E × ℝ) : ℂ := ∫ a, (Lk a p.2) • h (p.1, a)

def FTs (h : E × ℝ → ℂ) (p : E × ℝ) : ℂ := ∫ a, (θk a p.2) • h (p.1, a)

def DL (h : E × ℝ → ℂ) (p : E × ℝ) : E × ℝ →L[ℝ] ℂ :=
  (∫ a, (Lk a p.2) • Deh h (p.1, a)).comp (ContinuousLinearMap.fst ℝ E ℝ) +
    ((2 : ℝ) • ∫ a, (θk a p.2) • dsh h (p.1, a)) • (sndC : E × ℝ →L[ℝ] ℂ)

def DT (h : E × ℝ → ℂ) (p : E × ℝ) : E × ℝ →L[ℝ] ℂ :=
  (∫ a, (θk a p.2) • Deh h (p.1, a)).comp (ContinuousLinearMap.fst ℝ E ℝ) +
    ((-(1 / 2) : ℝ) • ∫ a, (Lk a p.2) • dsh h (p.1, a)) • (sndC : E × ℝ →L[ℝ] ℂ)

theorem continuous_dLk_right {ρ : ℝ} (hρ : 0 < ρ) : Continuous fun a : ℝ => dLk a ρ := by
  unfold dLk
  exact continuous_const.div (by fun_prop) fun a => by positivity

theorem continuous_dθk_right {ρ : ℝ} (hρ : 0 < ρ) : Continuous fun a : ℝ => dθk a ρ := by
  unfold dθk
  exact continuous_id.div (by fun_prop) fun a => by positivity

theorem abs_dLk_le (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) : |dLk a ρ| ≤ 2 / ρ := by
  unfold dLk
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hρ]
  nlinarith [sq_nonneg a]

theorem abs_dθk_le (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) : |dθk a ρ| ≤ 2 / ρ := by
  unfold dθk
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 2 + ρ ^ 2), div_le_div_iff₀ (by positivity) hρ]
  nlinarith [sq_nonneg (|a| - ρ), sq_abs a, abs_nonneg a]

theorem hasFDerivAt_FLs {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (p : E × ℝ) (hp : 0 < p.2) : HasFDerivAt (FLs h) (DL h p) p := by
  have key := hasFDerivAt_op Lk dLk hp (fun ρ hρ => continuous_Lk_right hρ.ne') (fun ρ hρ => continuous_dLk_right hρ)
    (fun a ρ hρ => hasDerivAt_Lk_right (by positivity))
    (fun a => |Real.log (a ^ 2)| + Real.log (1 + a ^ 2) + Real.log (1 + (p.2 + p.2 / 2) ^ 2))
    (fun R => integrableOn_logBound R _)
    (by
      filter_upwards [ae_ne_zero] with a ha
      intro ρ h1 h2
      exact abs_Lk_le ha (by rw [abs_of_pos (by linarith)]; exact h2.le))
    (fun a ρ hρ => abs_dLk_le a hρ) hh hhc p.1
  refine key.congr_fderiv ?_
  rw [ibp_dLk hh hhc p.1 hp]
  rfl

theorem hasFDerivAt_FTs {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (p : E × ℝ) (hp : 0 < p.2) : HasFDerivAt (FTs h) (DT h p) p := by
  have key := hasFDerivAt_op θk dθk hp (fun ρ hρ => continuous_θk_right hρ) (fun ρ hρ => continuous_dθk_right hρ)
    (fun a ρ hρ => hasDerivAt_θk_right hρ a) (fun _ => π) (fun R => integrableOn_const (by simp))
    (Filter.Eventually.of_forall fun a ρ _ _ => abs_θk_le a ρ)
    (fun a ρ hρ => abs_dθk_le a hρ) hh hhc p.1
  refine key.congr_fderiv ?_
  rw [ibp_dθk hh hhc p.1 hp]
  rfl

theorem continuousWithinAt_DL {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (p₀ : E × ℝ) (hp₀ : 0 ≤ p₀.2) : ContinuousWithinAt (DL h) {p : E × ℝ | 0 ≤ p.2} p₀ := by
  have t1 : ContinuousAt (fun p : E × ℝ => ∫ a, (Lk a p.2) • Deh h (p.1, a)) p₀ :=
    continuousAt_FL (Deh h) (continuous_Deh hh) (hasCompactSupport_Deh hhc) p₀
  have t2 : ContinuousWithinAt (fun p : E × ℝ => ∫ a, (θk a p.2) • dsh h (p.1, a)) {p : E × ℝ | 0 ≤ p.2} p₀ :=
    continuousWithinAt_FT (dsh h) (contDiff_dsh hh).continuous (hasCompactSupport_dsh hhc) p₀ hp₀
  unfold DL
  exact (t1.continuousWithinAt.clm_comp continuousWithinAt_const).fun_add
    ((continuousWithinAt_const.fun_smul t2).fun_smul continuousWithinAt_const)

theorem continuousWithinAt_DT {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (p₀ : E × ℝ) (hp₀ : 0 ≤ p₀.2) : ContinuousWithinAt (DT h) {p : E × ℝ | 0 ≤ p.2} p₀ := by
  have t1 : ContinuousWithinAt (fun p : E × ℝ => ∫ a, (θk a p.2) • Deh h (p.1, a)) {p : E × ℝ | 0 ≤ p.2} p₀ :=
    continuousWithinAt_FT (Deh h) (continuous_Deh hh) (hasCompactSupport_Deh hhc) p₀ hp₀
  have t2 : ContinuousAt (fun p : E × ℝ => ∫ a, (Lk a p.2) • dsh h (p.1, a)) p₀ :=
    continuousAt_FL (dsh h) (contDiff_dsh hh).continuous (hasCompactSupport_dsh hhc) p₀
  unfold DT
  exact (t1.clm_comp continuousWithinAt_const).fun_add
    ((continuousWithinAt_const.fun_smul t2.continuousWithinAt).fun_smul continuousWithinAt_const)

theorem closure_openHalfSpace :
    closure ({p : E × ℝ | 0 < p.2} : Set (E × ℝ)) = {p : E × ℝ | 0 ≤ p.2} := by
  have h1 : ({p : E × ℝ | 0 < p.2} : Set (E × ℝ)) = Prod.snd ⁻¹' Set.Ioi 0 := rfl
  have h2 : ({p : E × ℝ | 0 ≤ p.2} : Set (E × ℝ)) = Prod.snd ⁻¹' Set.Ici 0 := rfl
  rw [h1, h2, ← isOpenMap_snd.preimage_closure_eq_closure_preimage continuous_snd, closure_Ioi]

theorem convex_openHalfSpace : Convex ℝ ({p : E × ℝ | 0 < p.2} : Set (E × ℝ)) := by
  intro a ha b hb s t hs ht hst
  show (0 : ℝ) < (s • a + t • b).2
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rcases hs.eq_or_lt with h0 | hspos
  · subst h0; rw [zero_add] at hst; subst hst; simpa using hb
  · exact add_pos_of_pos_of_nonneg (mul_pos hspos ha) (mul_nonneg ht hb.le)

theorem isOpen_openHalfSpace : IsOpen ({p : E × ℝ | 0 < p.2} : Set (E × ℝ)) :=
  isOpen_lt continuous_const continuous_snd

theorem hasFDerivWithinAt_halfSpace {f : E × ℝ → ℂ} {D : E × ℝ → (E × ℝ →L[ℝ] ℂ)}
    (hint : ∀ p : E × ℝ, 0 < p.2 → HasFDerivAt f (D p) p)
    (hcont : ∀ p : E × ℝ, 0 ≤ p.2 → ContinuousWithinAt f {p : E × ℝ | 0 ≤ p.2} p)
    (hD : ∀ p : E × ℝ, 0 ≤ p.2 → ContinuousWithinAt D {p : E × ℝ | 0 ≤ p.2} p)
    (p₀ : E × ℝ) (hp₀ : 0 ≤ p₀.2) :
    HasFDerivWithinAt f (D p₀) {p : E × ℝ | 0 ≤ p.2} p₀ := by
  have hsub : ({p : E × ℝ | 0 < p.2} : Set (E × ℝ)) ⊆ {p : E × ℝ | 0 ≤ p.2} := fun p hp =>
    show (0 : ℝ) ≤ p.2 from le_of_lt hp
  rw [← closure_openHalfSpace]
  refine hasFDerivWithinAt_closure_of_tendsto_fderiv (fun y hy => (hint y hy).differentiableAt.differentiableWithinAt)
    convex_openHalfSpace isOpen_openHalfSpace (fun y hy => ?_) ?_
  · rw [closure_openHalfSpace] at hy
    exact (hcont y hy).mono hsub
  · have hev : (fun y => fderiv ℝ f y) =ᶠ[𝓝[{p : E × ℝ | 0 < p.2}] p₀] D :=
      eventually_nhdsWithin_of_forall fun y hy => (hint y hy).fderiv
    exact (((hD p₀ hp₀).mono hsub).tendsto).congr' hev.symm

theorem hasFDerivWithinAt_FLs {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (p : E × ℝ) (hp : 0 ≤ p.2) : HasFDerivWithinAt (FLs h) (DL h p) {p : E × ℝ | 0 ≤ p.2} p :=
  hasFDerivWithinAt_halfSpace (hasFDerivAt_FLs hh hhc)
    (fun q _ => (continuousAt_FL h hh.continuous hhc q).continuousWithinAt)
    (continuousWithinAt_DL hh hhc) p hp

theorem hasFDerivWithinAt_FTs {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (p : E × ℝ) (hp : 0 ≤ p.2) : HasFDerivWithinAt (FTs h) (DT h p) {p : E × ℝ | 0 ≤ p.2} p :=
  hasFDerivWithinAt_halfSpace (hasFDerivAt_FTs hh hhc)
    (fun q hq => continuousWithinAt_FT h hh.continuous hhc q hq)
    (continuousWithinAt_DT hh hhc) p hp

theorem DL_apply {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (p : E × ℝ) (y : E × ℝ) :
    DL h p y = FLs (deh h y.1) p + ((2 : ℝ) • FTs (dsh h) p) * (y.2 : ℂ) := by
  unfold DL FLs FTs
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, sndC_apply,
    ContinuousLinearMap.integral_apply (integrable_Lk_smul (Deh h) (continuous_Deh hh) (hasCompactSupport_Deh hhc) p)]
  rfl

theorem DT_apply {h : E × ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (p : E × ℝ) (y : E × ℝ) :
    DT h p y = FTs (deh h y.1) p + ((-(1 / 2) : ℝ) • FLs (dsh h) p) * (y.2 : ℂ) := by
  unfold DT FLs FTs
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, sndC_apply,
    ContinuousLinearMap.integral_apply (integrable_θk_smul (Deh h) (continuous_Deh hh) (hasCompactSupport_Deh hhc) p)]
  rfl

theorem uniqueDiffOn_H : UniqueDiffOn ℝ ({p : E × ℝ | 0 ≤ p.2} : Set (E × ℝ)) := by
  refine uniqueDiffOn_convex ?_ ⟨((0 : E), (1 : ℝ)), ?_⟩
  · intro a ha b hb s t hs ht _
    show (0 : ℝ) ≤ (s • a + t • b).2
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs ha) (mul_nonneg ht hb)
  · rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (isOpen_openHalfSpace.mem_nhds (by show (0 : ℝ) < 1; norm_num))
      fun p hp => show (0 : ℝ) ≤ p.2 from le_of_lt hp

theorem main [FiniteDimensional ℝ E] (n : ℕ) : ∀ (h : E × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h →
    ContDiffOn ℝ n (FLs h) {p : E × ℝ | 0 ≤ p.2} ∧ ContDiffOn ℝ n (FTs h) {p : E × ℝ | 0 ≤ p.2} := by
  induction n with
  | zero =>
    intro h hh hhc
    simp only [CharP.cast_eq_zero, contDiffOn_zero]
    exact ⟨fun p _ => (continuousAt_FL h hh.continuous hhc p).continuousWithinAt,
      fun p hp => continuousWithinAt_FT h hh.continuous hhc p hp⟩
  | succ n ih =>
    intro h hh hhc
    have hU := (uniqueDiffOn_H (E := E))
    rw [Nat.cast_succ]
    constructor
    · refine (contDiffOn_succ_iff_fderiv_apply hU).2 ⟨fun p hp => (hasFDerivWithinAt_FLs hh hhc p hp).differentiableWithinAt,
        fun hn => absurd hn (by simp), fun y => ?_⟩
      have h1 := (ih (deh h y.1) (contDiff_deh hh y.1) (hasCompactSupport_deh hhc y.1)).1
      have h2 := (ih (dsh h) (contDiff_dsh hh) (hasCompactSupport_dsh hhc)).2
      have h3 : ContDiffOn ℝ n (fun x : E × ℝ => FLs (deh h y.1) x + ((2 : ℝ) • FTs (dsh h) x) * (y.2 : ℂ))
          {p : E × ℝ | 0 ≤ p.2} := h1.add ((h2.const_smul (2 : ℝ)).mul contDiffOn_const)
      refine h3.congr fun x hx => ?_
      rw [(hasFDerivWithinAt_FLs hh hhc x hx).fderivWithin (hU x hx), DL_apply hh hhc]
    · refine (contDiffOn_succ_iff_fderiv_apply hU).2 ⟨fun p hp => (hasFDerivWithinAt_FTs hh hhc p hp).differentiableWithinAt,
        fun hn => absurd hn (by simp), fun y => ?_⟩
      have h1 := (ih (deh h y.1) (contDiff_deh hh y.1) (hasCompactSupport_deh hhc y.1)).2
      have h2 := (ih (dsh h) (contDiff_dsh hh) (hasCompactSupport_dsh hhc)).1
      have h3 : ContDiffOn ℝ n (fun x : E × ℝ => FTs (deh h y.1) x + ((-(1 / 2) : ℝ) • FLs (dsh h) x) * (y.2 : ℂ))
          {p : E × ℝ | 0 ≤ p.2} := h1.add ((h2.const_smul (-(1 / 2) : ℝ)).mul contDiffOn_const)
      refine h3.congr fun x hx => ?_
      rw [(hasFDerivWithinAt_FTs hh hhc x hx).fderivWithin (hU x hx), DT_apply hh hhc]

end LogPot

end

open LogPot in
theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : E × ℝ => ∫ s : ℝ, g (p.1, s) * (Real.log (s ^ 2 + p.2 ^ 2) : ℂ))
      {p : E × ℝ | 0 ≤ p.2} := by
  have h := contDiffOn_infty.2 fun n => (LogPot.main n g hg hgc).1
  refine h.congr fun p _ => ?_
  show (∫ s : ℝ, g (p.1, s) * (Real.log (s ^ 2 + p.2 ^ 2) : ℂ)) = ∫ a, (LogPot.Lk a p.2) • g (p.1, a)
  congr 1
  funext s
  rw [Complex.real_smul, mul_comm]
  rfl

end S_MeasureTheory_contDiffOn_integral_mul_log_sq_add_sq_halfSpace
end P2MW
export P2MW.S_MeasureTheory_contDiffOn_integral_mul_log_sq_add_sq_halfSpace (solution)
