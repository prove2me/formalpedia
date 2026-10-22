-- Prove2me | solution 1 for LariviereIGFR.Moments.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T17:29:47.597506+00:00
-- url     : https://prove2.me/submissions/4f740791-bd9b-4325-b023-c267a44c9da2

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LvIGFRMom

/-- The cdf of an atomless probability measure is continuous. -/
theorem cdf_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : ∀ x, μ {x} = 0) :
    Continuous (fun x => cdf μ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hm := (cdf μ).mono
  have hsing : (cdf μ).measure {x} = ENNReal.ofReal (cdf μ x - Function.leftLim (cdf μ) x) :=
    StieltjesFunction.measure_singleton _ x
  rw [measure_cdf, h0 x] at hsing
  have h1 : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 := ENNReal.ofReal_eq_zero.1 hsing.symm
  have h2 : Function.leftLim (cdf μ) x ≤ cdf μ x := Monotone.leftLim_le hm le_rfl
  have hl : Function.leftLim (cdf μ) x = cdf μ x := le_antisymm h2 (by linarith)
  have hL : ContinuousWithinAt (cdf μ) (Iio x) x :=
    (Monotone.continuousWithinAt_Iio_iff_leftLim_eq hm).2 hl
  rw [continuousAt_iff_continuous_left_right]
  exact ⟨continuousWithinAt_Iio_iff_Iic.1 hL, (cdf μ).right_continuous x⟩

/-- Right derivative of `S(x) x^c`. -/
theorem hasDeriv_F (μ : Measure ℝ) (φ : ℝ → ℝ) (c x : ℝ) (hx : 0 < x)
    (hd : HasDerivWithinAt (fun y => cdf μ y) (φ x) (Ici x) x) :
    HasDerivWithinAt (fun y => (1 - cdf μ y) * y ^ c)
      ((0 - φ x) * x ^ c + (1 - cdf μ x) * (c * x ^ (c - 1))) (Ici x) x := by
  have h1 : HasDerivWithinAt (fun y => 1 - cdf μ y) (0 - φ x) (Ici x) x :=
    (hasDerivWithinAt_const x (Ici x) (1 : ℝ)).sub hd
  have h2 : HasDerivWithinAt (fun y : ℝ => y ^ c) (c * x ^ (c - 1)) (Ici x) x :=
    (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).hasDerivWithinAt
  exact h1.mul h2

/-- Sign of the derivative in terms of `g`. -/
theorem deriv_eq (s φx gx c x : ℝ) (hx : 0 < x) (hs : 0 < s) (hg : gx = x * (φx / s)) :
    (0 - φx) * x ^ c + s * (c * x ^ (c - 1)) = x ^ c * s * (c - gx) / x := by
  rw [Real.rpow_sub_one hx.ne', hg]
  field_simp
  ring

end LvIGFRMom

open MeasureTheory ProbabilityTheory Filter Topology Set LariviereIGFR.Moments in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : LariviereIGFR.Char.IsRegDensity μ φ)
    (α : ℝ) (hsupp : HasSupportIoi μ α) (higfr : LariviereIGFR.Char.IsIGFR μ φ) (κ : ENNReal)
    (hκ : Tendsto (fun ξ => ENNReal.ofReal (LariviereIGFR.Char.genFailureRate μ φ ξ)) atTop (𝓝 κ))
    (n : ℝ) (hn : 0 < n) :
    nthMoment μ n < ⊤ ↔ ENNReal.ofReal n < κ := by
  classical
  -- basic facts
  set g := LariviereIGFR.Char.genFailureRate μ φ with hgdef
  have hgx : ∀ x, g x = x * (φ x / (1 - cdf μ x)) := fun x => rfl
  have hS0 : ∀ x, 0 < 1 - cdf μ x := fun x => by have := hsupp.2.2 x; linarith
  have hS1 : ∀ x, 1 - cdf μ x ≤ 1 := fun x => by have := cdf_nonneg μ x; linarith
  have hderiv : ∀ x, α < x → HasDerivWithinAt (fun y => cdf μ y) (φ x) (Ici x) x := by
    intro x hx
    refine hφ.2.2.1 x ?_ (hsupp.2.2 x)
    rcases (cdf_nonneg μ x).lt_or_eq with h | h
    · exact h
    · exact absurd ((hsupp.2.1 x).1 h.symm) (not_le.2 hx)
  have hatom : ∀ x, μ {x} = 0 := by
    intro x
    have hac : μ ≪ volume := by
      rw [hφ.2.1]; exact withDensity_absolutelyContinuous _ _
    exact hac (Real.volume_singleton)
  have hcont : Continuous (fun x => cdf μ x) := LvIGFRMom.cdf_continuous μ hatom
  -- generic monotonicity of F = S x^c
  have hFmono : ∀ c a : ℝ, 0 < a → α < a → ∀ b : ℝ, a ≤ b →
      ((∀ x, a ≤ x → c ≤ g x) → (1 - cdf μ b) * b ^ c ≤ (1 - cdf μ a) * a ^ c) ∧
      ((∀ x, a ≤ x → g x ≤ c) → (1 - cdf μ a) * a ^ c ≤ (1 - cdf μ b) * b ^ c) := by
    intro c a ha hα b hb
    have hcont' : ContinuousOn (fun y => (1 - cdf μ y) * y ^ c) (Icc a b) :=
      ContinuousOn.mul ((continuous_const.sub hcont).continuousOn)
        (fun y hy => (Real.continuousAt_rpow_const y c (Or.inl (by
          have := hy.1; linarith))).continuousWithinAt)
    have hd' : ∀ x ∈ Ico a b, HasDerivWithinAt (fun y => (1 - cdf μ y) * y ^ c)
        ((0 - φ x) * x ^ c + (1 - cdf μ x) * (c * x ^ (c - 1))) (Ici x) x :=
      fun x hx => LvIGFRMom.hasDeriv_F μ φ c x (by linarith [hx.1]) (hderiv x (by linarith [hx.1]))
    have hval : ∀ x ∈ Ico a b, (0 - φ x) * x ^ c + (1 - cdf μ x) * (c * x ^ (c - 1))
        = x ^ c * (1 - cdf μ x) * (c - g x) / x :=
      fun x hx => LvIGFRMom.deriv_eq _ _ _ c x (by linarith [hx.1]) (hS0 x) (hgx x)
    have hconstc : ContinuousOn (fun _ : ℝ => (1 - cdf μ a) * a ^ c) (Icc a b) :=
      continuousOn_const
    have hconstd : ∀ x ∈ Ico a b, HasDerivWithinAt (fun _ : ℝ => (1 - cdf μ a) * a ^ c) 0
        (Ici x) x := fun x _ => hasDerivWithinAt_const _ _ _
    constructor
    · intro hlow
      refine image_le_of_deriv_right_le_deriv_boundary hcont' hd' le_rfl hconstc hconstd
        ?_ ⟨hb, le_rfl⟩
      intro x hx
      rw [hval x hx]
      have hxp : 0 < x := by linarith [hx.1]
      apply div_nonpos_of_nonpos_of_nonneg _ hxp.le
      apply mul_nonpos_of_nonneg_of_nonpos
      · exact mul_nonneg (Real.rpow_nonneg hxp.le _) (hS0 x).le
      · linarith [hlow x hx.1]
    · intro hup
      refine image_le_of_deriv_right_le_deriv_boundary hconstc hconstd le_rfl hcont' hd'
        ?_ ⟨hb, le_rfl⟩
      intro x hx
      rw [hval x hx]
      have hxp : 0 < x := by linarith [hx.1]
      apply div_nonneg _ hxp.le
      apply mul_nonneg
      · exact mul_nonneg (Real.rpow_nonneg hxp.le _) (hS0 x).le
      · linarith [hup x hx.1]
  -- layer cake
  have hae : 0 ≤ᵐ[μ] (fun x : ℝ => x) := by
    rw [Filter.EventuallyLE, ae_iff]
    have : {a : ℝ | ¬ (0 : ℝ → ℝ) a ≤ a} = Iio 0 := by
      ext a; simp
    rw [this]; exact hnn
  have hlc : LariviereIGFR.Moments.nthMoment μ n = ENNReal.ofReal n *
      ∫⁻ t in Ioi 0, μ {a : ℝ | t < a} * ENNReal.ofReal (t ^ (n - 1)) := by
    unfold LariviereIGFR.Moments.nthMoment
    exact lintegral_rpow_eq_lintegral_meas_lt_mul μ hae measurable_id.aemeasurable hn
  have hmeasS : ∀ t, μ {a : ℝ | t < a} = ENNReal.ofReal (1 - cdf μ t) := by
    intro t
    have hset : {a : ℝ | t < a} = (Iic t)ᶜ := by ext a; simp
    rw [hset, prob_compl_eq_one_sub measurableSet_Iic, ENNReal.ofReal_sub _ (cdf_nonneg μ t),
      ENNReal.ofReal_one, cdf_eq_real, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  constructor
  · intro hfin
    by_contra hcon
    rw [not_lt] at hcon
    have hmonoG : Monotone (fun ξ => ENNReal.ofReal (g ξ)) := by
      intro x y hxy
      exact ENNReal.ofReal_le_ofReal (higfr (hsupp.2.2 x) (hsupp.2.2 y) hxy)
    have hgle : ∀ x, g x ≤ n := by
      intro x
      have h1 := hmonoG.ge_of_tendsto hκ x
      exact (ENNReal.ofReal_le_ofReal_iff hn.le).1 (h1.trans hcon)
    set a : ℝ := max α 0 + 1 with ha_def
    have ha : 0 < a := by have := le_max_right α 0; linarith
    have hαa : α < a := by have := le_max_left α 0; linarith
    set K : ℝ := (1 - cdf μ a) * a ^ n with hK_def
    have hK : 0 < K := mul_pos (hS0 a) (Real.rpow_pos_of_pos ha n)
    have hlow : ∀ t, a ≤ t → K ≤ (1 - cdf μ t) * t ^ n :=
      fun t ht => (hFmono n a ha hαa t ht).2 (fun x _ => hgle x)
    have hint : ∫⁻ t in Ioi a, ENNReal.ofReal (K * t ^ (-1:ℝ)) = ⊤ := by
      by_contra hne
      have hfi : HasFiniteIntegral (fun t : ℝ => K * t ^ (-1:ℝ)) (volume.restrict (Ioi a)) := by
        rw [hasFiniteIntegral_iff_ofReal]
        · exact lt_top_iff_ne_top.2 hne
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg hK.le (Real.rpow_nonneg (by linarith [Set.mem_Ioi.1 ht]) _)
      have hI : IntegrableOn (fun t : ℝ => K * t ^ (-1:ℝ)) (Ioi a) :=
        ⟨(measurable_const.mul (measurable_id.pow_const _)).aestronglyMeasurable, hfi⟩
      have hI2 : IntegrableOn (fun t : ℝ => t ^ (-1:ℝ)) (Ioi a) := by
        refine IntegrableOn.congr_fun (hI.const_mul K⁻¹) (fun t _ => ?_) measurableSet_Ioi
        field_simp
      have := (integrableOn_Ioi_rpow_iff ha).1 hI2
      linarith
    have hge : ⊤ ≤ LariviereIGFR.Moments.nthMoment μ n := by
      calc (⊤ : ENNReal) = ENNReal.ofReal n * ⊤ :=
            (ENNReal.mul_top (by simpa using hn)).symm
        _ = ENNReal.ofReal n * ∫⁻ t in Ioi a, ENNReal.ofReal (K * t ^ (-1:ℝ)) := by rw [hint]
        _ ≤ ENNReal.ofReal n * ∫⁻ t in Ioi a, μ {x : ℝ | t < x} * ENNReal.ofReal (t ^ (n - 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            apply setLIntegral_mono' measurableSet_Ioi
            intro t ht
            have hat : a < t := Set.mem_Ioi.1 ht
            have htp : 0 < t := lt_trans ha hat
            rw [hmeasS t, ← ENNReal.ofReal_mul (hS0 t).le]
            apply ENNReal.ofReal_le_ofReal
            rw [Real.rpow_neg_one, Real.rpow_sub_one htp.ne', mul_div_assoc', ← div_eq_mul_inv]
            exact div_le_div_of_nonneg_right (hlow t hat.le) htp.le
        _ ≤ ENNReal.ofReal n * ∫⁻ t in Ioi 0, μ {x : ℝ | t < x} * ENNReal.ofReal (t ^ (n - 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            exact lintegral_mono_set (Ioi_subset_Ioi ha.le)
        _ = LariviereIGFR.Moments.nthMoment μ n := hlc.symm
    exact (not_le.2 hfin) hge
  · intro hlt
    obtain ⟨c, _hc0, hnc, hcκ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlt
    have hnc' : n < c := ((ENNReal.ofReal_lt_ofReal_iff').1 hnc).1
    have hev : ∀ᶠ ξ in atTop, ENNReal.ofReal c < ENNReal.ofReal (g ξ) :=
      hκ.eventually (lt_mem_nhds hcκ)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    set a : ℝ := max N (max α 0 + 1) with ha_def
    have ha : 0 < a := by
      have := le_max_right α 0; have := le_max_right N (max α 0 + 1); linarith
    have hαa : α < a := by
      have := le_max_left α 0; have := le_max_right N (max α 0 + 1); linarith
    have hgc : ∀ x, a ≤ x → c ≤ g x := fun x hx => by
      have := hN x (le_trans (le_max_left _ _) hx)
      exact ((ENNReal.ofReal_lt_ofReal_iff').1 this).1.le
    set K : ℝ := (1 - cdf μ a) * a ^ c with hK_def
    have hup : ∀ t, a ≤ t → (1 - cdf μ t) * t ^ c ≤ K :=
      fun t ht => (hFmono c a ha hαa t ht).1 hgc
    rw [hlc]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    refine lt_of_le_of_lt (lintegral_union_le _ _ _) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · have hI : IntegrableOn (fun t : ℝ => t ^ (n - 1)) (Ioc 0 a) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1
          (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc (fun t _ => ?_)) hI.lintegral_lt_top
      calc μ {x : ℝ | t < x} * ENNReal.ofReal (t ^ (n - 1))
          ≤ 1 * ENNReal.ofReal (t ^ (n - 1)) := mul_le_mul_of_nonneg_right prob_le_one zero_le
        _ = ENNReal.ofReal (t ^ (n - 1)) := one_mul _
    · have hI : IntegrableOn (fun t : ℝ => K * t ^ (n - 1 - c)) (Ioi a) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul K
      refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)) hI.lintegral_lt_top
      have hat : a < t := Set.mem_Ioi.1 ht
      have htp : 0 < t := lt_trans ha hat
      rw [hmeasS t, ← ENNReal.ofReal_mul (hS0 t).le]
      apply ENNReal.ofReal_le_ofReal
      have h1 := hup t hat.le
      have hp : 0 < t ^ c := Real.rpow_pos_of_pos htp c
      have hq : 0 < t ^ (n - 1) := Real.rpow_pos_of_pos htp _
      rw [Real.rpow_sub htp (n - 1) c, ← mul_div_assoc, le_div_iff₀ hp]
      calc (1 - cdf μ t) * t ^ (n - 1) * t ^ c = ((1 - cdf μ t) * t ^ c) * t ^ (n - 1) := by ring
        _ ≤ K * t ^ (n - 1) := mul_le_mul_of_nonneg_right h1 hq.le

