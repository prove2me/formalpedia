-- Prove2me | solution 1 for LookbackMOT.HL.eq_3_23
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:22:30.790085+00:00
-- url     : https://prove2.me/submissions/bd020a2c-5862-46b9-a06e-fa3f3dd9c6c7

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL Filter Topology Asymptotics
open scoped NNReal ENNReal

/-- product of a function vanishing at `x` with derivative `f'` and a function continuous at `x` -/
lemma LB_hasDerivWithinAt_mul_of_zero {F G : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}
    (hF : HasDerivWithinAt F f' s x) (hF0 : F x = 0) (hG : ContinuousWithinAt G s x) :
    HasDerivWithinAt (fun y => F y * G y) (f' * G x) s x := by
  rw [hasDerivWithinAt_iff_isLittleO] at hF ⊢
  simp only [hF0, sub_zero, zero_mul, smul_eq_mul] at hF ⊢
  have h1 : (fun y => (F y - (y - x) * f') * G y) =o[𝓝[s] x] fun y => (y - x) * 1 :=
    hF.mul_isBigO (hG.tendsto.isBigO_one ℝ)
  have h2 : (fun y => (y - x) * (f' * (G y - G x))) =o[𝓝[s] x] fun y => (y - x) * 1 := by
    apply (isBigO_refl (fun y => y - x) _).mul_isLittleO
    have : Tendsto (fun y => f' * (G y - G x)) (𝓝[s] x) (𝓝 0) := by
      have := (hG.tendsto.sub_const (G x)).const_mul f'
      simpa using this
    exact (isLittleO_one_iff ℝ).mpr this
  have := h1.add h2
  simp only [mul_one] at this
  refine this.congr_left (fun y => ?_)
  ring

theorem solution (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (lam : ℝ → ℝ) (hlam : ConvexOn ℝ Set.univ lam)
    (ν₂ : Measure ℝ) (hν₂ : IsSecondDerivMeasure lam ν₂) (ψ : ℝ → ℝ) (hψ : InPsi g lam ν₂ ψ) :
    ∀ m : ℝ, HasDerivWithinAt (fun m' => vpsi g lam ψ m m') 0 (Set.Ici m) m := by
  obtain ⟨hlt, hrc, -, hode⟩ := hψ
  intro m
  set R := rDeriv lam with hRdef
  set h : ℝ → ℝ := fun s => deriv g s / (s - ψ s) with hhdef
  have hint : interior (Set.univ : Set ℝ) = Set.univ := interior_univ
  -- convexity sandwich
  have hsand : ∀ a b : ℝ, 0 ≤ lam b - lam a - R a * (b - a) ∧
      lam b - lam a - R a * (b - a) ≤ (R b - R a) * (b - a) := by
    have key : ∀ a b : ℝ, a < b → R a ≤ slope lam a b ∧ slope lam a b ≤ R b := by
      intro a b hab
      refine ⟨hlam.rightDeriv_le_slope_of_mem_interior (by simp) (Set.mem_univ _) hab, ?_⟩
      exact (hlam.slope_le_leftDeriv_of_mem_interior (Set.mem_univ _) (by simp) hab).trans
        (hlam.leftDeriv_le_rightDeriv_of_mem_interior (by simp))
    intro a b
    rcases lt_trichotomy a b with hab | rfl | hab
    · obtain ⟨k1, k2⟩ := key a b hab
      rw [slope_def_field] at k1 k2
      have hd : 0 < b - a := by linarith
      rw [le_div_iff₀ hd] at k1
      rw [div_le_iff₀ hd] at k2
      constructor <;> nlinarith
    · simp
    · obtain ⟨k1, k2⟩ := key b a hab
      rw [slope_def_field] at k1 k2
      have hd : 0 < a - b := by linarith
      rw [le_div_iff₀ hd] at k1
      rw [div_le_iff₀ hd] at k2
      constructor <;> nlinarith
  -- derivative facts on g
  have hdiff : Differentiable ℝ g := hgC1.differentiable (by norm_num)
  have hDcont : Continuous (deriv g) := hgC1.continuous_deriv (by norm_num)
  have hDnn : ∀ x, 0 ≤ deriv g x := fun x => hgmono.deriv_nonneg
  have hhnn : ∀ s, 0 ≤ h s := fun s => div_nonneg (hDnn s) (by linarith [hlt s])
  have hhcont : ContinuousWithinAt h (Set.Ici m) m := by
    apply ContinuousWithinAt.div hDcont.continuousWithinAt
    · exact continuousWithinAt_id.sub (hrc m)
    · linarith [hlt m]
  -- F(m') = R(ψ m') - R(ψ m)
  set F : ℝ → ℝ := fun y => R (ψ y) - R (ψ m) with hFdef
  have hF0 : F m = 0 := by simp [F]
  have hFbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝[Set.Ici m] m,
      |F y - (y - m) * h m| ≤ ε * |y - m| := by
    intro ε hε
    have hev : ∀ᶠ s in 𝓝[Set.Ici m] m, h s ∈ Set.Icc (h m - ε) (h m + ε) := by
      apply hhcont
      exact Icc_mem_nhds (by linarith) (by linarith)
    rcases (Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)) with ⟨δ, hδ, hball⟩
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, fun y hy hym => ?_⟩
    have hym' : m ≤ y := hym
    obtain ⟨hmono, heq⟩ := hode m y hym'
    have hFnn : 0 ≤ F y := by simp only [F]; linarith
    have hsub : ∀ s ∈ Set.Ioc m y, h s ∈ Set.Icc (h m - ε) (h m + ε) := by
      intro s hs
      apply hball
      · rw [Real.dist_eq, abs_lt]
        rw [Real.dist_eq, abs_lt] at hy
        constructor <;> linarith [hs.1, hs.2]
      · exact le_of_lt hs.1
    have hvol : volume (Set.Ioc m y) = ENNReal.ofReal (y - m) := Real.volume_Ioc
    have hup : ENNReal.ofReal (F y) ≤ ENNReal.ofReal ((h m + ε) * (y - m)) := by
      rw [show ENNReal.ofReal (F y) = ENNReal.ofReal (R (ψ y) - R (ψ m)) from rfl, heq]
      calc (∫⁻ s in Set.Ioc m y, ENNReal.ofReal (deriv g s / (s - ψ s)))
          ≤ ∫⁻ s in Set.Ioc m y, ENNReal.ofReal (h m + ε) := by
            apply setLIntegral_mono measurable_const
            intro s hs
            exact ENNReal.ofReal_le_ofReal (hsub s hs).2
        _ = ENNReal.ofReal ((h m + ε) * (y - m)) := by
            rw [setLIntegral_const, hvol, ← ENNReal.ofReal_mul (by linarith [hhnn m])]
    have hlow : ENNReal.ofReal ((h m - ε) * (y - m)) ≤ ENNReal.ofReal (F y) := by
      rcases le_or_gt (h m - ε) 0 with hneg | hpos
      · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hneg (by linarith))]
        exact bot_le
      rw [show ENNReal.ofReal (F y) = ENNReal.ofReal (R (ψ y) - R (ψ m)) from rfl, heq]
      calc ENNReal.ofReal ((h m - ε) * (y - m))
          = ∫⁻ s in Set.Ioc m y, ENNReal.ofReal (h m - ε) := by
            rw [setLIntegral_const, hvol, ← ENNReal.ofReal_mul hpos.le]
        _ ≤ ∫⁻ s in Set.Ioc m y, ENNReal.ofReal (deriv g s / (s - ψ s)) := by
            apply lintegral_mono_ae
            rw [ae_restrict_iff' measurableSet_Ioc]
            exact Eventually.of_forall (fun s hs => ENNReal.ofReal_le_ofReal (hsub s hs).1)
    have hup' : F y ≤ (h m + ε) * (y - m) :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith [hhnn m]) (by linarith))).mp hup
    have hlow' : (h m - ε) * (y - m) ≤ F y := by
      rcases le_or_gt (h m - ε) 0 with hneg | hpos
      · nlinarith
      · exact (ENNReal.ofReal_le_ofReal_iff hFnn).mp hlow
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y - m), abs_le]
    constructor <;> nlinarith
  have hFderiv : HasDerivWithinAt F (h m) (Set.Ici m) m := by
    rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
    intro c hc
    filter_upwards [hFbound c hc] with y hy
    simp only [hF0, sub_zero, smul_eq_mul, Real.norm_eq_abs]
    exact hy
  -- eventually ψ y ≤ m
  have hψev : ∀ᶠ y in 𝓝[Set.Ici m] m, ψ y < m :=
    (hrc m).eventually (gt_mem_nhds (hlt m))
  -- decomposition of v
  have hK : ContinuousWithinAt (fun y => ψ y - ψ m) (Set.Ici m) m :=
    (hrc m).sub continuousWithinAt_const
  have hG : ContinuousWithinAt (fun y => m - ψ y) (Set.Ici m) m :=
    continuousWithinAt_const.sub (hrc m)
  have hP1 := LB_hasDerivWithinAt_mul_of_zero hFderiv hF0 hK
  have hP2 := LB_hasDerivWithinAt_mul_of_zero hFderiv hF0 hG
  simp only [sub_self, mul_zero] at hP1
  -- E1(y) = lam (ψ y) - lam (ψ m) - R (ψ m) * (ψ y - ψ m), squeezed by F * K
  set E1 : ℝ → ℝ := fun y => lam (ψ y) - lam (ψ m) - R (ψ m) * (ψ y - ψ m)
  have hE1 : HasDerivWithinAt E1 0 (Set.Ici m) m := by
    rw [hasDerivWithinAt_iff_isLittleO] at hP1 ⊢
    simp only [hF0, zero_mul, sub_zero, smul_zero] at hP1 ⊢
    have hE10 : E1 m = 0 := by simp [E1]
    simp only [hE10, sub_zero]
    refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun y => ?_)) hP1
    obtain ⟨a1, a2⟩ := hsand (ψ m) (ψ y)
    simp only [Real.norm_eq_abs, one_mul, E1]
    rw [abs_of_nonneg a1]
    exact a2.trans (le_abs_self _)
  have hg' : HasDerivWithinAt g (deriv g m) (Set.Ici m) m := (hdiff m).hasDerivAt.hasDerivWithinAt
  have htot := (hg'.sub hE1).sub hP2
  have hsum : deriv g m - 0 - h m * (m - ψ m) = 0 := by
    simp only [h]
    field_simp [show m - ψ m ≠ 0 by linarith [hlt m]]
    ring
  rw [hsum] at htot
  have htot' := htot.add_const (-(lam (ψ m) + R (ψ m) * (m - ψ m)))
  apply htot'.congr_of_eventuallyEq_of_mem _ Set.self_mem_Ici
  filter_upwards [hψev, self_mem_nhdsWithin] with y hy _
  simp only [vpsi, E1, F, min_eq_right hy.le, Pi.sub_apply]
  ring
