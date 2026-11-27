-- Prove2me | solution 1 for Kyprianou.Ch05.killedLaplaceExponentDivTendstoAtZero
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T06:30:15.235088+00:00
-- url     : https://prove2.me/submissions/b41b2b2e-f877-495a-89d1-fdf98f149cbf

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05 Set

/-- H3: Phi(theta)/theta -> atTop as theta -> 0+.
By monotone convergence, Phi(theta)/theta = d + (F theta).toReal where
F theta is the lintegral of (1 - e^{-theta x})/theta, and F theta_n increases
to J = ∫ x dPi along theta_n = 1/(n+1). If J = ⊤, a direct lower bound
(1 - e^{-u}) >= u/2 for u in [0,1] forces Phi(theta)/theta -> atTop.
If J < ⊤, then Phi(theta)/theta -> d + J.toReal =: C > 0, so
Phi(2 theta)/Phi(theta) -> 2, contradicting regular variation
(which gives 2^alpha < 2). -/
theorem solution
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1) (hAlpha1 : alpha < 1)
    (hRV : RegularlyVaryingAtZero Phi alpha) :
    Tendsto (fun theta : Real => Phi theta / theta)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) atTop := by
  obtain ⟨heta, hd, hPi0, hInt, hPhiEq⟩ := hTriplet
  obtain ⟨hRVpos, hRVlim⟩ := hRV
  set F : Real → ENNReal :=
    fun theta => ∫⁻ x in Set.Ioi 0, ENNReal.ofReal ((1 - Real.exp (-theta * x)) / theta) ∂Pi with hF
  set J : ENNReal := ∫⁻ x in Set.Ioi 0, ENNReal.ofReal x ∂Pi with hJ
  -- (0) min(1, x) is integrable (as in H-Phi)
  have hMinInt : Integrable (fun x : Real => min 1 x) (Pi.restrict (Set.Ioi (0 : Real))) := by
    refine ⟨?_, ?_⟩
    · exact ((continuous_const.min continuous_id : Continuous fun x : Real => min 1 x)).aestronglyMeasurable
    · show (∫⁻ a, ‖(min 1 a : Real)‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real)))) < ⊤
      have h1 : (∫⁻ a, ‖(min 1 a : Real)‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real))))
          = ∫⁻ a in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 a) ∂Pi := by
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
        rw [Real.enorm_eq_ofReal (le_min zero_le_one (le_of_lt ha))]
      rw [h1]
      exact hInt
  -- (1) the divided integrand is integrable for theta > 0
  have hDivInt : ∀ theta : Real, 0 < theta →
      Integrable (fun x : Real => (1 - Real.exp (-theta * x)) / theta)
        (Pi.restrict (Set.Ioi (0 : Real))) := by
    intro theta htheta
    have hmeas : AEStronglyMeasurable (fun x : Real => (1 - Real.exp (-theta * x)) / theta)
        (Pi.restrict (Set.Ioi (0 : Real))) :=
      (by fun_prop : Continuous fun x : Real => (1 - Real.exp (-theta * x)) / theta).aestronglyMeasurable
    refine ⟨hmeas, ?_⟩
    show HasFiniteIntegral (fun x : Real => (1 - Real.exp (-theta * x)) / theta)
      (Pi.restrict (Set.Ioi (0 : Real)))
    show (∫⁻ a, ‖(1 - Real.exp (-theta * a)) / theta‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real)))) < ⊤
    have hbound : (∫⁻ a, ‖(1 - Real.exp (-theta * a)) / theta‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real))))
        ≤ ∫⁻ a, ENNReal.ofReal (max 1 (1 / theta) * min 1 a) ∂(Pi.restrict (Set.Ioi (0 : Real))) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
      have hax : (0 : Real) ≤ a := ha.le
      have hnn : (0 : Real) ≤ (1 - Real.exp (-theta * a)) / theta := by
        apply div_nonneg _ htheta.le
        apply sub_nonneg.mpr
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta.le) hax
      rw [Real.enorm_eq_ofReal hnn]
      apply ENNReal.ofReal_le_ofReal
      have hle1 : (1 - Real.exp (-theta * a)) / theta ≤ min a (1 / theta) := by
        apply le_min
        · rw [div_le_iff₀ htheta]
          have h := Real.add_one_le_exp (-theta * a)
          linarith
        · exact (div_le_div_iff_of_pos_right htheta).mpr (sub_le_self 1 (Real.exp_pos _).le)
      have hle2 : min a (1 / theta) ≤ max 1 (1 / theta) * min 1 a := by
        rcases le_total a 1 with ha1 | ha1
        · calc min a (1 / theta) ≤ a := min_le_left _ _
            _ = 1 * a := (one_mul a).symm
            _ ≤ max 1 (1 / theta) * a :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hax
            _ = max 1 (1 / theta) * min 1 a := by rw [min_eq_right ha1]
        · calc min a (1 / theta) ≤ 1 / theta := min_le_right _ _
            _ ≤ max 1 (1 / theta) := le_max_right _ _
            _ = max 1 (1 / theta) * 1 := (mul_one _).symm
            _ = max 1 (1 / theta) * min 1 a := by rw [min_eq_left ha1]
      exact le_trans hle1 hle2
    have hfin : (∫⁻ a, ENNReal.ofReal (max 1 (1 / theta) * min 1 a)
        ∂(Pi.restrict (Set.Ioi (0 : Real)))) < ⊤ := by
      have hmeas2 : Measurable (fun a : Real => ENNReal.ofReal (min 1 a)) :=
        Measurable.ennreal_ofReal (continuous_const.min continuous_id).measurable
      have heq : (∫⁻ a, ENNReal.ofReal (max 1 (1 / theta) * min 1 a)
          ∂(Pi.restrict (Set.Ioi (0 : Real))))
          = ENNReal.ofReal (max 1 (1 / theta)) *
            ∫⁻ a, ENNReal.ofReal (min 1 a) ∂(Pi.restrict (Set.Ioi (0 : Real))) := by
        rw [← MeasureTheory.lintegral_const_mul _ hmeas2]
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
        rw [ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ max 1 (1 / theta))]
      rw [heq]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hInt
    exact lt_of_le_of_lt hbound hfin
  -- (2) bridge: Phi theta / theta = d + (F theta).toReal for theta > 0
  have hBridge : ∀ theta : Real, 0 < theta →
      Phi theta / theta = d + (F theta).toReal := by
    intro theta htheta
    have hθ0 : theta ≠ 0 := ne_of_gt htheta
    have hPhi : Phi theta = d * theta + ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi := by
      have h := hPhiEq theta htheta.le
      simpa using h
    have hnn : 0 ≤ᵐ[Pi.restrict (Set.Ioi (0 : Real))]
        fun x : Real => (1 - Real.exp (-theta * x)) / theta := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
      apply div_nonneg _ htheta.le
      apply sub_nonneg.mpr
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta.le) ha.le
    have hOfReal : ENNReal.ofReal
        (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) / theta ∂Pi)
        = F theta :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hDivInt theta htheta) hnn
    have hI : (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi) / theta
        = ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) / theta ∂Pi := by
      rw [MeasureTheory.integral_div]
    have hnonneg : (0 : Real) ≤ Phi theta / theta - d := by
      have hI0 : (0 : Real) ≤ ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi := by
        apply integral_nonneg_of_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
        apply sub_nonneg.mpr
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta.le) ha.le
      rw [hPhi]
      have hdiv : (d * theta + ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi) / theta
          = d + (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi) / theta := by
        field_simp
      rw [hdiv]
      linarith [div_nonneg hI0 htheta.le]
    have hEq : ENNReal.ofReal (Phi theta / theta - d) = F theta := by
      rw [hPhi]
      have hdiv : (d * theta + ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi) / theta - d
          = (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi) / theta := by
        field_simp
        ring
      rw [hdiv, hI]
      exact hOfReal
    have htoReal : (F theta).toReal = Phi theta / theta - d := by
      rw [← hEq]
      exact ENNReal.toReal_ofReal hnonneg
    linarith
  -- (3) the divided integrand is antitone in theta (pointwise, for x > 0)
  have hmono : ∀ {θ₁ θ₂ : Real}, 0 < θ₁ → θ₁ ≤ θ₂ → ∀ x : Real, 0 < x →
      (1 - Real.exp (-θ₂ * x)) / θ₂ ≤ (1 - Real.exp (-θ₁ * x)) / θ₁ := by
    intro θ₁ θ₂ hθ₁ hθ₁₂ x hx
    rcases eq_or_lt_of_le hθ₁₂ with h | h
    · rw [← h]
    · have ha : (0 : Real) < θ₁ * x := mul_pos hθ₁ hx
      have hb : (0 : Real) < θ₂ * x := mul_pos (lt_trans hθ₁ h) hx
      have hA : (θ₁ * x) * Real.exp (-(θ₁ * x)) ≤ 1 - Real.exp (-(θ₁ * x)) := by
        have hexp : (0 : Real) < Real.exp (θ₁ * x) := Real.exp_pos _
        have hadd := Real.add_one_le_exp (θ₁ * x)
        rw [Real.exp_neg]
        have h2 : (θ₁ * x) * (Real.exp (θ₁ * x))⁻¹ = (θ₁ * x) / Real.exp (θ₁ * x) := by
          rw [div_eq_mul_inv]
        have h3 : (1 : Real) - (Real.exp (θ₁ * x))⁻¹
            = (Real.exp (θ₁ * x) - 1) / Real.exp (θ₁ * x) := by
          field_simp
        rw [h2, h3, div_le_div_iff_of_pos_right hexp]
        linarith
      have hB : Real.exp (-(θ₁ * x)) - Real.exp (-(θ₂ * x))
          ≤ Real.exp (-(θ₁ * x)) * (θ₂ * x - θ₁ * x) := by
        have hba : (0 : Real) ≤ θ₂ * x - θ₁ * x := by
          have : θ₁ * x ≤ θ₂ * x := mul_le_mul_of_nonneg_right hθ₁₂ hx.le
          linarith
        have h1 : (1 : Real) - Real.exp (-(θ₂ * x - θ₁ * x)) ≤ θ₂ * x - θ₁ * x := by
          have hh := Real.add_one_le_exp (-(θ₂ * x - θ₁ * x))
          linarith
        have h2 : Real.exp (-(θ₂ * x))
            = Real.exp (-(θ₁ * x)) * Real.exp (-(θ₂ * x - θ₁ * x)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [h2]
        have h3 : Real.exp (-(θ₁ * x)) - Real.exp (-(θ₁ * x)) * Real.exp (-(θ₂ * x - θ₁ * x))
            = Real.exp (-(θ₁ * x)) * (1 - Real.exp (-(θ₂ * x - θ₁ * x))) := by ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      have hkey : (θ₁ * x) * (1 - Real.exp (-(θ₂ * x)))
          ≤ (θ₂ * x) * (1 - Real.exp (-(θ₁ * x))) := by
        have e1 : (θ₂ * x) * (1 - Real.exp (-(θ₁ * x))) - (θ₁ * x) * (1 - Real.exp (-(θ₂ * x)))
            = (θ₂ * x - θ₁ * x) * (1 - Real.exp (-(θ₁ * x)))
              - (θ₁ * x) * (Real.exp (-(θ₁ * x)) - Real.exp (-(θ₂ * x))) := by ring
        have e2 : (θ₂ * x - θ₁ * x) * ((θ₁ * x) * Real.exp (-(θ₁ * x)))
            ≤ (θ₂ * x - θ₁ * x) * (1 - Real.exp (-(θ₁ * x))) :=
          mul_le_mul_of_nonneg_left hA (by
            have : θ₁ * x ≤ θ₂ * x := mul_le_mul_of_nonneg_right hθ₁₂ hx.le
            linarith)
        have e3 : (θ₁ * x) * (Real.exp (-(θ₁ * x)) - Real.exp (-(θ₂ * x)))
            ≤ (θ₂ * x - θ₁ * x) * ((θ₁ * x) * Real.exp (-(θ₁ * x))) := by
          calc (θ₁ * x) * (Real.exp (-(θ₁ * x)) - Real.exp (-(θ₂ * x)))
              ≤ (θ₁ * x) * (Real.exp (-(θ₁ * x)) * (θ₂ * x - θ₁ * x)) :=
                mul_le_mul_of_nonneg_left hB ha.le
            _ = (θ₂ * x - θ₁ * x) * ((θ₁ * x) * Real.exp (-(θ₁ * x))) := by ring
        linarith
      have hkey' : (θ₁ * x) * (1 - Real.exp (-θ₂ * x))
          ≤ (θ₂ * x) * (1 - Real.exp (-θ₁ * x)) := by
        simpa only [neg_mul] using hkey
      have e1 : ((θ₁ * x) * (1 - Real.exp (-θ₂ * x))) / x
          = (1 - Real.exp (-θ₂ * x)) * θ₁ := by
        rw [show (θ₁ * x) * (1 - Real.exp (-θ₂ * x))
            = ((1 - Real.exp (-θ₂ * x)) * θ₁) * x by ring,
          mul_div_cancel_right₀ _ (ne_of_gt hx)]
      have e2 : ((θ₂ * x) * (1 - Real.exp (-θ₁ * x))) / x
          = (1 - Real.exp (-θ₁ * x)) * θ₂ := by
        rw [show (θ₂ * x) * (1 - Real.exp (-θ₁ * x))
            = ((1 - Real.exp (-θ₁ * x)) * θ₂) * x by ring,
          mul_div_cancel_right₀ _ (ne_of_gt hx)]
      have hkey2 : (1 - Real.exp (-θ₂ * x)) * θ₁ ≤ (1 - Real.exp (-θ₁ * x)) * θ₂ := by
        have h' : ((θ₁ * x) * (1 - Real.exp (-θ₂ * x))) / x
            ≤ ((θ₂ * x) * (1 - Real.exp (-θ₁ * x))) / x :=
          (div_le_div_iff_of_pos_right hx).mpr hkey'
        rwa [e1, e2] at h'
      rw [div_le_div_iff₀ (lt_trans hθ₁ h) hθ₁]
      exact hkey2
  -- (4) the divided integrand tends to x as theta -> 0+
  have hlim : ∀ x : Real, 0 < x →
      Tendsto (fun theta : Real => (1 - Real.exp (-theta * x)) / theta)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds x) := by
    intro x hx
    have hslope : Tendsto (fun v : Real => (Real.exp v - 1) / v)
        (nhdsWithin (0 : Real) {0}ᶜ) (nhds 1) := by
      have h := (Real.hasDerivAt_exp (0 : Real)).tendsto_slope
      have heq : slope Real.exp (0 : Real) = fun v : Real => (Real.exp v - 1) / v := by
        funext v
        simp [slope, Real.exp_zero]
        rw [div_eq_mul_inv, mul_comm]
      rw [heq] at h
      simpa only [Real.exp_zero] using h
    have hnegmap : Tendsto (fun u : Real => -u) (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhdsWithin (0 : Real) {0}ᶜ) := by
      have h1 : Tendsto (fun u : Real => -u) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) := by
        simpa using (continuous_neg.tendsto (0 : Real)).mono_left nhdsWithin_le_nhds
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun u : Real => -u) h1
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact neg_ne_zero.mpr (ne_of_gt hu)
    have h1 : Tendsto (fun u : Real => (1 - Real.exp (-u)) / u)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) := by
      have h2 := hslope.comp hnegmap
      apply h2.congr'
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu0 : u ≠ 0 := ne_of_gt hu
      field_simp
      simp only [Function.comp_def]
      rw [div_mul_eq_mul_div₀, div_neg, mul_div_cancel_right₀ _ hu0, neg_sub]
    have hmap : Tendsto (fun theta : Real => theta * x)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhdsWithin (0 : Real) (Set.Ioi 0)) := by
      have h1 : Tendsto (fun theta : Real => theta * x)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) := by
        have h : Tendsto (fun theta : Real => theta * x) (nhds (0 : Real)) (nhds (0 * x)) :=
          (continuous_id.mul continuous_const).tendsto (0 : Real)
        simpa using h.mono_left nhdsWithin_le_nhds
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1
      filter_upwards [self_mem_nhdsWithin] with theta htheta
      exact mul_pos htheta hx
    have h2 := h1.comp hmap
    have h3 := h2.const_mul x
    rw [mul_one] at h3
    apply h3.congr'
    filter_upwards [self_mem_nhdsWithin] with theta htheta
    have hθ0 : theta ≠ 0 := ne_of_gt htheta
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp
    simp only [Function.comp_def]
    rw [mul_comm x ((1 - Real.exp (-(x * theta))) / (x * theta)), mul_assoc,
      div_mul_cancel₀ _ (mul_ne_zero hx0 hθ0)]
  -- (5) MCT along any positive antitone sequence tending to 0
  have hMCT : ∀ θ : ℕ → Real, (∀ n, 0 < θ n) → Antitone θ →
      Tendsto θ atTop (nhds 0) →
      Tendsto (fun n => F (θ n)) atTop (nhds J) := by
    intro θ hθpos hθanti hθlim
    have hmeas : ∀ n, Measurable (fun x : Real =>
        ENNReal.ofReal ((1 - Real.exp (-θ n * x)) / θ n)) := by
      intro n
      exact Measurable.ennreal_ofReal
        ((by fun_prop : Continuous fun x : Real => (1 - Real.exp (-θ n * x)) / θ n).measurable)
    have hmonoENN : Monotone (fun n x => ENNReal.ofReal ((1 - Real.exp (-θ n * x)) / θ n)) := by
      intro m n hmn x
      by_cases hx : (0 : Real) < x
      · apply ENNReal.ofReal_le_ofReal
        exact hmono (hθpos n) (hθanti hmn) x hx
      · have h1 : (1 - Real.exp (-θ m * x)) / θ m ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg _ (hθpos m).le
          have hle : (1 : Real) ≤ Real.exp (-θ m * x) := by
            have h := Real.add_one_le_exp (-θ m * x)
            have h2 : (0 : Real) ≤ -(θ m * x) := by
              have h3 : θ m * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hθpos m).le (le_of_not_gt hx)
              linarith
            linarith
          linarith
        have h2 : (1 - Real.exp (-θ n * x)) / θ n ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg _ (hθpos n).le
          have hle : (1 : Real) ≤ Real.exp (-θ n * x) := by
            have h := Real.add_one_le_exp (-θ n * x)
            have h2 : (0 : Real) ≤ -(θ n * x) := by
              have h3 : θ n * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hθpos n).le (le_of_not_gt hx)
              linarith
            linarith
          linarith
        show ENNReal.ofReal ((1 - Real.exp (-θ m * x)) / θ m)
            ≤ ENNReal.ofReal ((1 - Real.exp (-θ n * x)) / θ n)
        rw [ENNReal.ofReal_of_nonpos h1, ENNReal.ofReal_of_nonpos h2]
    have hsup : ∀ x : Real, (⨆ n, ENNReal.ofReal ((1 - Real.exp (-θ n * x)) / θ n))
        = ENNReal.ofReal x := by
      intro x
      by_cases hx : (0 : Real) < x
      · have hlimx : Tendsto (fun n => (1 - Real.exp (-θ n * x)) / θ n) atTop (nhds x) := by
          have hθ : Tendsto θ atTop (nhdsWithin (0 : Real) (Set.Ioi 0)) :=
            tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within θ hθlim
              (eventually_atTop.mpr ⟨0, fun n _ => hθpos n⟩)
          exact (hlim x hx).comp hθ
        have hT1 : Tendsto (fun n => ENNReal.ofReal ((1 - Real.exp (-θ n * x)) / θ n))
            atTop (nhds (⨆ n, ENNReal.ofReal ((1 - Real.exp (-θ n * x)) / θ n))) :=
          tendsto_atTop_ciSup (fun m n hmn => hmonoENN hmn x) ⟨⊤, fun _ _ => le_top⟩
        have hT2 : Tendsto (fun n => ENNReal.ofReal ((1 - Real.exp (-θ n * x)) / θ n))
            atTop (nhds (ENNReal.ofReal x)) :=
          (ENNReal.continuous_ofReal.tendsto x).comp hlimx
        exact tendsto_nhds_unique hT1 hT2
      · have hzero : ∀ n, ENNReal.ofReal ((1 - Real.exp (-θ n * x)) / θ n) = 0 := by
          intro n
          apply ENNReal.ofReal_of_nonpos
          apply div_nonpos_of_nonpos_of_nonneg _ (hθpos n).le
          have hle : (1 : Real) ≤ Real.exp (-θ n * x) := by
            have h := Real.add_one_le_exp (-θ n * x)
            have h2 : (0 : Real) ≤ -(θ n * x) := by
              have h3 : θ n * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hθpos n).le (le_of_not_gt hx)
              linarith
            linarith
          linarith
        simp only [hzero, iSup_const, ENNReal.ofReal_of_nonpos (le_of_not_gt hx)]
    have hEq : (∫⁻ x in Set.Ioi 0, (⨆ n, ENNReal.ofReal ((1 - Real.exp (-θ n * x)) / θ n)) ∂Pi)
        = ⨆ n, F (θ n) :=
      MeasureTheory.lintegral_iSup hmeas hmonoENN
    simp only [hsup] at hEq
    have hEqJ : J = ⨆ n, F (θ n) := hEq
    have hmonoF : Monotone (fun n => F (θ n)) := by
      intro m n hmn
      apply MeasureTheory.lintegral_mono
      intro x
      exact hmonoENN hmn x
    have hT := tendsto_atTop_ciSup hmonoF ⟨⊤, fun _ _ => le_top⟩
    rwa [← hEqJ] at hT
  -- (6) lower bound: (1 - e^{-u}) >= u/2 for u in [0,1]
  have hlb : ∀ θ x : Real, 0 < θ → 0 < x → θ * x ≤ 1 →
      x / 2 ≤ (1 - Real.exp (-θ * x)) / θ := by
    intro θ x hθ hx hθx
    rw [le_div_iff₀ hθ]
    have hu : (0 : Real) ≤ θ * x := mul_nonneg hθ.le hx.le
    have h1 : Real.exp (-(θ * x)) ≤ 1 - (θ * x) / 2 := by
      have ha : Real.exp (-(θ * x)) ≤ 1 / (1 + θ * x) := by
        rw [Real.exp_neg, one_div,
          inv_le_inv₀ (Real.exp_pos _) (by linarith : (0 : Real) < 1 + θ * x)]
        have h := Real.add_one_le_exp (θ * x)
        linarith
      have hb : (1 : Real) / (1 + θ * x) ≤ 1 - (θ * x) / 2 := by
        rw [div_le_iff₀ (by linarith : (0 : Real) < 1 + θ * x)]
        nlinarith [mul_nonneg hu (by linarith : (0 : Real) ≤ 1 - θ * x)]
      exact le_trans ha hb
    have heq : x / 2 * θ = (θ * x) / 2 := by ring
    rw [heq, neg_mul]
    linarith
  -- (6') lower bound: (1 - e^{-theta x})/theta >= min x (1/theta) / 2
  have hlb2 : ∀ θ x : Real, 0 < θ → 0 < x →
      min x (1 / θ) / 2 ≤ (1 - Real.exp (-θ * x)) / θ := by
    intro θ x hθ hx
    by_cases h : θ * x ≤ 1
    · have hxle : x ≤ 1 / θ := by
        rw [le_div_iff₀ hθ]
        linarith [mul_comm θ x]
      rw [min_eq_left hxle]
      exact hlb θ x hθ hx h
    · push_neg at h
      have hxge : 1 / θ ≤ x := by
        rw [div_le_iff₀ hθ]
        linarith [mul_comm θ x]
      rw [min_eq_right hxge, le_div_iff₀ hθ]
      have hhalf : (1 / θ) / 2 * θ = 1 / 2 := by
        rw [div_mul_eq_mul_div₀, one_div_mul_cancel (ne_of_gt hθ)]
      rw [hhalf]
      have h1 : Real.exp (-(θ * x)) ≤ 1 / 2 := by
        have h2 : Real.exp (-(θ * x)) ≤ Real.exp (-1) := by
          apply Real.exp_le_exp.mpr
          linarith
        have h3 : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg, one_div,
            inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : Real) < 2)]
          have hadd := Real.add_one_le_exp (1 : Real)
          linarith
        exact le_trans h2 h3
      rw [neg_mul]
      linarith
  -- sequences c/(n+1) and their MCT limits
  have hθ1lim : Tendsto (fun n : ℕ => (1 : Real) / (n + 1 : ℝ)) atTop (nhds 0) := by
    have h : Tendsto ((fun n : ℕ => (1 : Real) / (n : ℝ)) ∘ fun a : ℕ => a + 1)
        atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, one_div, Nat.cast_add, Nat.cast_one] using h
  have hSeq : ∀ c : Real, 0 < c →
      Tendsto (fun n : ℕ => F (c / (n + 1 : ℝ))) atTop (nhds J) := by
    intro c hc
    apply hMCT
    · intro n
      exact div_pos hc (by positivity)
    · intro m n hmn
      show c / ((n : ℝ) + 1) ≤ c / ((m : ℝ) + 1)
      have h1 : (1 : Real) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hmn 1)
      have h2 : c / ((n : ℝ) + 1) = c * (1 / ((n : ℝ) + 1)) := by
        rw [div_eq_mul_inv, one_div]
      have h3 : c / ((m : ℝ) + 1) = c * (1 / ((m : ℝ) + 1)) := by
        rw [div_eq_mul_inv, one_div]
      rw [h2, h3]
      exact mul_le_mul_of_nonneg_left h1 hc.le
    · have h2 := hθ1lim.const_mul c
      rw [mul_zero] at h2
      simpa only [div_eq_mul_inv, one_div, one_mul] using h2
  by_cases hJtop : J = ⊤
  · -- Case J = ⊤: the min-truncation forces Phi theta / theta -> atTop
    have hMinMCT : Tendsto (fun n : ℕ => ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (n : Real)) ∂Pi)
        atTop (nhds ⊤) := by
      have hmeas : ∀ n : ℕ, Measurable (fun x : Real => ENNReal.ofReal (min x (n : Real))) := by
        intro n
        exact Measurable.ennreal_ofReal (measurable_id.min measurable_const)
      have hmonoM : Monotone (fun n : ℕ => fun x : Real => ENNReal.ofReal (min x (n : Real))) := by
        intro m n hmn x
        apply ENNReal.ofReal_le_ofReal
        exact min_le_min le_rfl (by exact_mod_cast hmn)
      have hsupM : ∀ x : Real, (⨆ n : ℕ, ENNReal.ofReal (min x (n : Real))) = ENNReal.ofReal x := by
        intro x
        by_cases hx : (0 : Real) ≤ x
        · have hT1 : Tendsto (fun n : ℕ => ENNReal.ofReal (min x (n : Real)))
            atTop (nhds (⨆ n : ℕ, ENNReal.ofReal (min x (n : Real)))) :=
            tendsto_atTop_ciSup (fun m n hmn => hmonoM hmn x) ⟨⊤, fun _ _ => le_top⟩
          have hT2 : Tendsto (fun n : ℕ => ENNReal.ofReal (min x (n : Real)))
              atTop (nhds (ENNReal.ofReal x)) := by
            have hlimx : Tendsto (fun n : ℕ => min x (n : Real)) atTop (nhds x) := by
              apply tendsto_const_nhds.congr'
              filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
              exact (min_eq_left (le_trans (Nat.le_ceil x) (by exact_mod_cast hn))).symm
            exact (ENNReal.continuous_ofReal.tendsto x).comp hlimx
          exact tendsto_nhds_unique hT1 hT2
        · have hzero : ∀ n : ℕ, ENNReal.ofReal (min x (n : Real)) = 0 := by
            intro n
            apply ENNReal.ofReal_of_nonpos
            exact min_le_of_left_le (le_of_not_ge hx)
          simp [hzero, ENNReal.ofReal_of_nonpos (le_of_not_ge hx)]
      have hEq : (∫⁻ x in Set.Ioi 0, (⨆ n : ℕ, ENNReal.ofReal (min x (n : Real))) ∂Pi)
          = ⨆ n : ℕ, ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (n : Real)) ∂Pi :=
        MeasureTheory.lintegral_iSup hmeas hmonoM
      simp only [hsupM] at hEq
      have hT : Tendsto (fun n : ℕ => ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (n : Real)) ∂Pi)
          atTop (nhds (⨆ n : ℕ, ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (n : Real)) ∂Pi)) :=
        tendsto_atTop_ciSup (fun m n hmn => by
          apply MeasureTheory.lintegral_mono
          intro x
          exact hmonoM hmn x) ⟨⊤, fun _ _ => le_top⟩
      rw [← hEq] at hT
      have hT' : Tendsto (fun n : ℕ => ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (n : Real)) ∂Pi)
          atTop (nhds J) := hT
      rwa [hJtop] at hT'
    rw [tendsto_atTop]
    intro M
    by_cases hMd : M ≤ d
    · filter_upwards [self_mem_nhdsWithin] with theta htheta
      rw [hBridge theta htheta]
      have hnn : (0 : Real) ≤ (F theta).toReal := ENNReal.toReal_nonneg
      linarith
    · push_neg at hMd
      obtain ⟨n, hn⟩ := ((tendsto_order.1 hMinMCT).1
        (ENNReal.ofReal (2 * (M - d))) ENNReal.ofReal_lt_top).exists
      have hn : ENNReal.ofReal (2 * (M - d))
          ≤ ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (n : Real)) ∂Pi := hn.le
      have hn1 : 1 ≤ n := by
        by_contra hcon
        push_neg at hcon
        interval_cases n
        · simp at hn
          linarith
      have hev : ∀ᶠ theta in nhdsWithin (0 : Real) (Set.Ioi 0), theta ≤ 1 / (n : ℝ) := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [eventually_lt_nhds (show (0 : Real) < 1 / (n : ℝ) by positivity)]
          with theta htheta _
        exact le_of_lt htheta
      filter_upwards [hev, self_mem_nhdsWithin] with theta hle htheta
      have hθpos : (0 : Real) < theta := htheta
      have hθle : theta ≤ 1 / (n : ℝ) := hle
      have hθn : (n : Real) ≤ 1 / theta := by
        rw [le_div_iff₀ hθpos]
        have hle : (n : Real) * theta ≤ (n : Real) * (1 / (n : Real)) :=
          mul_le_mul_of_nonneg_left hθle (by positivity)
        rw [mul_one_div_cancel (by exact_mod_cast (by omega : n ≠ 0))] at hle
        linarith
      have hFbound : ENNReal.ofReal (2 * (M - d)) ≤ 2 * F theta := by
        have h1 : (∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (1 / theta)) ∂Pi) ≤ 2 * F theta := by
          have hstep : (∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (1 / theta)) ∂Pi)
              ≤ ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (2 * ((1 - Real.exp (-theta * x)) / theta)) ∂Pi := by
            apply MeasureTheory.lintegral_mono
            intro x
            by_cases hx : (0 : Real) < x
            · exact ENNReal.ofReal_le_ofReal (by linarith [hlb2 theta x hθpos hx])
            · have hle : min x (1 / theta) ≤ 0 := min_le_of_left_le (le_of_not_gt hx)
              show ENNReal.ofReal (min x (1 / theta))
                  ≤ ENNReal.ofReal (2 * ((1 - Real.exp (-theta * x)) / theta))
              rw [ENNReal.ofReal_of_nonpos hle]
              exact bot_le
          have hstep2 : (∫⁻ x in Set.Ioi 0, ENNReal.ofReal (2 * ((1 - Real.exp (-theta * x)) / theta)) ∂Pi)
              = 2 * F theta := by
            rw [← MeasureTheory.lintegral_const_mul _ (by
              exact Measurable.ennreal_ofReal
                ((by fun_prop : Continuous fun x : Real => (1 - Real.exp (-theta * x)) / theta).measurable))]
            apply MeasureTheory.lintegral_congr_ae
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
            rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
            simp
          exact le_trans hstep (le_of_eq hstep2)
        have h2 : (∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (n : Real)) ∂Pi)
            ≤ ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (min x (1 / theta)) ∂Pi := by
          apply MeasureTheory.lintegral_mono
          intro x
          apply ENNReal.ofReal_le_ofReal
          exact min_le_min le_rfl hθn
        exact le_trans hn (le_trans h2 h1)
      have hFfin : F theta ≠ ⊤ := by
        have hcongr : (∫⁻ x in Set.Ioi 0, ENNReal.ofReal ((1 - Real.exp (-theta * x)) / theta) ∂Pi)
            = ∫⁻ a, ‖(1 - Real.exp (-theta * a)) / theta‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real))) := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
          rw [Real.enorm_eq_ofReal (by
            apply div_nonneg _ hθpos.le
            apply sub_nonneg.mpr
            rw [Real.exp_le_one_iff]
            exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθpos.le) ha.le)]
        have hfin : (∫⁻ a, ‖(1 - Real.exp (-theta * a)) / theta‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real)))) ≠ ⊤ :=
          (hDivInt theta hθpos).2.ne
        rw [← hcongr] at hfin
        exact hfin
      have htoReal : (F theta).toReal ≥ M - d := by
        have h2 : (2 : ENNReal) * ENNReal.ofReal (M - d) ≤ 2 * F theta := by
          have hof : ENNReal.ofReal (2 * (M - d)) = 2 * ENNReal.ofReal (M - d) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
            simp
          rwa [hof] at hFbound
        have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hFfin) h2
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by linarith : (0 : Real) ≤ M - d)] at h3
        have h4 : (2 : ENNReal).toReal = 2 := by simp
        rw [h4] at h3
        linarith
      rw [hBridge theta hθpos]
      linarith
  · -- Case J < ⊤: sequential ratio contradiction
    have hJlt : J < ⊤ := lt_top_iff_ne_top.mpr hJtop
    set C : Real := d + J.toReal with hC
    have hlimC : ∀ c : Real, 0 < c →
        Tendsto (fun n : ℕ => Phi (c / (n + 1 : ℝ)) / (c / (n + 1 : ℝ))) atTop (nhds C) := by
      intro c hc
      have hF := hSeq c hc
      have htoReal := (ENNReal.tendsto_toReal hJtop).comp hF
      have hsum : Tendsto (fun n : ℕ => d + (F (c / (n + 1 : ℝ))).toReal) atTop (nhds (d + J.toReal)) :=
        tendsto_const_nhds.add htoReal
      apply hsum.congr'
      filter_upwards with n
      exact (hBridge (c / (n + 1 : ℝ)) (div_pos hc (by positivity))).symm
    have hCpos : 0 < C := by
      have hPhi1 : Phi 1 = d * 1 + ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-1 * x)) ∂Pi := by
        have h := hPhiEq 1 zero_le_one
        simpa using h
      have h1Int : Integrable (fun x : Real => 1 - Real.exp (-1 * x))
          (Pi.restrict (Set.Ioi (0 : Real))) := by
        simpa only [div_one] using hDivInt 1 one_pos
      have hxInt : Integrable (fun x : Real => x) (Pi.restrict (Set.Ioi (0 : Real))) := by
        refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
        show HasFiniteIntegral (fun x : Real => x) (Pi.restrict (Set.Ioi (0 : Real)))
        show (∫⁻ a, ‖(a : Real)‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real)))) < ⊤
        have h1 : (∫⁻ a, ‖(a : Real)‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real))))
            = ∫⁻ a in Set.Ioi (0 : Real), ENNReal.ofReal a ∂Pi := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
          rw [Real.enorm_eq_ofReal ha.le]
        rw [h1]
        exact hJlt
      have hle : (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-1 * x)) ∂Pi)
          ≤ ∫ x in Set.Ioi (0 : Real), x ∂Pi := by
        apply MeasureTheory.integral_mono_ae h1Int hxInt
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
        have h := Real.add_one_le_exp (-1 * a)
        linarith
      have hxEq : (∫ x in Set.Ioi (0 : Real), x ∂Pi) = J.toReal := by
        have hnn : (0 : Real) ≤ ∫ x in Set.Ioi (0 : Real), x ∂Pi := by
          apply integral_nonneg_of_ae
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
          exact ha.le
        have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hxInt
          (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha; exact ha.le)
        have hJeq : (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal x ∂Pi) = J := rfl
        rw [hJeq] at h
        rw [← h]
        exact (ENNReal.toReal_ofReal hnn).symm
      have hPhi1le : Phi 1 ≤ C := by
        rw [hPhi1, hC]
        have hmul : d * 1 = d := mul_one d
        rw [hmul]
        linarith
      exact lt_of_lt_of_le (hRVpos 1 one_pos) hPhi1le
    have hratio : Tendsto (fun n : ℕ => Phi (2 / (n + 1 : ℝ)) / Phi (1 / (n + 1 : ℝ)))
        atTop (nhds 2) := by
      have hCne : C ≠ 0 := ne_of_gt hCpos
      have h1 := hlimC 2 (by norm_num)
      have h2 := hlimC 1 one_pos
      have h3 : Tendsto (fun n : ℕ =>
          (Phi (2 / (n + 1 : ℝ)) / (2 / (n + 1 : ℝ))) /
          (Phi (1 / (n + 1 : ℝ)) / (1 / (n + 1 : ℝ)))) atTop (nhds (C / C)) :=
        h1.div h2 hCne
      rw [div_self hCne] at h3
      have heq : (fun n : ℕ => Phi (2 / (n + 1 : ℝ)) / Phi (1 / (n + 1 : ℝ)))
          = fun n : ℕ => ((Phi (2 / (n + 1 : ℝ)) / (2 / (n + 1 : ℝ))) /
            (Phi (1 / (n + 1 : ℝ)) / (1 / (n + 1 : ℝ)))) * 2 := by
        funext n
        have hθ1 : (0 : Real) < 1 / (n + 1 : ℝ) := by positivity
        have hθ2 : (0 : Real) < 2 / (n + 1 : ℝ) := by positivity
        have hP1 : Phi (1 / (n + 1 : ℝ)) ≠ 0 := ne_of_gt (hRVpos _ hθ1)
        have hP2 : Phi (2 / (n + 1 : ℝ)) ≠ 0 := ne_of_gt (hRVpos _ hθ2)
        field_simp
      rw [heq]
      simpa using h3.mul_const 2
    have hRVseq : Tendsto (fun n : ℕ => Phi (2 / (n + 1 : ℝ)) / Phi (1 / (n + 1 : ℝ)))
        atTop (nhds ((2 : Real) ^ alpha)) := by
      have h := hRVlim 2 (by norm_num)
      have hθ : Tendsto (fun n : ℕ => (1 : Real) / (n + 1 : ℝ)) atTop
          (nhdsWithin (0 : Real) (Set.Ioi 0)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hθ1lim
          (eventually_atTop.mpr ⟨0, fun n _ => Set.mem_Ioi.mpr (by positivity)⟩)
      have hcomp := h.comp hθ
      apply hcomp.congr'
      filter_upwards with n
      simp only [Function.comp_def]
      rw [show (2 : Real) * (1 / (n + 1 : ℝ)) = 2 / (n + 1 : ℝ) by ring]
    have hEq2 : (2 : Real) = (2 : Real) ^ alpha := tendsto_nhds_unique hratio hRVseq
    have hlt : (2 : Real) ^ alpha < 2 := by
      have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : Real) < 2) hAlpha1
      rwa [Real.rpow_one] at h
    linarith
