-- Prove2me | solution 1 for Kyprianou.Ch05.killedTailLaplaceTransform
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T06:49:08.958782+00:00
-- url     : https://prove2.me/submissions/054998ca-9d9c-4c95-a55c-97c28aec1304

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05 Set

/-- H2: the Laplace transform of the tail density is (Phi theta - d*theta)/theta.
By Tonelli, ∫₀^∞ e^{-θx} Π̄(x) dx = ∫_{y>0} ∫₀^y e^{-θx} dx Π(dy)
= ∫_{y>0} (1-e^{-θy})/θ Π(dy) = (Φ(θ) - dθ)/θ via the triplet equation. -/
theorem solution
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (theta : Real) (htheta : 0 < theta) :
    positiveLaplace
      (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
        (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta
      = ENNReal.ofReal ((Phi theta - d * theta) / theta) := by
  obtain ⟨heta, hd, hPi0, hInt, hPhiEq⟩ := hTriplet
  have hθne : theta ≠ 0 := htheta.ne'
  -- (0) tail finiteness for x > 0 (as in the C2 wrapper)
  have hPiFin : ∀ x : Real, 0 < x → Pi (Set.Ioi x) ≠ ⊤ := by
    intro x hx
    have hle : (∫⁻ y in Set.Ioi x, ENNReal.ofReal (min 1 x) ∂Pi) ≤
        ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi := by
      calc (∫⁻ y in Set.Ioi x, ENNReal.ofReal (min 1 x) ∂Pi)
          ≤ ∫⁻ y in Set.Ioi x, ENNReal.ofReal (min 1 y) ∂Pi := by
            apply MeasureTheory.lintegral_mono_ae
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
            exact ENNReal.ofReal_le_ofReal (min_le_min_left _ hy.le)
        _ ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi :=
            MeasureTheory.lintegral_mono_set (Set.Ioi_subset_Ioi hx.le)
    have hval : (∫⁻ y in Set.Ioi x, ENNReal.ofReal (min 1 x) ∂Pi)
        = ENNReal.ofReal (min 1 x) * Pi (Set.Ioi x) := by
      simp [MeasureTheory.lintegral_const]
    rw [hval] at hle
    have hlt : ENNReal.ofReal (min 1 x) * Pi (Set.Ioi x) < ⊤ := lt_of_le_of_lt hle hInt
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (min 1 x) :=
      ENNReal.ofReal_pos.mpr (lt_min one_pos hx)
    by_contra hb
    rw [hb, ENNReal.mul_top hpos.ne'] at hlt
    exact lt_irrefl ⊤ hlt
  -- (0') tail measurability (as in the C2 wrapper)
  have hTailAnti : Antitone (fun x : Real => Pi (Set.Ioi x)) := by
    intro a b hab
    exact measure_mono (Set.Ioi_subset_Ioi hab)
  have hTailMeas : Measurable (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal)) :=
    Measurable.ennreal_ofReal (Measurable.ennreal_toReal hTailAnti.measurable)
  have hExpMeas : Measurable (fun x : Real => ENNReal.ofReal (Real.exp (-theta * x))) :=
    Measurable.ennreal_ofReal ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable)
  -- (0'') min(1, x) is integrable (as in H3)
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
  -- (0''') the divided integrand is integrable for theta > 0 (as in H3)
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
  -- (0'''') Pi is sigma-finite (needed for Tonelli): exhaust by Iic 0 ∪ Ioo (1/(n+1)) (n+1)
  have hPiSigma : SigmaFinite Pi := by
    refine ⟨⟨⟨fun n : ℕ => Set.Iic (0 : Real) ∪ Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1), ?_, ?_, ?_⟩⟩⟩
    · intro n
      trivial
    · intro n
      have h1 : Pi (Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) < ⊤ := by
        have hbound : (∫⁻ y in Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1), ENNReal.ofReal (min 1 y) ∂Pi)
            ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi :=
          MeasureTheory.lintegral_mono_set
            (Set.Ioo_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (by positivity)))
        have hlow : ∀ y ∈ Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1),
            ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ ENNReal.ofReal (min 1 y) := by
          intro y hy
          apply ENNReal.ofReal_le_ofReal
          apply le_min
          · rw [div_le_one (by positivity : (0 : Real) < (n : ℝ) + 1)]
            have hn0 : (0 : Real) ≤ (n : ℝ) := Nat.cast_nonneg n
            linarith
          · exact hy.1.le
        have h2 : ENNReal.ofReal (1 / ((n : ℝ) + 1))
            * Pi (Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) < ⊤ := by
          have hval : (∫⁻ y in Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1),
                ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∂Pi)
              = ENNReal.ofReal (1 / ((n : ℝ) + 1))
                * Pi (Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
            simp [MeasureTheory.lintegral_const]
          have hmono : (∫⁻ y in Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1),
                ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∂Pi)
              ≤ ∫⁻ y in Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1),
                ENNReal.ofReal (min 1 y) ∂Pi := by
            apply MeasureTheory.lintegral_mono_ae
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with y hy
            exact hlow y hy
          rw [hval] at hmono
          exact lt_of_le_of_lt (le_trans hmono hbound) hInt
        have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
          ENNReal.ofReal_pos.mpr (by positivity)
        by_contra hb
        have htop : Pi (Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) = ⊤ :=
          le_antisymm le_top (le_of_not_gt hb)
        rw [htop, ENNReal.mul_top hpos.ne'] at h2
        exact lt_irrefl ⊤ h2
      calc Pi (Set.Iic (0 : Real) ∪ Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1))
          ≤ Pi (Set.Iic (0 : Real)) + Pi (Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
            measure_union_le _ _
        _ = Pi (Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by rw [hPi0, zero_add]
        _ < ⊤ := h1
    · ext x
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_Iic, Set.mem_Ioo, Set.mem_univ, iff_true]
      by_cases hx : x ≤ 0
      · exact ⟨0, Or.inl hx⟩
      · push_neg at hx
        obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / x) x)
        have hNpos : (0 : Real) < (N : ℝ) :=
          lt_trans (lt_of_lt_of_le hx (le_max_right _ _)) hN
        refine ⟨N, Or.inr ⟨?_, ?_⟩⟩
        · have h1 : (1 : Real) / ((N : ℝ) + 1) < 1 / (N : ℝ) :=
            one_div_lt_one_div_of_lt hNpos (by linarith)
          have h2 : (1 : Real) / (N : ℝ) < x := by
            rw [div_lt_iff₀ hNpos]
            have hmax : (1 : Real) / x < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
            rw [div_lt_iff₀ hx] at hmax
            rw [mul_comm] at hmax
            exact hmax
          exact lt_trans h1 h2
        · have hle : x ≤ max (1 / x) x := le_max_right _ _
          linarith
  haveI := hPiSigma
  -- (0''''') Ici 0 and Ioi 0 agree a.e. for volume, so the restricts agree
  have hAe : Set.Ici (0 : Real) =ᵐ[volume] Set.Ioi (0 : Real) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have hsymm : Set.Ici (0 : Real) \ Set.Ioi (0 : Real) = {0} := by
        ext x
        simp only [Set.mem_diff, Set.mem_Ici, Set.mem_Ioi, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact le_antisymm (le_of_not_gt h2) h1
        · intro h
          subst h
          exact ⟨le_refl 0, lt_irrefl 0⟩
      rw [hsymm]
      simp
    · have hempty : Set.Ioi (0 : Real) \ Set.Ici (0 : Real) = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro x hx
        exact hx.2 (Set.mem_Ici.mpr (Set.mem_Ioi.mp hx.1).le)
      rw [hempty]
      simp
  have hIciIoi : (volume : Measure Real).restrict (Set.Ici (0 : Real))
      = (volume : Measure Real).restrict (Set.Ioi (0 : Real)) :=
    MeasureTheory.Measure.restrict_congr_set hAe
  -- (1) the joint Tonelli integrand: e^{-θx} on {x < y}, else 0
  set G : ℝ × ℝ → ℝ≥0∞ := Set.indicator {p : ℝ × ℝ | p.1 < p.2}
    (fun p => ENNReal.ofReal (Real.exp (-theta * p.1))) with hG
  have hGmeas : Measurable G := by
    rw [hG]
    exact Measurable.indicator
      (Measurable.ennreal_ofReal ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable))
      measurableSet_lt'
  -- (2) x-side: ∫⁻ y, G (x, y) ∂Pi = ofReal (Π̄ x) * ofReal (e^{-θx}) for x > 0
  have hXSide : ∀ x : Real, 0 < x →
      (∫⁻ y, G (x, y) ∂Pi)
        = ENNReal.ofReal ((Pi (Set.Ioi x)).toReal) * ENNReal.ofReal (Real.exp (-theta * x)) := by
    intro x hx
    have hpt : ∀ y : Real, G (x, y)
        = Set.indicator (Set.Ioi x)
            (fun _ : Real => ENNReal.ofReal (Real.exp (-theta * x))) y := by
      intro y
      rw [hG]
      by_cases hy : y ∈ Set.Ioi x
      · rw [Set.indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | p.1 < p.2} from hy),
            Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | p.1 < p.2} from hy),
            Set.indicator_of_notMem hy]
    calc (∫⁻ y, G (x, y) ∂Pi)
        = ∫⁻ y, Set.indicator (Set.Ioi x)
            (fun _ : Real => ENNReal.ofReal (Real.exp (-theta * x))) y ∂Pi := by
          apply MeasureTheory.lintegral_congr_ae
          exact ae_of_all _ (fun y => hpt y)
      _ = ∫⁻ y in Set.Ioi x, ENNReal.ofReal (Real.exp (-theta * x)) ∂Pi :=
          MeasureTheory.lintegral_indicator measurableSet_Ioi _
      _ = ENNReal.ofReal (Real.exp (-theta * x)) * Pi (Set.Ioi x) := by
          simp [MeasureTheory.lintegral_const]
      _ = ENNReal.ofReal ((Pi (Set.Ioi x)).toReal) * ENNReal.ofReal (Real.exp (-theta * x)) := by
          rw [ENNReal.ofReal_toReal (hPiFin x hx)]
          exact mul_comm _ _
  -- (3) inner integral over (0, y) of e^{-θx} dx = (1 - e^{-θy})/θ for y > 0
  have hInnerInt : ∀ y : Real, 0 < y →
      (∫⁻ x in Set.Ioo (0 : Real) y, ENNReal.ofReal (Real.exp (-theta * x)) ∂volume)
        = ENNReal.ofReal ((1 - Real.exp (-theta * y)) / theta) := by
    intro y hy
    have hderiv : ∀ t : Real, HasDerivAt (fun s => -Real.exp (-theta * s) / theta)
        (Real.exp (-theta * t)) t := by
      intro t
      have h1 : HasDerivAt (fun s : Real => Real.exp (-theta * s))
          (Real.exp (-theta * t) * (-theta)) t := by
        have hc : HasDerivAt (fun s : Real => -theta * s) (-theta) t := by
          simpa using (hasDerivAt_id t).const_mul (-theta)
        exact (Real.hasDerivAt_exp (-theta * t)).comp t hc
      have h2 := h1.neg.div_const theta
      have heq : Real.exp (-theta * t) = -(Real.exp (-theta * t) * (-theta)) / theta := by
        field_simp
      rw [heq]
      exact h2
    have hIntble : IntegrableOn (fun x : Real => Real.exp (-theta * x))
        (Set.Ioo (0 : Real) y) volume := by
      apply IntegrableOn.mono_set _ Set.Ioo_subset_Icc_self
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hIntble
      (ae_of_all _ (fun x => (Real.exp_pos _).le))]
    congr 1
    have h1 : (∫ x in Set.Ioo (0 : Real) y, Real.exp (-theta * x) ∂volume)
        = ∫ x in (0 : Real)..y, Real.exp (-theta * x) := by
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le hy.le]
    rw [h1]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 y)]
    show -Real.exp (-theta * y) / theta - (-Real.exp (-theta * 0) / theta)
        = (1 - Real.exp (-theta * y)) / theta
    rw [mul_zero, Real.exp_zero]
    field_simp
    ring
  -- (4) y-side: the inner x-integral is over Ioo 0 y, hence the inner integral
  have hInner : ∀ y : Real, (∫⁻ x in Set.Ioi (0 : Real), G (x, y) ∂volume)
      = ∫⁻ x in Set.Ioo (0 : Real) y, ENNReal.ofReal (Real.exp (-theta * x)) ∂volume := by
    intro y
    have hpt : ∀ x : Real, G (x, y)
        = Set.indicator (Set.Iio y)
            (fun x : Real => ENNReal.ofReal (Real.exp (-theta * x))) x := by
      intro x
      rw [hG]
      by_cases hy : x < y
      · rw [Set.indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | p.1 < p.2} from hy),
            Set.indicator_of_mem (show x ∈ Set.Iio y from hy)]
      · rw [Set.indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | p.1 < p.2} from hy),
            Set.indicator_of_notMem (show x ∉ Set.Iio y from hy)]
    calc (∫⁻ x in Set.Ioi (0 : Real), G (x, y) ∂volume)
        = ∫⁻ x in Set.Ioi (0 : Real), Set.indicator (Set.Iio y)
            (fun x : Real => ENNReal.ofReal (Real.exp (-theta * x))) x ∂volume := by
          apply MeasureTheory.lintegral_congr_ae
          exact ae_of_all _ (fun x => hpt x)
      _ = ∫⁻ x in Set.Iio y, ENNReal.ofReal (Real.exp (-theta * x))
            ∂(volume.restrict (Set.Ioi (0 : Real))) := by
          rw [MeasureTheory.lintegral_indicator measurableSet_Iio]
      _ = ∫⁻ x in Set.Ioo (0 : Real) y, ENNReal.ofReal (Real.exp (-theta * x)) ∂volume := by
          have hrr : ((volume : Measure Real).restrict (Set.Ioi (0 : Real))).restrict (Set.Iio y)
              = (volume : Measure Real).restrict (Set.Ioo (0 : Real) y) := by
            rw [MeasureTheory.Measure.restrict_restrict measurableSet_Iio]
            congr 1
            ext x
            simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]
            exact and_comm
          rw [← hrr]
  have hYSide : ∀ y : Real, (∫⁻ x in Set.Ioi (0 : Real), G (x, y) ∂volume)
      = ENNReal.ofReal ((1 - Real.exp (-theta * y)) / theta) := by
    intro y
    by_cases hy : 0 < y
    · rw [hInner y, hInnerInt y hy]
    · have hy0 : y ≤ 0 := le_of_not_gt hy
      have hnonpos : (1 - Real.exp (-theta * y)) / theta ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ htheta.le
        have h1 : (1 : Real) ≤ Real.exp (-theta * y) := by
          have h := Real.add_one_le_exp (-theta * y)
          have hnn : (0 : Real) ≤ -theta * y :=
            mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr htheta.le) hy0
          linarith
        linarith
      rw [hInner y, Set.Ioo_eq_empty (show ¬ (0 : Real) < y from hy),
        ENNReal.ofReal_of_nonpos hnonpos]
      simp
  -- (5) Tonelli swap
  have hAEM : AEMeasurable (Function.uncurry (fun x y : Real => G (x, y)))
      ((volume.restrict (Set.Ioi (0 : Real))).prod Pi) := by
    have hEq : Function.uncurry (fun x y : Real => G (x, y)) = G := by
      funext ⟨x, y⟩
      rfl
    rw [hEq]
    exact hGmeas.aemeasurable
  have hPiRestrict : Pi.restrict (Set.Ioi (0 : Real)) = Pi := by
    have h0 : Pi.restrict (Set.Ioi (0 : Real))ᶜ = 0 := by
      rw [MeasureTheory.Measure.restrict_eq_zero]
      have hcompl : (Set.Ioi (0 : Real))ᶜ = Set.Iic (0 : Real) := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_Ioi, Set.mem_Iic, not_lt]
      rw [hcompl]
      exact hPi0
    have h : Pi.restrict (Set.Ioi (0 : Real)) + Pi.restrict (Set.Ioi (0 : Real))ᶜ = Pi :=
      MeasureTheory.Measure.restrict_add_restrict_compl measurableSet_Ioi
    rw [h0, add_zero] at h
    exact h
  have hOuter : (∫⁻ y, ENNReal.ofReal ((1 - Real.exp (-theta * y)) / theta) ∂Pi)
      = ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal ((1 - Real.exp (-theta * y)) / theta) ∂Pi := by
    conv_lhs => rw [← hPiRestrict]
  have hSwap : (∫⁻ x in Set.Ioi (0 : Real), ∫⁻ y, G (x, y) ∂Pi ∂volume)
      = ∫⁻ y, ∫⁻ x in Set.Ioi (0 : Real), G (x, y) ∂volume ∂Pi :=
    MeasureTheory.lintegral_lintegral_swap hAEM
  -- (6) bridge: ∫⁻ (1-e^{-θx})/θ dΠ = ofReal ((Φθ - dθ)/θ)
  have hBridge : (∫⁻ x in Set.Ioi (0 : Real),
        ENNReal.ofReal ((1 - Real.exp (-theta * x)) / theta) ∂Pi)
      = ENNReal.ofReal ((Phi theta - d * theta) / theta) := by
    have hnn : 0 ≤ᵐ[Pi.restrict (Set.Ioi (0 : Real))]
        fun x : Real => (1 - Real.exp (-theta * x)) / theta := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
      apply div_nonneg _ htheta.le
      apply sub_nonneg.mpr
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta.le) ha.le
    have hFin : (∫⁻ x in Set.Ioi (0 : Real),
        ENNReal.ofReal ((1 - Real.exp (-theta * x)) / theta) ∂Pi) ≠ ⊤ := by
      have hlt := (hDivInt theta htheta).2
      have heq : (∫⁻ x in Set.Ioi (0 : Real),
          ENNReal.ofReal ((1 - Real.exp (-theta * x)) / theta) ∂Pi)
          = ∫⁻ a, ‖(1 - Real.exp (-theta * a)) / theta‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real))) := by
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
        rw [Real.enorm_eq_ofReal]
        apply div_nonneg _ htheta.le
        apply sub_nonneg.mpr
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta.le) ha.le
      rw [heq]
      exact hlt.ne
    have hToReal : (∫⁻ x in Set.Ioi (0 : Real),
        ENNReal.ofReal ((1 - Real.exp (-theta * x)) / theta) ∂Pi).toReal
        = (Phi theta - d * theta) / theta := by
      have hEq : (∫⁻ x in Set.Ioi (0 : Real),
          ENNReal.ofReal ((1 - Real.exp (-theta * x)) / theta) ∂Pi)
          = ENNReal.ofReal (∫ x in Set.Ioi (0 : Real),
              (1 - Real.exp (-theta * x)) / theta ∂Pi) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hDivInt theta htheta) hnn]
      have hIntNonneg : 0 ≤ ∫ x in Set.Ioi (0 : Real),
          (1 - Real.exp (-theta * x)) / theta ∂Pi :=
        MeasureTheory.integral_nonneg_of_ae hnn
      rw [hEq, ENNReal.toReal_ofReal hIntNonneg, MeasureTheory.integral_div]
      have hPhi : Phi theta = d * theta
          + ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi := by
        have h := hPhiEq theta htheta.le
        simpa using h
      have hIntEq : (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi)
          = Phi theta - d * theta := by
        linarith
      rw [hIntEq]
    rw [← ENNReal.ofReal_toReal hFin, hToReal]
  -- (7) unfold positiveLaplace and the density; move Ici 0 to Ioi 0
  have hStep1 : positiveLaplace
        (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
          (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta
      = ∫⁻ x in Set.Ioi (0 : Real),
          ENNReal.ofReal ((Pi (Set.Ioi x)).toReal) * ENNReal.ofReal (Real.exp (-theta * x)) ∂volume := by
    show (∫⁻ x, ENNReal.ofReal (Real.exp (-theta * x)) ∂(((volume : Measure Real).restrict
          (Set.Ici (0 : Real))).withDensity
          (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal)))) = _
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ hTailMeas hExpMeas]
    simp only [_root_.Pi.mul_apply]
    rw [hIciIoi]
  calc positiveLaplace
        (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
          (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta
      = ∫⁻ x in Set.Ioi (0 : Real),
          ENNReal.ofReal ((Pi (Set.Ioi x)).toReal) * ENNReal.ofReal (Real.exp (-theta * x)) ∂volume :=
        hStep1
    _ = ∫⁻ x in Set.Ioi (0 : Real), (∫⁻ y, G (x, y) ∂Pi) ∂volume := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
          exact (hXSide x hx).symm
    _ = ∫⁻ y, (∫⁻ x in Set.Ioi (0 : Real), G (x, y) ∂volume) ∂Pi := hSwap
    _ = ∫⁻ y, ENNReal.ofReal ((1 - Real.exp (-theta * y)) / theta) ∂Pi := by
          apply MeasureTheory.lintegral_congr_ae
          exact ae_of_all _ (fun y => hYSide y)
    _ = ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal ((1 - Real.exp (-theta * y)) / theta) ∂Pi :=
        hOuter
    _ = ENNReal.ofReal ((Phi theta - d * theta) / theta) := hBridge
