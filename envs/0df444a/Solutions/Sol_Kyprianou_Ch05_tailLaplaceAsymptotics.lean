-- Prove2me | solution 1 for Kyprianou.Ch05.tailLaplaceAsymptotics
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T04:52:45.811029+00:00
-- url     : https://prove2.me/submissions/2c8abee4-ef77-452a-9a80-aed32a041424
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
import Theorems.Thm_Kyprianou_Ch05_killedLaplaceExponent_continuousOn
import Theorems.Thm_Kyprianou_Ch05_slowlyVaryingAtInfinity_rpow
import Theorems.Thm_Kyprianou_Ch05_slowlyVaryingAtZero_rpow
import Theorems.Thm_Kyprianou_Ch05_killedTailLaplaceTransform
import Theorems.Thm_Kyprianou_Ch05_killedLaplaceExponentDivTendstoAtZero
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05

/-- Lemma 5.17, step 2 (tail): the Lévy tail, as a density on
`[0, ∞)`, has Laplace transform `(Phi theta - d * theta) / theta`,
and for `alpha < 1` regular variation of `Phi` transports to a
Karamata-ready Laplace asymptotic, at both endpoints. The drift term
is negligible: at zero it is `o(Phi theta)`, and at infinity regular
variation of index `< 1` forces `d = 0`. The tail is antitone, hence
ultimately monotone in both senses used by Theorems 5.14 / 5.15. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1) (hAlpha1 : alpha < 1) :
  ((RegularlyVaryingAtZero Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtInfinity L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x) ∧
       UltimatelyMonotone (fun x : Real => (Pi (Set.Ioi x)).toReal) ∧
       UltimatelyMonotoneAtZero (fun x : Real => (Pi (Set.Ioi x)).toReal) ∧
       ((((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
           (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal)))
         (Set.Iio (0 : Real)) = 0) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace
             (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
               (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta).toReal /
             (theta ^ (-(1 - alpha)) * L (1 / theta)))
         (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ∧
   (RegularlyVaryingAtInfinity Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtZero L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x) ∧
       UltimatelyMonotone (fun x : Real => (Pi (Set.Ioi x)).toReal) ∧
       UltimatelyMonotoneAtZero (fun x : Real => (Pi (Set.Ioi x)).toReal) ∧
       ((((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
           (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal)))
         (Set.Iio (0 : Real)) = 0) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace
             (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
               (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta).toReal /
             (theta ^ (-(1 - alpha)) * L (1 / theta)))
         atTop (nhds 1))) := by
  obtain ⟨heta, hd, hPi0, hInt, hPhiEq⟩ := hTriplet
  have hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi := ⟨heta, hd, hPi0, hInt, hPhiEq⟩
  -- The tail is finite away from zero (finite-variation hypothesis).
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
  -- The tail function is antitone, hence measurable.
  have hTailAnti : Antitone (fun x : Real => Pi (Set.Ioi x)) := by
    intro a b hab
    exact measure_mono (Set.Ioi_subset_Ioi hab)
  have hTailMeas : Measurable (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal)) :=
    Measurable.ennreal_ofReal (Measurable.ennreal_toReal hTailAnti.measurable)
  have hAntiOn : ∀ s : Set Real, (∀ x ∈ s, 0 < x) →
      AntitoneOn (fun x : Real => (Pi (Set.Ioi x)).toReal) s := by
    intro s hs a ha b hb hab
    exact ENNReal.toReal_mono (hPiFin a (hs a ha)) (measure_mono (Set.Ioi_subset_Ioi hab))
  have hMono : UltimatelyMonotone (fun x : Real => (Pi (Set.Ioi x)).toReal) :=
    ⟨1, Or.inr (hAntiOn (Set.Ici 1) (fun x hx => lt_of_lt_of_le one_pos hx))⟩
  have hMono0 : UltimatelyMonotoneAtZero (fun x : Real => (Pi (Set.Ioi x)).toReal) :=
    ⟨1, one_pos, Or.inr (hAntiOn (Set.Ioc 0 1) (fun x hx => hx.1))⟩
  -- The density measure is supported on [0, ∞).
  have hSupp : ((((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
      (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) (Set.Iio (0 : Real)) = 0) := by
    rw [MeasureTheory.withDensity_apply _ measurableSet_Iio]
    have hcap : Set.Iio (0 : Real) ∩ Set.Ici (0 : Real) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iio, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 h2
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl x)
    rw [MeasureTheory.Measure.restrict_restrict measurableSet_Iio, hcap,
      MeasureTheory.Measure.restrict_empty, MeasureTheory.lintegral_zero_measure]
  -- The tail Laplace transform (helper H2), in real form.
  have hLap : ∀ theta : Real, 0 < theta →
      positiveLaplace (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
        (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta
        = ENNReal.ofReal ((Phi theta - d * theta) / theta) :=
    fun theta htheta => killedTailLaplaceTransform d Pi Phi hTriplet theta htheta
  have hPhiSub : ∀ theta : Real, 0 < theta → 0 ≤ Phi theta - d * theta := by
    intro theta htheta
    have h := hPhiEq theta htheta.le
    have hnn : 0 ≤ ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi := by
      apply integral_nonneg_of_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta.le) (Set.mem_Ioi.mp hx).le))
    rw [h]
    linarith [hnn]
  have hLapReal : ∀ theta : Real, 0 < theta →
      (positiveLaplace (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
        (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta).toReal
        = (Phi theta - d * theta) / theta := by
    intro theta htheta
    rw [hLap theta htheta, ENNReal.toReal_ofReal (div_nonneg (hPhiSub theta htheta) htheta.le)]
  -- The slowly varying factor, defined directly from Phi.
  set M : Real → Real := fun x => Phi (1 / x) / x ^ (-alpha) with hMdef
  have hMlink : ∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * M x := by
    intro x hx
    have hr : x ^ (-alpha) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
    simp only [hMdef]
    field_simp
  have hMcont : ContinuousOn M (Set.Ioi (0 : Real)) := by
    have hPhiC : ContinuousOn Phi (Set.Ici (0 : Real)) :=
      killedLaplaceExponent_continuousOn 0 d Pi Phi hTriplet
    have hinv : ContinuousOn (fun x : Real => (1 : Real) / x) (Set.Ioi (0 : Real)) := by
      have h : ContinuousOn (fun x : Real => x⁻¹) (Set.Ioi (0 : Real)) :=
        continuousOn_id.inv₀ (fun x hx => ne_of_gt (Set.mem_Ioi.mp hx))
      simpa only [one_div] using h
    have hcomp : ContinuousOn (fun x : Real => Phi (1 / x)) (Set.Ioi (0 : Real)) := by
      apply ContinuousOn.comp hPhiC hinv
      intro x hx
      exact le_of_lt (one_div_pos.mpr (Set.mem_Ioi.mp hx))
    have hrpow : ContinuousOn (fun x : Real => x ^ (-alpha)) (Set.Ioi (0 : Real)) := by
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      exact Or.inl (ne_of_gt (Set.mem_Ioi.mp hx))
    simp only [hMdef]
    exact hcomp.div hrpow (fun x hx => ne_of_gt (Real.rpow_pos_of_pos hx _))
  have hMθ : ∀ theta : Real, 0 < theta → M (1 / theta) = Phi theta / theta ^ alpha := by
    intro theta htheta
    have h := hMlink (1 / theta) (one_div_pos.mpr htheta)
    rw [one_div_one_div] at h
    have h1 : (1 / theta) ^ (-alpha) = theta ^ alpha := by
      rw [Real.div_rpow zero_le_one htheta.le, Real.one_rpow, one_div,
        Real.rpow_neg htheta.le, inv_inv]
    rw [h1] at h
    rw [eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos htheta _)), h]
    ring
  have hθpow : ∀ theta : Real, 0 < theta →
      theta ^ (-(1 - alpha)) = theta ^ alpha / theta := by
    intro theta htheta
    rw [show -(1 - alpha) = alpha - 1 by ring, Real.rpow_sub htheta, Real.rpow_one]
  constructor
  · intro hRV
    have hMpos : ∀ x : Real, 0 < x → 0 < M x := by
      intro x hx
      simp only [hMdef]
      exact div_pos (hRV.1 _ (one_div_pos.mpr hx)) (Real.rpow_pos_of_pos hx _)
    have hslow : SlowlyVaryingAtInfinity M := by
      refine ⟨hMpos, fun a ha => ?_⟩
      have hlim : Tendsto (fun x : Real => Phi (1 / x) / Phi (1 / (a * x))) atTop
          (nhds (a ^ alpha)) := by
        have hcomp : Tendsto (fun x : Real => (a * x)⁻¹) atTop
            (nhdsWithin (0 : Real) (Set.Ioi 0)) :=
          tendsto_inv_atTop_nhdsGT_zero.comp (tendsto_id.const_mul_atTop ha)
        have h := (hRV.2 a ha).comp hcomp
        apply h.congr'
        filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
        have ha0 : a ≠ 0 := ne_of_gt ha
        have hx0 : x ≠ 0 := ne_of_gt hx
        simp only [Function.comp_apply]
        have e1 : a * (a * x)⁻¹ = 1 / x := by
          rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul, inv_eq_one_div]
        have e2 : (a * x)⁻¹ = 1 / (a * x) := by rw [one_div]
        rw [e1, e2]
      have hratio : Tendsto (fun x : Real => M (a * x) / M x) atTop (nhds 1) := by
        have h5 : (0 : Real) < a ^ alpha := Real.rpow_pos_of_pos ha _
        have heq : ∀ᶠ x in atTop, M (a * x) / M x
            = (Phi (1 / x) / Phi (1 / (a * x)))⁻¹ * a ^ alpha := by
          filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
          have hax : 0 < a * x := mul_pos ha hx
          have h1 : 0 < Phi (1 / x) := hRV.1 _ (one_div_pos.mpr hx)
          have h2 : 0 < Phi (1 / (a * x)) := hRV.1 _ (one_div_pos.mpr hax)
          have h3 : (0 : Real) < x ^ (-alpha) := Real.rpow_pos_of_pos hx _
          have h4 : (0 : Real) < (a * x) ^ (-alpha) := Real.rpow_pos_of_pos hax _
          have h6 : (0 : Real) < a ^ (-alpha) := Real.rpow_pos_of_pos ha _
          simp only [hMdef]
          rw [Real.mul_rpow ha.le hx.le, Real.rpow_neg ha.le]
          field_simp
        have h2 := hlim.inv₀ (ne_of_gt h5)
        have h3 := h2.mul_const (a ^ alpha)
        rw [inv_mul_cancel₀ (ne_of_gt h5)] at h3
        exact h3.congr' (heq.mono fun x h => h.symm)
      simpa only [Real.rpow_zero] using hratio
    refine ⟨M, hslow, hMlink, hMono, hMono0, hSupp, ?_⟩
    have hRatioEq : ∀ᶠ theta in nhdsWithin (0 : Real) (Set.Ioi 0),
        (positiveLaplace (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
          (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta).toReal /
          (theta ^ (-(1 - alpha)) * M (1 / theta))
          = 1 - d * (theta / Phi theta) := by
      filter_upwards [self_mem_nhdsWithin] with theta htheta
      have hθ : (0 : Real) < theta := Set.mem_Ioi.mp htheta
      have hΦ : 0 < Phi theta := hRV.1 _ hθ
      have hθa : (0 : Real) < theta ^ alpha := Real.rpow_pos_of_pos hθ _
      have hθ0 : theta ≠ 0 := ne_of_gt hθ
      have hΦ0 : Phi theta ≠ 0 := ne_of_gt hΦ
      have hθa0 : theta ^ alpha ≠ 0 := ne_of_gt hθa
      rw [hLapReal theta hθ, hMθ theta hθ, hθpow theta hθ]
      field_simp
    have hDrift : Tendsto (fun theta : Real => d * (theta / Phi theta))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) := by
      have h3 := killedLaplaceExponentDivTendstoAtZero d Pi Phi hTriplet alpha hAlpha hAlpha1 hRV
      have hinv : Tendsto (fun theta : Real => (Phi theta / theta)⁻¹)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) := h3.inv_tendsto_atTop
      have h0 : Tendsto (fun theta : Real => theta / Phi theta)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) := by
        apply hinv.congr'
        filter_upwards [self_mem_nhdsWithin] with theta htheta
        have hΦ : 0 < Phi theta := hRV.1 _ htheta
        rw [inv_div]
      simpa using h0.const_mul d
    have hTend : Tendsto (fun theta : Real => 1 - d * (theta / Phi theta))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hDrift
    rw [sub_zero] at hTend
    exact hTend.congr' (hRatioEq.mono fun theta h => h.symm)
  · intro hRV
    have hMpos : ∀ x : Real, 0 < x → 0 < M x := by
      intro x hx
      simp only [hMdef]
      exact div_pos (hRV.1 _ (one_div_pos.mpr hx)) (Real.rpow_pos_of_pos hx _)
    have hslow0 : SlowlyVaryingAtZero M := by
      refine ⟨hMpos, fun a ha => ?_⟩
      have hlim : Tendsto (fun s : Real => Phi (1 / s) / Phi (1 / (a * s)))
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (a ^ alpha)) := by
        have hmul : Tendsto (fun s : Real => a * s) (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhdsWithin (0 : Real) (Set.Ioi 0)) := by
          have h1 : Tendsto (fun s : Real => a * s) (nhds (0 : Real)) (nhds (0 : Real)) := by
            have h2 : Tendsto (id : Real → Real) (nhds (0 : Real)) (nhds (0 : Real)) :=
              tendsto_id
            simpa using h2.const_mul a
          have h2 : ∀ᶠ s in nhdsWithin (0 : Real) (Set.Ioi 0), a * s ∈ Set.Ioi 0 := by
            filter_upwards [self_mem_nhdsWithin] with s hs
            exact mul_pos ha (Set.mem_Ioi.mp hs)
          exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
            (fun s : Real => a * s) (h1.mono_left nhdsWithin_le_nhds) h2
        have hcomp : Tendsto (fun s : Real => (a * s)⁻¹) (nhdsWithin (0 : Real) (Set.Ioi 0))
            atTop := tendsto_inv_nhdsGT_zero.comp hmul
        have h := (hRV.2 a ha).comp hcomp
        apply h.congr'
        filter_upwards [self_mem_nhdsWithin] with s hs
        have ha0 : a ≠ 0 := ne_of_gt ha
        have hs0 : s ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hs)
        simp only [Function.comp_apply]
        have e1 : a * (a * s)⁻¹ = 1 / s := by
          rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul, inv_eq_one_div]
        have e2 : (a * s)⁻¹ = 1 / (a * s) := by rw [one_div]
        rw [e1, e2]
      have hratio : Tendsto (fun s : Real => M (a * s) / M s)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) := by
        have h5 : (0 : Real) < a ^ alpha := Real.rpow_pos_of_pos ha _
        have heq : ∀ᶠ s in nhdsWithin (0 : Real) (Set.Ioi 0), M (a * s) / M s
            = (Phi (1 / s) / Phi (1 / (a * s)))⁻¹ * a ^ alpha := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          have has : 0 < a * s := mul_pos ha (Set.mem_Ioi.mp hs)
          have h1 : 0 < Phi (1 / s) := hRV.1 _ (one_div_pos.mpr (Set.mem_Ioi.mp hs))
          have h2 : 0 < Phi (1 / (a * s)) := hRV.1 _ (one_div_pos.mpr has)
          have h3 : (0 : Real) < s ^ (-alpha) := Real.rpow_pos_of_pos (Set.mem_Ioi.mp hs) _
          have h4 : (0 : Real) < (a * s) ^ (-alpha) := Real.rpow_pos_of_pos has _
          have h6 : (0 : Real) < a ^ (-alpha) := Real.rpow_pos_of_pos ha _
          simp only [hMdef]
          rw [Real.mul_rpow ha.le (Set.mem_Ioi.mp hs).le, Real.rpow_neg ha.le]
          field_simp
        have h2 := hlim.inv₀ (ne_of_gt h5)
        have h3 := h2.mul_const (a ^ alpha)
        rw [inv_mul_cancel₀ (ne_of_gt h5)] at h3
        exact h3.congr' (heq.mono fun s h => h.symm)
      simpa only [Real.rpow_zero] using hratio
    have hd0 : d = 0 := by
      have heps : 0 < 1 - alpha := sub_pos.mpr hAlpha1
      have hInv : Tendsto (fun s : Real => (M s)⁻¹ / s ^ (1 - alpha))
          (nhdsWithin (0 : Real) (Set.Ioi 0)) atTop := by
        apply slowlyVaryingAtZero_rpow (fun s => (M s)⁻¹) ?_ ?_ ?_ (1 - alpha) heps
        · intro s hs
          exact inv_pos.mpr (hMpos s hs)
        · intro a ha
          have h := hslow0.2 a ha
          rw [Real.rpow_zero] at h
          have hinv := h.inv₀ one_ne_zero
          rw [inv_one] at hinv
          apply hinv.congr'
          filter_upwards [self_mem_nhdsWithin] with s hs
          rw [inv_div, div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_comm]
        · exact hMcont.inv₀ (fun s hs => ne_of_gt (hMpos s (Set.mem_Ioi.mp hs)))
      have hMs : Tendsto (fun s : Real => M s * s ^ (1 - alpha))
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) := by
        have h := hInv.inv_tendsto_atTop
        apply h.congr'
        filter_upwards [self_mem_nhdsWithin] with s hs
        show ((M s)⁻¹ / s ^ (1 - alpha))⁻¹ = M s * s ^ (1 - alpha)
        rw [div_eq_mul_inv, mul_inv, inv_inv, inv_inv]
      have hPhiDiv : Tendsto (fun theta : Real => Phi theta / theta) atTop (nhds 0) := by
        have hEq : ∀ᶠ theta in atTop,
            Phi theta / theta = M (1 / theta) * (1 / theta) ^ (1 - alpha) := by
          filter_upwards [eventually_gt_atTop (0 : Real)] with theta htheta
          have h := hMlink (1 / theta) (one_div_pos.mpr htheta)
          rw [one_div_one_div] at h
          have h1 : (1 / theta) ^ (-alpha) = theta ^ alpha := by
            rw [Real.div_rpow zero_le_one htheta.le, Real.one_rpow, one_div,
              Real.rpow_neg htheta.le, inv_inv]
          rw [h1] at h
          have h2 : (1 / theta) ^ (1 - alpha) = theta ^ (alpha - 1) := by
            rw [Real.div_rpow zero_le_one htheta.le, Real.one_rpow, one_div,
              ← Real.rpow_neg htheta.le]
            congr 1
            ring
          rw [h2, h, Real.rpow_sub htheta, Real.rpow_one]
          have hθ0 : theta ≠ 0 := ne_of_gt htheta
          field_simp
        have hcomp : Tendsto (fun theta : Real => M (1 / theta) * (1 / theta) ^ (1 - alpha))
            atTop (nhds 0) := by
          have h := hMs.comp tendsto_inv_atTop_nhdsGT_zero
          simpa only [Function.comp_def, one_div] using h
        exact hcomp.congr' (hEq.mono fun theta h => h.symm)
      have hdle : d ≤ 0 := by
        apply le_of_tendsto_of_tendsto tendsto_const_nhds hPhiDiv
        filter_upwards [eventually_gt_atTop (0 : Real)] with theta htheta
        have h := hPhiEq theta htheta.le
        have hnn : 0 ≤ ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi := by
          apply integral_nonneg_of_ae
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
          exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta.le) (Set.mem_Ioi.mp hx).le))
        rw [h, le_div_iff₀ htheta]
        linarith [hnn]
      exact le_antisymm hdle hd
    refine ⟨M, hslow0, hMlink, hMono, hMono0, hSupp, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with theta htheta
    have hΦ : 0 < Phi theta := hRV.1 _ htheta
    rw [hLapReal theta htheta, hMθ theta htheta, hθpow theta htheta, hd0]
    field_simp
    ring

