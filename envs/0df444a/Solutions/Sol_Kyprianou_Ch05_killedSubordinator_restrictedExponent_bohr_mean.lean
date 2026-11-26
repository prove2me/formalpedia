-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_restrictedExponent_bohr_mean
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:17:52.45562+00:00
-- url     : https://prove2.me/submissions/54381195-4632-4094-8a8e-c0a82c22f5a0

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  (Pi (Set.Ioi (0 : Real)) = ⊤ →
    ∀ δ : Real, 0 < δ → δ ≤ 1 → ∀ ε : ENNReal, 0 < ε →
      ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ENNReal.ofReal (Pi (Set.Icc δ 1)).toReal + ε ∧
        ENNReal.ofReal (Pi (Set.Icc δ 1)).toReal ≤ (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε) := by
  intro _hPi δ hδ hδ1 ε hε
  have hLevy : (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi) < ⊤ :=
    hTriplet.2.2.2.1
  -- Pi (Icc δ 1) is finite, via the Lévy integrability field (pattern from the parent glue)
  have hfin : Pi (Set.Icc δ 1) < ⊤ := by
    have hstep : ENNReal.ofReal δ * Pi (Set.Icc δ 1)
        ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi := by
      calc ENNReal.ofReal δ * Pi (Set.Icc δ 1)
          = ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal δ ∂Pi := by
            rw [lintegral_const, Measure.restrict_apply_univ]
        _ ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (min 1 y) ∂Pi :=
            lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).mpr
              (Eventually.of_forall (fun y hy => ENNReal.ofReal_le_ofReal (le_min hδ1 hy.1))))
        _ ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi :=
            lintegral_mono_set (fun y hy => lt_of_lt_of_le hδ hy.1)
    by_contra htop
    have htop' : Pi (Set.Icc δ 1) = ⊤ := top_unique (not_lt.mp htop)
    rw [htop', ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))] at hstep
    exact lt_irrefl _ (lt_of_le_of_lt hstep hLevy)
  set Λ : Real := (Pi (Set.Icc δ 1)).toReal with hΛdef
  have hΛnn : 0 ≤ Λ := ENNReal.toReal_nonneg
  have hPiIcc : ENNReal.ofReal Λ = Pi (Set.Icc δ 1) := ENNReal.ofReal_toReal hfin.ne
  -- the restricted exponent is finite for every u
  have hRfin : ∀ u : Real,
      (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi) ≠ ⊤ := by
    intro u
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    calc (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi)
        ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal 2 ∂Pi := by
          apply lintegral_mono
          intro y
          apply ENNReal.ofReal_le_ofReal
          have h := Real.neg_one_le_cos (u * y)
          linarith
      _ = ENNReal.ofReal 2 * Pi (Set.Icc δ 1) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  -- scalar integral: ∫₀^U (1 - cos (u*y)) du = U - sin (U*y)/y, in lintegral form
  have hscalar : ∀ (U y : Real), 0 ≤ U → y ≠ 0 →
      (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (1 - Real.cos (u * y)) ∂volume)
        = ENNReal.ofReal (U - Real.sin (U * y) / y) := by
    intro U y hU hy
    have hcont : Continuous (fun u : Real => (1 : Real) - Real.cos (u * y)) :=
      continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const))
    have hInt : IntegrableOn (fun u : Real => (1 : Real) - Real.cos (u * y))
        (Set.Icc 0 U) volume := hcont.integrableOn_Icc
    have hnn : (0 : Real → Real) ≤ᵐ[volume.restrict (Set.Icc 0 U)]
        (fun u => 1 - Real.cos (u * y)) :=
      (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall (fun u _ =>
        sub_nonneg.mpr (Real.cos_le_one (u * y))))
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hU]
    have hderiv : ∀ u ∈ Set.uIcc (0 : Real) U,
        HasDerivAt (fun u => u - Real.sin (u * y) / y) (1 - Real.cos (u * y)) u := by
      intro u _
      have hmul : HasDerivAt (fun x : Real => x * y) y u := by
        simpa using (hasDerivAt_id u).mul_const y
      have hsin : HasDerivAt (fun u => Real.sin (u * y) / y) (Real.cos (u * y)) u := by
        have h := ((Real.hasDerivAt_sin (u * y)).comp u hmul).div_const y
        have e : Real.cos (u * y) * y / y = Real.cos (u * y) := by
          rw [mul_div_assoc, div_self hy, mul_one]
        rwa [e] at h
      exact (hasDerivAt_id u).sub hsin
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 U)]
    simp
  -- joint measurability of the Tonelli integrand
  have hFm : Measurable (fun p : Real × Real => ENNReal.ofReal (1 - Real.cos (p.1 * p.2))) :=
    (ENNReal.continuous_ofReal.comp
      (continuous_const.sub (Real.continuous_cos.comp (continuous_fst.mul continuous_snd)))).measurable
  by_cases hεtop : ε = ⊤
  · refine ⟨1 / δ, fun U _ => ?_⟩
    subst hεtop
    simp only [add_top]
    exact ⟨le_top, le_top⟩
  · have hεtoReal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    refine ⟨max (1 / δ) (Λ / (δ * ε.toReal)), fun U hU => ?_⟩
    have hUδ : 1 / δ ≤ U := (le_max_left _ _).trans hU
    have hUΛ : Λ / (δ * ε.toReal) ≤ U := (le_max_right _ _).trans hU
    have hUpos : 0 < U := lt_of_lt_of_le (one_div_pos.mpr hδ) hUδ
    have hδε : (0 : Real) < δ * ε.toReal := mul_pos hδ hεtoReal
    have hΛle : Λ ≤ U * (δ * ε.toReal) := (div_le_iff₀ hδε).mp hUΛ
    have hsmallℝ : Λ / (δ * U) ≤ ε.toReal := by
      rw [div_le_iff₀ (mul_pos hδ hUpos)]
      calc Λ ≤ U * (δ * ε.toReal) := hΛle
        _ = ε.toReal * (δ * U) := by ring
    have hsmall : ENNReal.ofReal (Λ / (δ * U)) ≤ ε :=
      (ENNReal.ofReal_le_ofReal hsmallℝ).trans_eq (ENNReal.ofReal_toReal hεtop)
    have hδUge1 : (1 : Real) ≤ δ * U :=
      (mul_one_div_cancel hδ.ne').symm ▸ mul_le_mul_of_nonneg_left hUδ hδ.le
    have hfrac : Λ / (δ * U) ≤ Λ := by
      rw [div_le_iff₀ (mul_pos hδ hUpos)]
      calc Λ = Λ * 1 := (mul_one Λ).symm
        _ ≤ Λ * (δ * U) := mul_le_mul_of_nonneg_left hδUge1 hΛnn
    have hΛfracnn : (0 : Real) ≤ Λ / (δ * U) :=
      div_nonneg hΛnn (mul_nonneg hδ.le hUpos.le)
    haveI : IsFiniteMeasure (Pi.restrict (Set.Icc δ 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : Real) U)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
          exact ENNReal.ofReal_lt_top⟩
    -- the Cesàro numerator, after Tonelli and the scalar integral
    have hGeq : (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ∂volume)
        = ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U - Real.sin (U * y) / y) ∂Pi := by
      calc (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ∂volume)
          = ∫⁻ u in Set.Icc (0 : Real) U, ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi ∂volume := by
            apply lintegral_congr
            intro u
            rw [ENNReal.ofReal_toReal (hRfin u)]
        _ = ∫⁻ y in Set.Icc δ 1, ∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (1 - Real.cos (u * y)) ∂volume ∂Pi :=
            lintegral_lintegral_swap (f := fun u y => ENNReal.ofReal (1 - Real.cos (u * y)))
              hFm.aemeasurable
        _ = ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U - Real.sin (U * y) / y) ∂Pi := by
            apply lintegral_congr_ae
            apply (ae_restrict_iff' measurableSet_Icc).mpr
            apply Eventually.of_forall
            intro y hy
            exact hscalar U y hUpos.le (ne_of_gt (lt_of_lt_of_le hδ hy.1))
    -- pointwise bound |sin (U*y)/y| ≤ 1/δ on Icc δ 1
    have hpt : ∀ y ∈ Set.Icc δ 1,
        - (1 / δ) ≤ Real.sin (U * y) / y ∧ Real.sin (U * y) / y ≤ 1 / δ := by
      intro y hy
      have hypos : 0 < y := lt_of_lt_of_le hδ hy.1
      have h1 : |Real.sin (U * y) / y| ≤ 1 / δ := by
        calc |Real.sin (U * y) / y| = |Real.sin (U * y)| / y := by
              rw [abs_div, abs_of_pos hypos]
          _ ≤ 1 / y := by
              gcongr
              exact Real.abs_sin_le_one (U * y)
          _ ≤ 1 / δ := one_div_le_one_div_of_le hδ hy.1
      exact abs_le.mp h1
    have hup : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U - Real.sin (U * y) / y) ∂Pi)
        ≤ ENNReal.ofReal (U + 1 / δ) * Pi (Set.Icc δ 1) := by
      calc (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U - Real.sin (U * y) / y) ∂Pi)
          ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U + 1 / δ) ∂Pi := by
            apply lintegral_mono_ae
            apply (ae_restrict_iff' measurableSet_Icc).mpr
            apply Eventually.of_forall
            intro y hy
            apply ENNReal.ofReal_le_ofReal
            have h := (hpt y hy).1
            linarith
        _ = ENNReal.ofReal (U + 1 / δ) * Pi (Set.Icc δ 1) := by
            rw [lintegral_const, Measure.restrict_apply_univ]
    have hlo : ENNReal.ofReal (U - 1 / δ) * Pi (Set.Icc δ 1)
        ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U - Real.sin (U * y) / y) ∂Pi := by
      calc ENNReal.ofReal (U - 1 / δ) * Pi (Set.Icc δ 1)
          = ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U - 1 / δ) ∂Pi := by
            rw [lintegral_const, Measure.restrict_apply_univ]
        _ ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U - Real.sin (U * y) / y) ∂Pi := by
            apply lintegral_mono_ae
            apply (ae_restrict_iff' measurableSet_Icc).mpr
            apply Eventually.of_forall
            intro y hy
            apply ENNReal.ofReal_le_ofReal
            have h := (hpt y hy).2
            linarith
    -- ENNReal factorizations
    have hw : (ENNReal.ofReal U)⁻¹ = ENNReal.ofReal U⁻¹ :=
      (ENNReal.ofReal_inv_of_pos hUpos).symm
    have hfact_up : ENNReal.ofReal (U + 1 / δ) * (ENNReal.ofReal U)⁻¹
        = ENNReal.ofReal (1 + 1 / (δ * U)) := by
      rw [hw, ← ENNReal.ofReal_mul (add_nonneg hUpos.le (one_div_nonneg.mpr hδ.le))]
      congr 1
      field_simp
    have hfact_lo : ENNReal.ofReal (U - 1 / δ) * (ENNReal.ofReal U)⁻¹
        = ENNReal.ofReal (1 - 1 / (δ * U)) := by
      rw [hw, ← ENNReal.ofReal_mul (sub_nonneg.mpr hUδ)]
      congr 1
      field_simp
    have hfact_up' : (ENNReal.ofReal (U + 1 / δ) * Pi (Set.Icc δ 1)) * (ENNReal.ofReal U)⁻¹
        = ENNReal.ofReal (Λ + Λ / (δ * U)) := by
      rw [← hPiIcc, mul_comm (ENNReal.ofReal (U + 1 / δ)) (ENNReal.ofReal Λ), mul_assoc,
        hfact_up, ← ENNReal.ofReal_mul hΛnn]
      congr 1
      ring
    have hfact_lo' : (ENNReal.ofReal (U - 1 / δ) * Pi (Set.Icc δ 1)) * (ENNReal.ofReal U)⁻¹
        = ENNReal.ofReal (Λ - Λ / (δ * U)) := by
      rw [← hPiIcc, mul_comm (ENNReal.ofReal (U - 1 / δ)) (ENNReal.ofReal Λ), mul_assoc,
        hfact_lo, ← ENNReal.ofReal_mul hΛnn]
      congr 1
      ring
    constructor
    · calc (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ∂volume) * (ENNReal.ofReal U)⁻¹
          = (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U - Real.sin (U * y) / y) ∂Pi) * (ENNReal.ofReal U)⁻¹ := by
            rw [hGeq]
        _ ≤ (ENNReal.ofReal (U + 1 / δ) * Pi (Set.Icc δ 1)) * (ENNReal.ofReal U)⁻¹ :=
            mul_le_mul hup le_rfl bot_le bot_le
        _ = ENNReal.ofReal (Λ + Λ / (δ * U)) := hfact_up'
        _ = ENNReal.ofReal Λ + ENNReal.ofReal (Λ / (δ * U)) :=
            ENNReal.ofReal_add hΛnn hΛfracnn
        _ ≤ ENNReal.ofReal Λ + ε := add_le_add le_rfl hsmall
    · calc ENNReal.ofReal Λ
          = ENNReal.ofReal (Λ - Λ / (δ * U)) + ENNReal.ofReal (Λ / (δ * U)) := by
            rw [← ENNReal.ofReal_add (sub_nonneg.mpr hfrac) hΛfracnn]
            congr 1
            ring
        _ ≤ (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (U - Real.sin (U * y) / y) ∂Pi) * (ENNReal.ofReal U)⁻¹ + ε := by
            apply add_le_add _ hsmall
            rw [← hfact_lo']
            exact mul_le_mul hlo le_rfl bot_le bot_le
        _ = (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε := by
            rw [← hGeq]
