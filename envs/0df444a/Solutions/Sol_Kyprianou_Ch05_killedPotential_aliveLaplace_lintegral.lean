-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_aliveLaplace_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T10:00:51.339526+00:00
-- url     : https://prove2.me/submissions/3013368e-a543-4bc8-a07d-33e5d5779cc8

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_aliveLintegral_factor
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
  ∀ (t : Real), 0 ≤ t → ∀ theta : Real, 0 ≤ theta →
      (∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
        ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P) =
      ENNReal.ofReal (Real.exp (-t * Phi theta)) := by
  intro t ht theta htheta
  have hYAEMeas : ∀ s : NNReal, AEMeasurable (Y s) P := by
    intro s
    have h := (hKilled.1.1.stationary_increments 0 s).1
    have hinc : ProbabilityTheory.increment Y 0 (0 + s) = Y s := by
      funext ω
      simp [ProbabilityTheory.increment, hKilled.1.1.start_zero]
    rwa [hinc] at h
  -- `Y t' ≥ 0` a.e., from a.e. monotonicity and `Y 0 = 0`.
  have hYnn : ∀ᵐ omega ∂P, 0 ≤ Y (Real.toNNReal t) omega := by
    filter_upwards [hKilled.1.2] with omega hω
    have h0 : Y 0 omega = 0 := congrFun hKilled.1.1.start_zero omega
    have hle : Y 0 omega ≤ Y (Real.toNNReal t) omega := hω bot_le
    rwa [h0] at hle
  have heAEMeas : AEMeasurable
      (fun omega : Omega => Real.exp (-theta * Y (Real.toNNReal t) omega)) P :=
    Real.measurable_exp.comp_aemeasurable
      ((measurable_const_mul (-theta)).comp_aemeasurable
        (hYAEMeas (Real.toNNReal t)))
  have heInt : Integrable
      (fun omega : Omega => Real.exp (-theta * Y (Real.toNNReal t) omega)) P := by
    refine Integrable.of_bound heAEMeas.aestronglyMeasurable 1 ?_
    filter_upwards [hYnn] with omega hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta) hω)
  have hconv : (∫⁻ omega, ENNReal.ofReal
        (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P)
      = ENNReal.ofReal (Real.exp (-t * (Phi theta - eta))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal heInt
      (by filter_upwards with omega; exact Real.exp_nonneg _),
      hLaplaceLaw (Real.toNNReal t) theta htheta, Real.coe_toNNReal t ht]
  rw [Kyprianou.Ch05.killedPotential_aliveLintegral_factor P Y death eta d Pi Phi
    hKilled hTriplet hLaplaceLaw U hPotential t ht theta htheta, hconv,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 1
  ring
