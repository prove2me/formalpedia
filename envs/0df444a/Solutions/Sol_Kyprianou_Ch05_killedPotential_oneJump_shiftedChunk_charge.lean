-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_oneJump_shiftedChunk_charge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T11:31:31.045886+00:00
-- url     : https://prove2.me/submissions/e2b6c948-7893-4262-a3f3-c80306e38256
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_oneJump_shiftedChunk_pointwise
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
  (Pi (Set.Ioi (0 : Real)) < ⊤ →
    ∀ h : Real, 0 < h → ∀ a b : Real, 0 < a → a ≤ b →
      (∀ z ∈ Set.Icc a b, ∀ n : Int, z ≠ (n : Real) * h) →
      ∃ δ : Real, 0 < δ ∧ ENNReal.ofReal (δ^2 / 3) * Pi (Set.Icc a b) ≤
        ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}} ∂volume) := by
  intro hPi h hh a b ha hab hoff
  obtain ⟨δ, hδ, hpt⟩ := Kyprianou.Ch05.killedPotential_oneJump_shiftedChunk_pointwise
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hPi h hh a b ha hab hoff
  refine ⟨δ, hδ, ?_⟩
  -- Step 1: integrate the pointwise bound over t ∈ Ioc 0 δ.
  have hae : (fun t : Real => ENNReal.ofReal (2 * t / 3) * Pi (Set.Icc a b)) ≤ᵐ[volume.restrict (Set.Ioc (0 : Real) δ)]
      (fun t : Real => P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}}) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hpt)
  have hstep : (∫⁻ t in Set.Ioc (0 : Real) δ, ENNReal.ofReal (2 * t / 3) * Pi (Set.Icc a b) ∂volume)
      ≤ ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}} ∂volume :=
    lintegral_mono_ae hae
  -- Step 2: evaluate the scalar integral.
  have hfmeas : Measurable (fun t : Real => ENNReal.ofReal (2 * t / 3)) :=
    ((measurable_const.mul measurable_id).div_const 3).ennreal_ofReal
  have hcont : Continuous (fun t : Real => 2 * t / 3) := by fun_prop
  have hIntOn : IntegrableOn (fun t : Real => 2 * t / 3) (Set.Ioc (0 : Real) δ) volume :=
    (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hderiv : ∀ x : Real, HasDerivAt (fun x : Real => x^2 / 3) (2 * x / 3) x := by
    intro x
    simpa using (hasDerivAt_pow 2 x).div_const (3 : Real)
  have hint : IntervalIntegrable (fun x : Real => 2 * x / 3) volume 0 δ :=
    hcont.intervalIntegrable 0 δ
  have hdiff : ∀ x ∈ Set.uIcc (0 : Real) δ, DifferentiableAt Real (fun x : Real => x^2 / 3) x :=
    fun x _ => (by fun_prop : Differentiable Real (fun x : Real => x^2 / 3)) x
  have hderEq : deriv (fun x : Real => x^2 / 3) = (fun x : Real => 2 * x / 3) :=
    funext fun x => (hderiv x).deriv
  have hint2 : IntervalIntegrable (deriv (fun x : Real => x^2 / 3)) volume 0 δ := by
    rw [hderEq]; exact hint
  have hBochner : ∫ t in Set.Ioc (0 : Real) δ, (2 * t / 3 : Real) = δ^2 / 3 := by
    rw [← intervalIntegral.integral_of_le hδ.le, ← hderEq,
      intervalIntegral.integral_deriv_eq_sub hdiff hint2]
    simp
  have hnn : (0 : Real → Real) ≤ᵐ[volume.restrict (Set.Ioc (0 : Real) δ)]
      (fun t : Real => 2 * t / 3) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun t ht => by
      show (0 : Real) ≤ 2 * t / 3
      linarith [ht.1.le]))
  have hEval : (∫⁻ t in Set.Ioc (0 : Real) δ, ENNReal.ofReal (2 * t / 3) ∂volume)
      = ENNReal.ofReal (δ^2 / 3) := by
    rw [← hBochner]
    exact (ofReal_integral_eq_lintegral_ofReal hIntOn hnn).symm
  have hInt : (∫⁻ t in Set.Ioc (0 : Real) δ, ENNReal.ofReal (2 * t / 3) * Pi (Set.Icc a b) ∂volume)
      = ENNReal.ofReal (δ^2 / 3) * Pi (Set.Icc a b) := by
    have hcong : (∫⁻ t in Set.Ioc (0 : Real) δ, ENNReal.ofReal (2 * t / 3) * Pi (Set.Icc a b) ∂volume)
        = ∫⁻ t in Set.Ioc (0 : Real) δ, Pi (Set.Icc a b) * ENNReal.ofReal (2 * t / 3) ∂volume :=
      lintegral_congr (fun t => mul_comm _ _)
    rw [hcong, lintegral_const_mul _ hfmeas, hEval, mul_comm]
  rw [hInt] at hstep
  exact hstep
