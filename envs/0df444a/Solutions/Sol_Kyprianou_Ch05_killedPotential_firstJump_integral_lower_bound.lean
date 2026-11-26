-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_firstJump_integral_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T04:19:48.292669+00:00
-- url     : https://prove2.me/submissions/24a58436-f9e2-4b7d-a92b-649cf4e8d3cb

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
  (∀ h : Real, ∀ q : Real, 0 ≤ q → ∀ δ : Real, ∀ c : ℝ≥0∞,
    c ≤ ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume →
    ENNReal.ofReal (Real.exp (-q * δ)) * c ≤
      ∫⁻ t in Set.Ici (0 : Real),
        ENNReal.ofReal (Real.exp (-q * t)) *
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume) := by
  intro h q hq δ c hc
  set f : Real → ℝ≥0∞ := fun t => P {omega : Omega |
    (Real.toNNReal t : WithTop NNReal) < death omega ∧
      Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} with hf_def
  set K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-q * δ)) with hK_def
  -- Step 3 (the crux): constant factor through the lintegral, measurability-free,
  -- via withDensity (constant density is measurable) + smul-measure.
  have h3 : ∫⁻ t in Set.Ioc (0 : Real) δ, K * f t ∂volume
      = K * ∫⁻ t in Set.Ioc (0 : Real) δ, f t ∂volume := by
    have hwd : ∫⁻ t in Set.Ioc (0 : Real) δ, K * f t ∂volume
        = ∫⁻ t, f t ∂((volume.restrict (Set.Ioc (0 : Real) δ)).withDensity (fun _ => K)) :=
      (MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (measurable_const : Measurable (fun _ : Real => K))
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f).symm
    rw [hwd, MeasureTheory.withDensity_const, MeasureTheory.lintegral_smul_measure,
      smul_eq_mul]
  -- Step 2: pointwise discount comparison on Ioc 0 δ.
  have hpt : ∀ t ∈ Set.Ioc (0 : Real) δ,
      K * f t ≤ ENNReal.ofReal (Real.exp (-q * t)) * f t := by
    intro t ht
    have h1 : q * t ≤ q * δ := mul_le_mul_of_nonneg_left ht.2 hq
    have h2 : -q * δ ≤ -q * t := by
      have e1 : -q * δ = -(q * δ) := by ring
      have e2 : -q * t = -(q * t) := by ring
      rw [e1, e2]; exact neg_le_neg h1
    have hexp : K ≤ ENNReal.ofReal (Real.exp (-q * t)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h2)
    exact mul_le_mul' hexp (le_refl _)
  have h2 : ∫⁻ t in Set.Ioc (0 : Real) δ, K * f t ∂volume
      ≤ ∫⁻ t in Set.Ioc (0 : Real) δ,
          ENNReal.ofReal (Real.exp (-q * t)) * f t ∂volume := by
    apply MeasureTheory.lintegral_mono_ae
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun t ht => hpt t ht)
  -- Step 1: enlarge the set Ioc 0 δ ⊆ Ici 0.
  have h1 : ∫⁻ t in Set.Ioc (0 : Real) δ,
        ENNReal.ofReal (Real.exp (-q * t)) * f t ∂volume
      ≤ ∫⁻ t in Set.Ici (0 : Real),
          ENNReal.ofReal (Real.exp (-q * t)) * f t ∂volume :=
    MeasureTheory.lintegral_mono_set (fun t ht => ht.1.le)
  calc K * c ≤ K * ∫⁻ t in Set.Ioc (0 : Real) δ, f t ∂volume :=
        mul_le_mul' (le_refl K) hc
    _ = ∫⁻ t in Set.Ioc (0 : Real) δ, K * f t ∂volume := h3.symm
    _ ≤ ∫⁻ t in Set.Ioc (0 : Real) δ,
          ENNReal.ofReal (Real.exp (-q * t)) * f t ∂volume := h2
    _ ≤ ∫⁻ t in Set.Ici (0 : Real),
          ENNReal.ofReal (Real.exp (-q * t)) * f t ∂volume := h1
