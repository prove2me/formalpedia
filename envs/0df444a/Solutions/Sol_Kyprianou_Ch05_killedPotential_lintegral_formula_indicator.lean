-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_lintegral_formula_indicator
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T11:35:55.792262+00:00
-- url     : https://prove2.me/submissions/31862787-dfdd-4a56-9197-2a97d1393828

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_inner_aemeasurable
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
  ∀ q : Real, 0 ≤ q → ∀ (c : ENNReal) (B : Set Real), MeasurableSet B →
      (∫⁻ x : Real, B.indicator (fun _ => c) x ∂(U q)) =
        ∫⁻ t in Set.Ici (0 : Real),
          ENNReal.ofReal (Real.exp (-q * t)) *
          ∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
            B.indicator (fun _ => c) (Y (Real.toNNReal t) omega) ∂P ∂volume := by
  intro q hq c B hB
  -- The marginals are a.e. measurable (probe-verified derivation).
  have hYAEMeas : ∀ s : NNReal, AEMeasurable (Y s) P := by
    intro s
    have hstat := hKilled.1.1.stationary_increments 0 s
    have hm2 : AEMeasurable (ProbabilityTheory.increment Y 0 s) P :=
      hstat.aemeasurable_snd
    have h0 : Y 0 = fun _ => (0 : Real) := hKilled.1.1.start_zero
    have heq : ProbabilityTheory.increment Y 0 s = Y s := by
      funext ω
      simp only [ProbabilityTheory.increment, h0]
      simp
    rwa [heq] at hm2
  have hdeath : Measurable death := hKilled.2.2.1
  -- Inner integral evaluation, for every constant: the occupation set is only
  -- null-measurable (Y is only a.e. measurable), which is enough for the
  -- indicator lintegral.
  have hinner : ∀ (c' : ENNReal) (t : Real),
      (∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
          B.indicator (fun _ => c') (Y (Real.toNNReal t) omega) ∂P)
        = c' * P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ B} := by
    intro c' t
    set A : Set Omega := {omega : Omega |
      (Real.toNNReal t : WithTop NNReal) < death omega} with hAdef
    set S : Set Omega := {omega : Omega |
      (Real.toNNReal t : WithTop NNReal) < death omega ∧
        Y (Real.toNNReal t) omega ∈ B} with hSdef
    have hA : MeasurableSet A := measurableSet_lt measurable_const hdeath
    have hSeq : S = A ∩ Y (Real.toNNReal t) ⁻¹' B := by
      ext ω
      simp only [hSdef, hAdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    have hS : NullMeasurableSet S P := by
      rw [hSeq]
      exact hA.nullMeasurableSet.inter
        ((hYAEMeas (Real.toNNReal t)).nullMeasurableSet_preimage hB)
    have hfun : A.indicator
          (fun omega => B.indicator (fun _ => c') (Y (Real.toNNReal t) omega))
        = S.indicator (fun _ => c') := by
      funext ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        by_cases hY : Y (Real.toNNReal t) ω ∈ B
        · rw [Set.indicator_of_mem hY,
            Set.indicator_of_mem (show ω ∈ S from ⟨hω, hY⟩)]
        · rw [Set.indicator_of_notMem hY,
            Set.indicator_of_notMem (show ω ∉ S from fun h => hY h.2)]
      · rw [Set.indicator_of_notMem hω,
          Set.indicator_of_notMem (show ω ∉ S from fun h => hω h.1)]
    calc (∫⁻ omega in A, B.indicator (fun _ => c') (Y (Real.toNNReal t) omega) ∂P)
        = ∫⁻ omega, A.indicator
            (fun omega => B.indicator (fun _ => c') (Y (Real.toNNReal t) omega))
            omega ∂P :=
          (lintegral_indicator hA _).symm
      _ = ∫⁻ omega, S.indicator (fun _ => c') omega ∂P := by rw [hfun]
      _ = c' * P S := lintegral_indicator_const₀ hS c'
  -- The occupation integrand is a.e. measurable in t: this is L1b applied to
  -- the unit indicator, transported along the pointwise identity hinner.
  have hinnerAE : AEMeasurable (fun t : Real =>
      ∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
        B.indicator (fun _ => (1 : ENNReal)) (Y (Real.toNNReal t) omega) ∂P)
      (volume.restrict (Set.Ici (0 : Real))) :=
    Kyprianou.Ch05.killedPotential_inner_aemeasurable P Y death eta d Pi Phi
      hKilled hTriplet hLaplaceLaw U hPotential (B.indicator (fun _ => (1 : ENNReal)))
      (measurable_const.indicator hB)
  have hcongr : (fun t : Real =>
      ∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
        B.indicator (fun _ => (1 : ENNReal)) (Y (Real.toNNReal t) omega) ∂P)
      = (fun t : Real => P {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ B}) := by
    funext t
    rw [hinner 1 t, one_mul]
  have hPAE : AEMeasurable (fun t : Real => P {omega : Omega |
      (Real.toNNReal t : WithTop NNReal) < death omega ∧
        Y (Real.toNNReal t) omega ∈ B})
      (volume.restrict (Set.Ici (0 : Real))) :=
    hinnerAE.congr (Filter.EventuallyEq.of_eq hcongr)
  have hcmeas : Measurable (fun t : Real => ENNReal.ofReal (Real.exp (-q * t))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul _))
  have hoccAE : AEMeasurable (fun t : Real =>
      ENNReal.ofReal (Real.exp (-q * t)) *
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ B})
      (volume.restrict (Set.Ici (0 : Real))) :=
    hcmeas.aemeasurable.mul hPAE
  -- The potential definition, at B.
  have hdef : (U q) B = ∫⁻ t in Set.Ici (0 : Real),
      ENNReal.ofReal (Real.exp (-q * t)) *
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ B} ∂volume :=
    (hPotential q hq).2 B hB
  -- Assembly.
  have step : (∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
        (c * P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ B}) ∂volume)
      = c * ∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ B} ∂volume := by
    have hpt : ∀ t : Real, ENNReal.ofReal (Real.exp (-q * t)) *
          (c * P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ B})
        = c * (ENNReal.ofReal (Real.exp (-q * t)) *
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ B}) :=
      fun t => mul_left_comm _ _ _
    rw [lintegral_congr hpt]
    exact lintegral_const_mul'' c hoccAE
  calc (∫⁻ x : Real, B.indicator (fun _ => c) x ∂(U q))
      = c * (U q) B := lintegral_indicator_const hB c
    _ = c * ∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ B} ∂volume := by rw [hdef]
    _ = ∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
          (c * P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ B}) ∂volume := step.symm
    _ = ∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
          ∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
            B.indicator (fun _ => c) (Y (Real.toNNReal t) omega) ∂P ∂volume := by
        apply lintegral_congr
        intro t
        rw [hinner c t]
