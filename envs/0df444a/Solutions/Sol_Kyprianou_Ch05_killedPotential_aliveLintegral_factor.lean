-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_aliveLintegral_factor
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T09:56:38.413395+00:00
-- url     : https://prove2.me/submissions/4ef173f7-357c-40df-a79a-d0203976f7c3

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
  ∀ (t : Real), 0 ≤ t → ∀ theta : Real, 0 ≤ theta →
      (∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
        ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P) =
      (∫⁻ omega, ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P) *
        ENNReal.ofReal (Real.exp (-eta * t)) := by
  intro t ht theta htheta
  -- AE measurability of each `Y s`, from stationary increments + start at zero.
  have hYAEMeas : ∀ s : NNReal, AEMeasurable (Y s) P := by
    intro s
    have h := (hKilled.1.1.stationary_increments 0 s).1
    have hinc : ProbabilityTheory.increment Y 0 (0 + s) = Y s := by
      funext ω
      simp [ProbabilityTheory.increment, hKilled.1.1.start_zero]
    rwa [hinc] at h
  have hdeath : Measurable death := hKilled.2.2.1
  have hA : MeasurableSet {omega : Omega |
      (Real.toNNReal t : WithTop NNReal) < death omega} :=
    hdeath measurableSet_Ioi
  have hg : AEMeasurable (fun omega : Omega =>
      ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega))) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable
        ((measurable_const_mul (-theta)).comp_aemeasurable
          (hYAEMeas (Real.toNNReal t))))
  have hf : Measurable ({omega : Omega |
      (Real.toNNReal t : WithTop NNReal) < death omega}.indicator 1) :=
    (measurable_const (a := (1 : ENNReal))).indicator hA
  -- Independence of the two factors, from `Indep` of the death/path comaps.
  have hF : Measurable ((Set.Ioi (Real.toNNReal t : WithTop NNReal)).indicator
      (1 : WithTop NNReal → ENNReal)) :=
    (measurable_const (a := (1 : ENNReal))).indicator measurableSet_Ioi
  have hG : Measurable (fun p : NNReal → Real =>
      ENNReal.ofReal (Real.exp (-theta * p (Real.toNNReal t)))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_pi_apply _).const_mul _))
  have hcomp : ({omega : Omega |
        (Real.toNNReal t : WithTop NNReal) < death omega}.indicator
          (1 : Omega → ENNReal))
      = (Set.Ioi (Real.toNNReal t : WithTop NNReal)).indicator 1 ∘ death := by
    funext omega
    by_cases hω : (Real.toNNReal t : WithTop NNReal) < death omega
    · have hm1 : omega ∈ {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega} := hω
      have hm2 : death omega ∈ Set.Ioi (Real.toNNReal t : WithTop NNReal) := hω
      rw [Set.indicator_of_mem hm1, Function.comp_apply,
        Set.indicator_of_mem hm2]
      simp only [_root_.Pi.one_apply]
    · have hm1 : omega ∉ {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega} := hω
      have hm2 : death omega ∉ Set.Ioi (Real.toNNReal t : WithTop NNReal) :=
        fun h => hω (Set.mem_Ioi.mp h)
      rw [Set.indicator_of_notMem hm1, Function.comp_apply,
        Set.indicator_of_notMem hm2]
  have hIndepFun : ProbabilityTheory.IndepFun
      ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}.indicator
        (1 : Omega → ENNReal))
      (fun omega : Omega =>
        ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega))) P := by
    have h0 : ProbabilityTheory.IndepFun death
        (fun omega : Omega => fun s : NNReal => Y s omega) P :=
      hKilled.2.2.2.2.2
    have hc := h0.comp hF hG
    rwa [← hcomp] at hc
  have hfact := ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    hf.aemeasurable hg hIndepFun
  have hrestr : (∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
        ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P)
      = ∫⁻ omega, ({omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega}.indicator 1) omega *
          ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P := by
    rw [← MeasureTheory.lintegral_indicator hA]
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards with omega
    by_cases hω : omega ∈ {omega : Omega |
        (Real.toNNReal t : WithTop NNReal) < death omega}
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]; simp
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]; simp
  have hsurv := hKilled.2.2.2.2.1 (Real.toNNReal t)
  rw [Real.coe_toNNReal t ht] at hsurv
  rw [hrestr, hfact, MeasureTheory.lintegral_indicator_one hA, hsurv, mul_comm]
