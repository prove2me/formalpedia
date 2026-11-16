-- Prove2me | solution 1 for Kyprianou.Ch01.brownianRealExpPastFactorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T14:59:12.404214+00:00
-- url     : https://prove2.me/submissions/6879b352-02a0-4617-b39a-c093cc134cfc

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_levyRealExpIncrementStationaryMean
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_indep_naturalSigma
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_measurable_past
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_le_ambient

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Factorisation of an exponential increment against natural-past events. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω)
    (hA : @MeasurableSet Ω (naturalSigma X s) A) :
    (∫ ω in A, Real.exp (theta * X t ω) ∂P) =
      (∫ ω, Real.exp (theta * X (t - s) ω) ∂P) *
        (∫ ω in A, Real.exp (theta * X s ω) ∂P) := by
  let G : Ω → ℝ := fun ω => X t ω - X s ω
  let phi : ℝ → ℝ := fun z => Real.exp (theta * z)
  let F : Ω → ℝ := A.indicator (fun ω => Real.exp (theta * X s ω))
  have hNat : naturalSigma X s ≤ (inferInstance : MeasurableSpace Ω) :=
    Kyprianou.Ch01.naturalSigma_le_ambient X hMeas s
  have hAamb : MeasurableSet A := hNat A hA
  have hsMeas : @Measurable Ω ℝ (naturalSigma X s) inferInstance (X s) :=
    Kyprianou.Ch01.naturalSigma_measurable_past X s s le_rfl
  have hMs : @Measurable Ω ℝ (naturalSigma X s) inferInstance
      (fun ω => Real.exp (theta * X s ω)) := by
    fun_prop (disch := exact hsMeas)
  have hF : @Measurable Ω ℝ (naturalSigma X s) inferInstance F :=
    hMs.indicator hA
  have hG : Measurable G := (hMeas t).sub (hMeas s)
  have hphi : Measurable phi := by dsimp [phi]; fun_prop
  have hind : Indep (MeasurableSpace.comap G inferInstance)
      (naturalSigma X s) P :=
    Kyprianou.Ch01.levyIncrement_indep_naturalSigma
      P X hX.1 hMeas s t hst
  have hIF : IndepFun G F P := by
    apply (IndepFun_iff_Indep G F P).2
    intro U V hU hV
    exact hind U V hU (hF.comap_le V hV)
  have hFamb : Measurable F := hF.mono hNat le_rfl
  have hproduct :
      (∫ ω, phi (G ω) * F ω ∂P) =
        (∫ ω, phi (G ω) ∂P) * (∫ ω, F ω ∂P) := by
    have h := (hIF.comp hphi measurable_id).integral_mul_eq_mul_integral
      (hphi.comp hG).aestronglyMeasurable hFamb.aestronglyMeasurable
    simpa only [Pi.mul_apply, Function.comp_def, id_eq] using h
  have hmean :
      (∫ ω, phi (G ω) ∂P) =
        (∫ ω, phi (X (t - s) ω) ∂P) := by
    simpa only [phi, G] using
      (Kyprianou.Ch01.levyRealExpIncrementStationaryMean
        P X hX.1 hMeas theta s t hst)
  have hfactor (ω : Ω) :
      Real.exp (theta * X t ω) =
        phi (G ω) * Real.exp (theta * X s ω) := by
    dsimp [phi, G]
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (∫ ω in A, Real.exp (theta * X t ω) ∂P) =
      (∫ ω, phi (G ω) * F ω ∂P) := by
        rw [← integral_indicator hAamb]
        apply integral_congr_ae
        filter_upwards [] with ω
        by_cases hw : ω ∈ A
        · simp [F, Set.indicator_of_mem hw, hfactor ω]
        · simp [F, Set.indicator_apply, hw]
    _ = (∫ ω, phi (G ω) ∂P) * (∫ ω, F ω ∂P) := hproduct
    _ = _ := by
      rw [hmean, integral_indicator hAamb]
