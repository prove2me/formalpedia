-- Prove2me | solution 1 for Kyprianou.Ch01.characteristicExponentialConditionalExpectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:51:25.923539+00:00
-- url     : https://prove2.me/submissions/6f326869-898e-4f9a-a33b-f6195002be30

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_indep_naturalSigma
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_measurable_past
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_le_ambient
import Theorems.Thm_Kyprianou_Ch01_characteristicExponential_increment_mean_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ t : ℝ≥0,
      charFun (P.map (X t)) theta =
        Complex.exp (-((t : ℝ) : ℂ) * Psi)) :
    let M : ℝ≥0 → Ω → ℂ :=
      fun t ω =>
        Complex.exp (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
          ((t : ℝ) : ℂ) * Psi)
    ∀ (s t : ℝ≥0), s ≤ t →
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
          (∫ ω in A, M t ω ∂P) =
            (∫ ω in A, M s ω ∂P) := by
  dsimp
  intro s t hst A hA
  let M : ℝ≥0 → Ω → ℂ := fun u ω =>
    Complex.exp (Complex.I * (theta : ℂ) * (X u ω : ℂ) +
      ((u : ℝ) : ℂ) * Psi)
  let G : Ω → ℝ := fun ω => X t ω - X s ω
  let phi : ℝ → ℂ := fun z =>
    Complex.exp (Complex.I * (theta : ℂ) * (z : ℂ) +
      (((t - s : ℝ≥0) : ℝ) : ℂ) * Psi)
  let F : Ω → ℂ := A.indicator (M s)
  change (∫ ω in A, M t ω ∂P) = (∫ ω in A, M s ω ∂P)
  have hNat : naturalSigma X s ≤ (inferInstance : MeasurableSpace Ω) :=
    Kyprianou.Ch01.naturalSigma_le_ambient X hmeas s
  have hAamb : MeasurableSet A := hNat A hA
  have hsMeas : @Measurable Ω ℝ (naturalSigma X s) inferInstance (X s) :=
    Kyprianou.Ch01.naturalSigma_measurable_past X s s le_rfl
  have hMC : @Measurable Ω ℂ (naturalSigma X s) inferInstance (M s) := by
    change @Measurable Ω ℂ (naturalSigma X s) inferInstance
      (fun ω => Complex.exp (Complex.I * (theta : ℂ) * (X s ω : ℂ) +
        ((s : ℝ) : ℂ) * Psi))
    fun_prop (disch := exact hsMeas)
  have hF : @Measurable Ω ℂ (naturalSigma X s) inferInstance F :=
    hMC.indicator hA
  have hG : Measurable G := (hmeas t).sub (hmeas s)
  have hphi : Measurable phi := by
    dsimp [phi]
    fun_prop
  have hind : Indep (MeasurableSpace.comap G inferInstance)
      (naturalSigma X s) P :=
    Kyprianou.Ch01.levyIncrement_indep_naturalSigma
      P X hX hmeas s t hst
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
  have hmean : (∫ ω, phi (G ω) ∂P) = 1 := by
    simpa [phi, G, Complex.ofReal_sub] using
      (Kyprianou.Ch01.characteristicExponential_increment_mean_one
        P X hX hmeas theta Psi hchar s t hst)
  have hfactor (ω : Ω) : M t ω = phi (G ω) * M s ω := by
    dsimp [M, phi, G]
    rw [← Complex.exp_add]
    congr 1
    simp only [NNReal.coe_sub hst, Complex.ofReal_sub]
    ring
  calc
    (∫ ω in A, M t ω ∂P) =
      (∫ ω, phi (G ω) * F ω ∂P) := by
        rw [← integral_indicator hAamb]
        apply integral_congr_ae
        filter_upwards [] with ω
        by_cases hw : ω ∈ A
        · simp [F, Set.indicator_of_mem hw, hfactor ω]
        · simp [F, Set.indicator_apply, hw]
    _ = (∫ ω, phi (G ω) ∂P) * (∫ ω, F ω ∂P) := hproduct
    _ = ∫ ω in A, M s ω ∂P := by
      rw [hmean, one_mul]
      exact integral_indicator hAamb
