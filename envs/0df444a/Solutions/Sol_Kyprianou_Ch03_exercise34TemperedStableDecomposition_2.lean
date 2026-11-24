-- Prove2me | solution 2 for Kyprianou.Ch03.exercise34TemperedStableDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:00:07.116138+00:00
-- url     : https://prove2.me/submissions/a879da14-45ec-4c4b-a9dc-3c2d71a48c74

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch03_temperedStableTripletSplitV1
import Theorems.Thm_Kyprianou_Ch03_temperedStableZeroGaussianProcessExistsV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_temperedStableProductDifferenceCharV1
import Theorems.Thm_Kyprianou_Ch03_temperedStableFiniteMassV1
import Theorems.Thm_Kyprianou_Ch03_temperedStableForwardTiltV1
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (cp ap gp cm am gm : ℝ)
    (hcp : 0 < cp) (hcm : 0 < cm)
    (hap : ap < 2) (ham : am < 2)
    (hgp : 0 < gp) (hgm : 0 < gm)
    (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStableSignedMeasure cp ap gp cm am gm) :
    ∃ (OmegaP OmegaM : Type)
      (mP : MeasurableSpace OmegaP) (mM : MeasurableSpace OmegaM),
      letI : MeasurableSpace OmegaP := mP
      letI : MeasurableSpace OmegaM := mM
      ∃ (PP : Measure OmegaP) (PM : Measure OmegaM),
        ∃ (hPP : IsProbabilityMeasure PP) (hPM : IsProbabilityMeasure PM),
        letI : IsProbabilityMeasure PP := hPP
        letI : IsProbabilityMeasure PM := hPM
        ∃ (XP : NNReal → OmegaP → ℝ) (XM : NNReal → OmegaM → ℝ)
          (TP TM : ProbabilityTheory.LevyKhintchineTriple),
          ProbabilityTheory.IsLevyProcess XP PP ∧
          ProbabilityTheory.IsLevyProcess XM PM ∧
          TP.gaussianVariance = 0 ∧ TM.gaussianVariance = 0 ∧
          TP.levyMeasure = temperedStablePositiveMeasure cp ap gp ∧
          TM.levyMeasure = temperedStablePositiveMeasure cm am gm ∧
          (∀ (t : NNReal) (xi : ℝ),
            charFun (PP.map (XP t)) xi =
              Complex.exp (((t : ℝ) : ℂ) *
                Kyprianou.Ch01.levyTripleExponent TP xi)) ∧
          (∀ (t : NNReal) (xi : ℝ),
            charFun (PM.map (XM t)) xi =
              Complex.exp (((t : ℝ) : ℂ) *
                Kyprianou.Ch01.levyTripleExponent TM xi)) ∧
          (∀ t : NNReal,
            Measure.map
              (fun pair : OmegaP × OmegaM => XP t pair.1 - XM t pair.2)
              (PP.prod PM) =
            P.map (X t)) ∧
          (ap < 0 → temperedStablePositiveMeasure cp ap gp Set.univ < ⊤) ∧
          (am < 0 → temperedStablePositiveMeasure cm am gm Set.univ < ⊤) ∧
          (∀ alpha c gamma : ℝ, 0 < c → 0 < gamma →
            temperedStablePositiveMeasure c alpha gamma =
              (temperedStablePositiveMeasure c alpha 0).withDensity
                (fun x => ENNReal.ofReal (Real.exp (-gamma * x)))) := by
  obtain ⟨TP, TM, hP0, hM0, hPν, hMν, hs⟩ :=
    Kyprianou.Ch03.temperedStableTripletSplitV1 T cp ap gp cm am gm hGaussian hMeasure
  obtain ⟨OmegaP, mP, PP, XP, hPP, hXP, hmP, hLKp⟩ :=
    Kyprianou.Ch03.temperedStableZeroGaussianProcessExistsV1 TP hP0
  obtain ⟨OmegaM, mM, PM, XM, hPM, hXM, hmM, hLKm⟩ :=
    Kyprianou.Ch03.temperedStableZeroGaussianProcessExistsV1 TM hM0
  letI := mP
  letI := mM
  letI := hPP
  letI := hPM
  refine ⟨OmegaP, OmegaM, mP, mM, PP, PM, hPP, hPM, XP, XM, TP, TM,
    hXP, hXM, hP0, hM0, hPν, hMν, hLKp, hLKm, ?_, ?_, ?_, ?_⟩
  · intro t
    have hXmeas := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t
    letI : IsProbabilityMeasure (P.map (X t)) := Measure.isProbabilityMeasure_map hXmeas
    letI : IsProbabilityMeasure ((PP.prod PM).map (fun pair : OmegaP × OmegaM => XP t pair.1 - XM t pair.2)) :=
      Measure.isProbabilityMeasure_map ((hmP t).comp measurable_fst |>.sub ((hmM t).comp measurable_snd)).aemeasurable
    apply Measure.ext_of_charFun
    funext xi
    rw [Kyprianou.Ch03.temperedStableProductDifferenceCharV1 PP PM (XP t) (XM t)
      (hmP t) (hmM t), hLKp, hLKm, hLK, hs, mul_add, Complex.exp_add]
  · intro h
    exact Kyprianou.Ch03.temperedStableFiniteMassV1 cp ap gp hcp h hgp
  · intro h
    exact Kyprianou.Ch03.temperedStableFiniteMassV1 cm am gm hcm h hgm
  · intro alpha c gamma hc hg
    exact Kyprianou.Ch03.temperedStableForwardTiltV1 c alpha gamma hc hg
