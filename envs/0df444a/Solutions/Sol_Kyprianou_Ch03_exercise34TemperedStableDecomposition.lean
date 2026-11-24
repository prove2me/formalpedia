-- Prove2me | solution 1 for Kyprianou.Ch03.exercise34TemperedStableDecomposition
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:49:25.418584+00:00
-- url     : https://prove2.me/submissions/b76e07c2-48a2-43b3-9bc7-176b10c5fc57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch03_temperedStableTripletSplitV1
import Theorems.Thm_Kyprianou_Ch03_temperedStableFiniteMassV1
import Theorems.Thm_Kyprianou_Ch03_temperedStableForwardTiltV1
import Theorems.Thm_Kyprianou_Ch03_temperedStableProductDifferenceCharV1
import Theorems.Thm_Kyprianou_Ch01_levyProcess_exists_zeroGaussian
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

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
  obtain ⟨TP, TM, hGP, hGM, hMP, hMM, hExp⟩ :=
    temperedStableTripletSplitV1 T cp ap gp cm am gm hGaussian hMeasure
  obtain ⟨OP, mp, PP, XP, hPP, hXP, hMeasP, hCharP⟩ :=
    Kyprianou.Ch01.levyProcess_exists_zeroGaussian TP hGP
  obtain ⟨OM, mm, PM, XM, hPM, hXM, hMeasM, hCharM⟩ :=
    Kyprianou.Ch01.levyProcess_exists_zeroGaussian TM hGM
  letI : MeasurableSpace OP := mp
  letI : MeasurableSpace OM := mm
  letI : IsProbabilityMeasure PP := hPP
  letI : IsProbabilityMeasure PM := hPM
  refine ⟨OP, OM, mp, mm, PP, PM, hPP, hPM, XP, XM, TP, TM,
    hXP, hXM, hGP, hGM, hMP, hMM, hCharP, hCharM, ?_,
    fun ha => temperedStableFiniteMassV1 cp ap gp hcp ha hgp,
    fun ha => temperedStableFiniteMassV1 cm am gm hcm ha hgm, ?_⟩
  · intro t
    letI := Measure.isProbabilityMeasure_map
      (μ := P) (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t)
    letI := Measure.isProbabilityMeasure_map (μ := PP.prod PM)
      (((hMeasP t).comp measurable_fst).sub ((hMeasM t).comp measurable_snd)).aemeasurable
    apply Measure.ext_of_charFun
    funext xi
    rw [temperedStableProductDifferenceCharV1 PP PM (XP t) (XM t)
      (hMeasP t) (hMeasM t), hCharP, hCharM, hLK, hExp, mul_add, Complex.exp_add]
  · intro alpha c gamma hc hg
    exact temperedStableForwardTiltV1 c alpha gamma hc hg
