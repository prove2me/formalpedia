-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_filtered_avram_model
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:57:24.435109+00:00
-- url     : https://prove2.me/submissions/de4bd38d-b3d3-45d8-86a6-42ac6f9478bb

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_allpath_cadlag_version
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_no_positive_jumps
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
import Theorems.Thm_AvramDividend_Classical_avram_e0_natural_filtration_from_leanlevy_increment

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem version_increments
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (G Y : ℝ≥0 → Ω → ℝ) (hG : IsLevyProcess G P)
    (hYmeas : ∀ t, Measurable (Y t)) (heq : ∀ᵐ ω ∂P, ∀ t, Y t ω = G t ω) :
    HasIndependentIncrements Y P ∧
      ∀ s t, s ≤ t → IdentDistrib (fun ω => Y t ω - Y s ω) (Y (t - s)) P P := by
  have hInc (s t : ℝ≥0) : (fun ω => Y t ω - Y s ω) =ᵐ[P]
      (fun ω => G t ω - G s ω) := heq.mono (fun _ h => by simp only [h])
  constructor
  · intro n ts hmono
    exact (iIndepFun_congr (fun k : Fin n => hInc (ts k.castSucc) (ts k.succ))).mpr
      (hG.indep_increments n ts hmono)
  · intro s t hst
    have h := hG.stationary_increments s (t - s)
    rw [add_tsub_cancel_of_le hst] at h
    change IdentDistrib (fun ω => G t ω - G s ω)
      (fun ω => G (t - s) ω - G 0 ω) P P at h
    have hStart : (fun ω => G (t - s) ω - G 0 ω) = G (t - s) := by
      funext ω
      rw [congrFun hG.start_zero ω, sub_zero]
    rw [hStart] at h
    exact (IdentDistrib.of_ae_eq ((hYmeas t).sub (hYmeas s)).aemeasurable (hInc s t)).trans
      (h.trans (IdentDistrib.of_ae_eq (hYmeas (t - s)).aemeasurable
        (heq.mono (fun _ hω => hω (t - s)))).symm)

private theorem triplet_convention (c σ : ℝ) (ν : Measure ℝ) (hneg : ν (Ici 0) = 0)
    (β : ℝ) :
    AvramDividend.Classical.laplaceExponent c σ ν β = tripletLaplace (-c) σ ν β := by
  have hν : ∀ᵐ y ∂ν, y ∈ Iio (0 : ℝ) := by
    have hComplement : {y : ℝ | ¬y ∈ Iio (0 : ℝ)} = Ici 0 := by
      ext y
      simp only [mem_setOf_eq, mem_Iio, mem_Ici, not_lt]
    rw [ae_iff, hComplement]
    exact hneg
  rw [AvramDividend.Classical.laplaceExponent, tripletLaplace, neg_neg,
    Measure.restrict_eq_self_of_ae_mem hν]
  congr 1
  apply integral_congr_ae
  filter_upwards [hν] with y hny
  by_cases hy : -1 < y
  · have hyIoo : y ∈ Ioo (-1 : ℝ) 1 :=
      ⟨hy, (show y < 0 from hny).trans zero_lt_one⟩
    simp [hy, indicator_of_mem hyIoo]
  · rw [if_neg hy, indicator_of_notMem (fun h : y ∈ Ioo (-1 : ℝ) 1 => hy h.1)]
    simp

theorem solution
    (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ∃ (F : Filtration ℝ≥0 mΩ)
      (A : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      (∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω) ∧
      (∀ β : ℝ, 0 ≤ β → A.ψ β = ψ β) := by
  classical
  have hM (t : ℝ≥0) : AEMeasurable (D.X t) P := by
    have hi := (D.levy.stationary_increments 0 t).aemeasurable_snd
    change AEMeasurable (fun ω => D.X t ω - D.X 0 ω) P at hi
    simpa only [D.levy.start_zero, sub_zero] using hi
  obtain ⟨Y, heq, hYmeas, hY0, hCad, hJump⟩ :=
    source_result81_allpath_cadlag_version Ω P D.X hM D.levy.start_zero
      D.levy.cadlag_ae (source_result81_no_positive_jumps Ω P D)
  obtain ⟨hInd, hStationary⟩ := version_increments P D.X Y D.levy hYmeas heq
  have hBridge := triplet_convention D.triplet.drift D.gaussianCoefficient
    D.triplet.levyMeasure D.negativeJumps
  have hMomentEq (t : ℝ≥0) (β : ℝ) :
      (fun ω => Real.exp (β * Y t ω)) =ᵐ[P] (fun ω => Real.exp (β * D.X t ω)) :=
    heq.mono (fun _ h => by simp only [h])
  let hSm (t : ℝ≥0) := (hYmeas t).stronglyMeasurable
  let F := Filtration.natural Y hSm
  obtain ⟨hAdapt, hPast⟩ :=
    AvramDividend.Classical.avram_e0_natural_filtration_from_leanlevy_increment
      Y hSm hY0 hInd
  let A : AvramDividend.Classical.SpectrallyNegativeLevy P F :=
    { X := Y
      c := D.triplet.drift
      σ := D.gaussianCoefficient
      ν := D.triplet.levyMeasure
      isProbability := inferInstance
      σ_nonneg := D.gaussianNonnegative
      ν_Ici := D.negativeJumps
      ν_integrable := D.triplet.levyMeasure_isLevyMeasure.2
      X_zero := fun ω => congrFun hY0 ω
      rightCont := fun ω t => (hCad ω t).1
      leftLim := fun ω t _ => (hCad ω t).2
      noPosJumps := hJump
      adapted := hAdapt.adapted
      indepIncrements := hPast
      stationaryIncrements := hStationary
      laplace := fun t β hβ => by
        obtain ⟨hInt, hIntEq⟩ := source_result81_law_positive_mgf Ω P D t β hβ
        exact ⟨hInt.congr (hMomentEq t β).symm, by
          rw [integral_congr_ae (hMomentEq t β), hIntEq, hBridge]⟩ }
  refine ⟨F, A, heq, ?_⟩
  intro β hβ
  have h := (hψ β 1 hβ zero_lt_one).2
  change ψ β = Real.log (∫ ω, Real.exp (β * D.X 1 ω) ∂P) / ((1 : ℝ≥0) : ℝ) at h
  rw [(source_result81_law_positive_mgf Ω P D 1 β hβ).2, Real.log_exp] at h
  simpa only [AvramDividend.Classical.SpectrallyNegativeLevy.ψ, A, hBridge, NNReal.coe_one,
    one_mul, div_one] using h.symm
