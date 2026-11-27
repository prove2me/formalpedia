-- Prove2me | solution 1 for Kyprianou.Ch04.physicalKernelMaximalProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:26:26.78275+00:00
-- url     : https://prove2.me/submissions/2dac7a7b-0fc0-40c8-8db9-545176233cbe

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalMartingaleV1
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalIsometryV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousMartingaleL2MaximalV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousMartingaleCompactBddV1
import Theorems.Thm_Kyprianou_Ch04_compactSquareSupProbabilityV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A bounded marked predictable physical kernel inherits the compact L2
maximal probability bound from its terminal isometry. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ → Measurable[F u] (fun w => N.N w D))
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ) (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ p, ‖g p‖ ≤ C)
    (hs : ∀ p, p.2 ∉ B → g p = 0)
    (T : NNReal) (hT : 0 < T) (q : ℝ)
    (hq : (∫ w, ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ),
      (g ((z.1.toNNReal,w),z.2))^2 ∂referenceIntensity ν ∂P) ≤ q) :
    let J := fun (t : NNReal) w =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    (∀ᵐ w ∂P, ∀ t, Tendsto (fun s => J s w) (nhdsWithin t (Ioi t)) (nhds (J t w))) →
    ∀ δ : ℝ, 0 < δ →
      P {w | ∃ t ≤ T, δ < |J t w|} ≤ ENNReal.ofReal (4*q) / ENNReal.ofReal (δ^2) := by
  intro J hR δ hδ
  have hm : Martingale J F P := Kyprianou.Ch04.boundedSupportedPredictablePhysicalMartingaleV1
    P ν X F hF N hFuture hPast B hB hfin g hg C hC0 hC hs
  obtain ⟨hi,he⟩ := Kyprianou.Ch04.boundedSupportedPredictablePhysicalIsometryV1
    P ν F N hFuture hPast T B hB hfin g hg C hC hs
  have hL2 : Integrable (fun w => (J T w)^2) P := hi
  have hE : (∫ w, (J T w)^2 ∂P) ≤ q := he.trans_le hq
  obtain ⟨hI,hMax⟩ := Kyprianou.Ch04.rightContinuousMartingaleL2MaximalV1
    P F J hm T hT hR hL2
  have hb := Kyprianou.Ch04.rightContinuousMartingaleCompactBddV1
    P F J hm T hT hR hL2
  refine (Kyprianou.Ch04.compactSquareSupProbabilityV1 P J T δ hδ hb hI).trans ?_
  exact ENNReal.div_le_div_right
    (ENNReal.ofReal_le_ofReal (hMax.trans (mul_le_mul_of_nonneg_left hE (by norm_num)))) _
