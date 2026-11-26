-- Prove2me | solution 1 for Kyprianou.Ch04.cutoffPredictableTerminalCertificateV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:37:39.525567+00:00
-- url     : https://prove2.me/submissions/53eb65b1-6dd3-4bfb-b63e-63b78b704ed1

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableContinuousTimeStateWeightV1
import Theorems.Thm_Kyprianou_Ch04_boundedPredictableMarkMaskV1
import Theorems.Thm_Kyprianou_Ch04_poissonZeroTimeSliceV1
import Theorems.Thm_Kyprianou_Ch04_physicalMarkIndicatorWindowIntegralV1
import Theorems.Thm_Kyprianou_Ch04_physicalWindowPositiveTimeCongrV1
import Theorems.Thm_Kyprianou_Ch04_referenceIntensityClosedWindowProductV1
import Theorems.Thm_Kyprianou_Ch04_predictablePhysicalKernelSectionV1
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedWindowIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A cutoff terminal variable has a bounded predictable marked kernel certificate. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (T : NNReal) (e K : ℝ) (hK : 0 ≤ K)
    (hfin : ν {x : ℝ | e < |x| ∧ |x| < 1} < ⊤)
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hBound : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K)
    (L V : NNReal → Ω → ℝ) (hV : IsStronglyPredictable F V)
    (hEq : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V t ω = L t ω)
    (M : Ω → ℝ)
    (hM : ∀ ω, M ω = (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ
      {x : ℝ | e < |x| ∧ |x| < 1}, z.2 * f z.1 (L z.1.toNNReal ω) ∂(N.N ω)) -
      ∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x in {x : ℝ | e < |x| ∧ |x| < 1},
        x * f s (L s.toNNReal ω) ∂ν ∂volume) :
    let B := {x : ℝ | e < |x| ∧ |x| < 1}
    let g := fun p : (NNReal × Ω) × ℝ =>
      B.indicator (fun z => z * f (p.1.1 : ℝ) (V p.1.1 p.1.2)) p.2
    let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
    Measurable[F.predictable.prod inferInstance] g ∧ (∀ p, ‖g p‖ ≤ K) ∧
      (∀ p, p.2 ∉ B → g p = 0) ∧ ∀ᵐ ω ∂P, M ω =
      ((∫ z in U, g ((z.1.toNNReal,ω),z.2) ∂(N.N ω)) -
        ∫ z in U, g ((z.1.toNNReal,ω),z.2) ∂referenceIntensity ν) := by
  let B : Set ℝ := {x | e < |x| ∧ |x| < 1}
  let W (p : NNReal × Ω) := f (p.1 : ℝ) (V p.1 p.2)
  let g := fun p : (NNReal × Ω) × ℝ => B.indicator (fun z => z * W p.1) p.2
  let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
  have hB : MeasurableSet B := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hW := Kyprianou.Ch04.predictableContinuousTimeStateWeightV1 F V hV f hf
  have hG := Kyprianou.Ch04.boundedPredictableMarkMaskV1 F B hB
    (fun z hz => hz.2.le) W hW K hK (fun p => hBound _ _ p.1.coe_nonneg)
  refine ⟨hG.1,hG.2.1,hG.2.2,?_⟩
  have hIntensity := Kyprianou.Ch04.closedTimeBandIntensityFinite ν T B hfin
  have hProd := Kyprianou.Ch04.referenceIntensityClosedWindowProductV1 ν T
    (univ : Set ℝ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hProd
  filter_upwards [hEq,(Kyprianou.Ch04.poissonZeroTimeSliceV1 P ν N).2] with ω hω hz
  have hw (s : ℝ) (hs : 0 < s) : W (s.toNNReal,ω) = f s (L s.toNNReal ω) := by
    have ht : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs
    simp only [W,Real.coe_toNNReal s hs.le,hω _ ht]
  have hRaw := Kyprianou.Ch04.physicalWindowPositiveTimeCongrV1 (N.N ω) T B hB hz
    (fun z => z.2 * f z.1 (L z.1.toNNReal ω)) (fun z => z.2 * W (z.1.toNNReal,ω))
    (fun z hs _ _ => by rw [hw z.1 hs])
  have hMask := Kyprianou.Ch04.physicalMarkIndicatorWindowIntegralV1 (N.N ω) T B hB
    (fun z => z.2 * W (z.1.toNNReal,ω))
  have hInt := (Kyprianou.Ch04.boundedSupportedWindowIntegrableV1
    (referenceIntensity ν) T B hB hIntensity.lt_top _
    (Kyprianou.Ch04.predictablePhysicalKernelSectionV1 F g hG.1 ω)
    K (fun z => hG.2.1 _) (fun z hz => hG.2.2 _ hz)).1
  rw [IntegrableOn,hProd] at hInt
  have hComp : (∫ z in U, g ((z.1.toNNReal,ω),z.2) ∂referenceIntensity ν) =
      ∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x in B, x * f s (L s.toNNReal ω) ∂ν ∂volume := by
    change (∫ z, g ((z.1.toNNReal,ω),z.2) ∂(referenceIntensity ν).restrict U) = _
    rw [show U = Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ) from rfl,hProd,
      integral_prod _ hInt]
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change (∫ x, B.indicator (fun z => z * W (s.toNNReal,ω)) x ∂ν) = _
    rw [integral_indicator hB,hw s hs.1]
  rw [hM ω]
  change ((∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ B,
    z.2 * f z.1 (L z.1.toNNReal ω) ∂(N.N ω)) -
      ∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x in B, x * f s (L s.toNNReal ω) ∂ν ∂volume) = _
  rw [hRaw,← hMask,← hComp]
