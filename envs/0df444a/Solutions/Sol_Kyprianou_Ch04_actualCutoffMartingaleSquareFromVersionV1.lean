-- Prove2me | solution 1 for Kyprianou.Ch04.actualCutoffMartingaleSquareFromVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:47:51.259343+00:00
-- url     : https://prove2.me/submissions/b39b8007-7b05-4f19-9e5d-a7a8f05d0e60

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_cutoffPredictableTerminalCertificateV1
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalMartingaleV1
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalIsometryV1
import Theorems.Thm_Kyprianou_Ch04_completedMeasAECongrV1
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The original physical cutoff integral inherits martingale and square-integrability properties from its predictable version. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ → Measurable[F u] (fun w => N.N w D))
    (e K : ℝ) (hK : 0 ≤ K)
    (hfin : ν {x : ℝ | e < |x| ∧ |x| < 1} < ⊤)
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hBound : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K)
    (L V : NNReal → Ω → ℝ) (hV : IsStronglyPredictable F V)
    (hEq : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V t ω = L t ω)
    (M : NNReal → Ω → ℝ)
    (hM : ∀ t ω, M t ω = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ
      {x : ℝ | e < |x| ∧ |x| < 1}, z.2 * f z.1 (L z.1.toNNReal ω) ∂(N.N ω)) -
      ∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x in {x : ℝ | e < |x| ∧ |x| < 1},
        x * f s (L s.toNNReal ω) ∂ν ∂volume) :
    Martingale M F P ∧ ∀ t, Integrable (fun w => (M t w)^2) P := by
  let B : Set ℝ := {x | e < |x| ∧ |x| < 1}
  let g := fun p : (NNReal × Ω) × ℝ =>
    B.indicator (fun z => z * f (p.1.1 : ℝ) (V p.1.1 p.1.2)) p.2
  let J := fun (t : NNReal) w =>
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
    ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
  have hB : MeasurableSet B := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hG (t : NNReal) := Kyprianou.Ch04.cutoffPredictableTerminalCertificateV1
    P ν F N t e K hK hfin f hf hBound L V hV hEq (M t) (hM t)
  have hAE (t : NNReal) : M t =ᵐ[P] J t := (hG t).2.2.2
  have h := hG 0
  have hm : Martingale J F P :=
    Kyprianou.Ch04.boundedSupportedPredictablePhysicalMartingaleV1 P ν X F hF N
      hFuture hPast B hB hfin g h.1 K hK h.2.1 h.2.2.1
  refine ⟨hm.congr (fun t => ?_) (fun t => (hAE t).symm),fun t => ?_⟩
  · exact (Kyprianou.Ch04.completedMeasAECongrV1 P X F hF t (M t) (J t)
      (hm.stronglyAdapted t).measurable (hAE t)).stronglyMeasurable
  · have hSq := (Kyprianou.Ch04.boundedSupportedPredictablePhysicalIsometryV1
      P ν F N hFuture hPast t B hB hfin g h.1 K h.2.1 h.2.2.1).1
    exact hSq.congr ((hAE t).symm.mono fun w hw => congrArg (fun x : ℝ => x^2) hw)
