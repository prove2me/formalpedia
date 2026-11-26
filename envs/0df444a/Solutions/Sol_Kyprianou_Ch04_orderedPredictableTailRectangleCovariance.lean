-- Prove2me | solution 1 for Kyprianou.Ch04.orderedPredictableTailRectangleCovariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:48.129789+00:00
-- url     : https://prove2.me/submissions/ac81416a-5ff6-4650-9a34-fdf03fbc1d66

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_compensatedTimeBoxSplitAE
import Theorems.Thm_Kyprianou_Ch04_sameTimeWeightedPoissonBoxCovariance
import Theorems.Thm_Kyprianou_Ch04_orderedWeightedPoissonBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_predictableWeightedPoissonBoxL2
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Predictable tail-box covariance for ordered left endpoints. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (a b t : NNReal) (hab : a ≤ b) (hbt : b ≤ t)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAf : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤)
    (hBf : referenceIntensity ν (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (H K : Ω → ℝ) (hH : StronglyMeasurable[F a] H) (hK : StronglyMeasurable[F b] K)
    (hH2 : Integrable (fun ω => (H ω)^2) P)
    (hK2 : Integrable (fun ω => (K ω)^2) P) :
    (∫ ω, (H ω * N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ω) *
      (K ω * N.compensated (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ B) ω) ∂P) =
      (∫ ω, H ω * K ω ∂P) *
      (referenceIntensity ν (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ (A ∩ B))).toReal := by
  let U := Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A
  let V := Set.Ioc (b : ℝ) (t : ℝ) ×ˢ A
  let W := Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A
  let D := Set.Ioc (b : ℝ) (t : ℝ) ×ˢ B
  let X := fun ω => H ω * N.compensated U ω
  let Y := fun ω => H ω * N.compensated V ω
  let Z := fun ω => K ω * N.compensated D ω
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbt' : (b : ℝ) ≤ t := by exact_mod_cast hbt
  have hU : U ⊆ W := fun z hz => ⟨⟨hz.1.1, hz.1.2.trans hbt'⟩, hz.2⟩
  have hV : V ⊆ W := fun z hz => ⟨⟨hab'.trans_lt hz.1.1, hz.1.2⟩, hz.2⟩
  have hUf := ne_top_of_le_ne_top hAf (measure_mono hU)
  have hVf := ne_top_of_le_ne_top hAf (measure_mono hV)
  have hHb := hH.mono (F.mono hab)
  have hX2 := (Kyprianou.Ch04.predictableWeightedPoissonBoxL2
    P ν F N hFuture a b hab A hA hUf H hH hH2).1
  have hY2 := (Kyprianou.Ch04.predictableWeightedPoissonBoxL2
    P ν F N hFuture b t hbt A hA hVf H hHb hH2).1
  have hZ2 := (Kyprianou.Ch04.predictableWeightedPoissonBoxL2
    P ν F N hFuture b t hbt B hB hBf K hK hK2).1
  have hm (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) (G : Ω → ℝ)
      (hG : AEStronglyMeasurable G P) :
      AEStronglyMeasurable (fun ω => G ω * N.compensated S ω) P :=
    hG.mul ((ENNReal.measurable_toReal.comp
      (N.measurable_eval hS)).sub_const _).aestronglyMeasurable
  have hHm := (hH.mono (F.le' a)).aestronglyMeasurable (μ := P)
  have hKm := (hK.mono (F.le' b)).aestronglyMeasurable (μ := P)
  have hZm := hm D (measurableSet_Ioc.prod hB) K hKm
  have hXZ := Kyprianou.Ch04.integrableProductOfSquareIntegrable P X Z
    (hm U (measurableSet_Ioc.prod hA) H hHm) hZm hX2 hZ2
  have hYZ := Kyprianou.Ch04.integrableProductOfSquareIntegrable P Y Z
    (hm V (measurableSet_Ioc.prod hA) H hHm) hZm hY2 hZ2
  have hzero := Kyprianou.Ch04.orderedWeightedPoissonBoxCrossZero
    P ν F N hFuture hPast a b b t hab le_rfl hbt A B hA hB hBf H K
    hH hK hK2 hX2 hZ2
  have hHK := Kyprianou.Ch04.integrableProductOfSquareIntegrable P H K
    hHm hKm hH2 hK2
  have hcov := Kyprianou.Ch04.sameTimeWeightedPoissonBoxCovariance
    P ν F N hFuture b t hbt A B hA hB hVf hBf
    (fun ω => H ω * K ω) (hHb.mul hK) hHK
  have hsplit := Kyprianou.Ch04.compensatedTimeBoxSplitAE
    P ν N a b t hab hbt A hA hAf
  calc
    _ = ∫ ω, X ω * Z ω + Y ω * Z ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hsplit] with ω hω
      simp only [X, Y, Z, U, V, D]
      rw [hω]
      ring
    _ = (∫ ω, X ω * Z ω ∂P) + ∫ ω, Y ω * Z ω ∂P :=
      integral_add hXZ hYZ
    _ = _ := by
      rw [show (∫ ω, X ω * Z ω ∂P) = 0 from hzero, zero_add]
      convert hcov using 1
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [Y, Z, V, D]
      ring
