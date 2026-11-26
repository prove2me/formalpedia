-- Prove2me | solution 1 for Kyprianou.Ch04.weightedDisjointGridBoxCrossZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:05:34.51315+00:00
-- url     : https://prove2.me/submissions/781ab3a7-f2b9-49c8-afdd-f01f3ccc1c6b

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_orderedWeightedPoissonBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_sameTimeWeightedPoissonBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Weighted cells in a disjoint time-mark grid have zero cross moment. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ → Measurable[F u] (fun ω => N.N ω B))
    (a b c d : NNReal) (hab : a ≤ b) (hcd : c ≤ d)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ≠ ⊤)
    (hBfin : referenceIntensity ν (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ≠ ⊤)
    (hGrid : b ≤ c ∨ d ≤ a ∨ (a = c ∧ b = d ∧ Disjoint A B))
    (H K : Ω → ℝ) (hH : StronglyMeasurable[F a] H) (hK : StronglyMeasurable[F c] K)
    (hH2 : Integrable (fun ω => (H ω)^2) P)
    (hK2 : Integrable (fun ω => (K ω)^2) P)
    (hE2 : Integrable (fun ω => (H ω *
      N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω)^2) P)
    (hL2 : Integrable (fun ω => (K ω *
      N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω)^2) P) :
    ∫ ω, (H ω * N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω) *
      (K ω * N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω) ∂P = 0 := by
  rcases hGrid with h | h | ⟨ha, hb, hd⟩
  · exact Kyprianou.Ch04.orderedWeightedPoissonBoxCrossZero
      P ν F N hFuture hPast a b c d hab h hcd A B hA hB hBfin H K hH hK hK2 hE2 hL2
  · have hz := Kyprianou.Ch04.orderedWeightedPoissonBoxCrossZero
      P ν F N hFuture hPast c d a b hcd h hab B A hB hA hAfin K H hK hH hH2 hL2 hE2
    simpa only [mul_comm] using hz
  · subst c
    subst d
    have hWi := Kyprianou.Ch04.integrableProductOfSquareIntegrable P H K
      (hH.mono (F.le' a)).aestronglyMeasurable (hK.mono (F.le' a)).aestronglyMeasurable
      hH2 hK2
    have hz := Kyprianou.Ch04.sameTimeWeightedPoissonBoxCrossZero P ν F N hFuture a b
      hab A B hA hB hd hAfin hBfin (fun ω => H ω * K ω) (hH.mul hK) hWi
    rw [← hz]
    apply integral_congr_ae
    filter_upwards [] with ω
    ring
