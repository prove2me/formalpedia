-- Prove2me | solution 1 for Kyprianou.Ch04.orderedWeightedPoissonBoxCrossZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:53:39.3438+00:00
-- url     : https://prove2.me/submissions/92767a79-4630-4bd9-83f2-897ee6cf4cf1

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_pastWeightCompensatedFutureBoxCentered
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Adapted past counts make two ordered weighted Poisson boxes orthogonal. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ → Measurable[F u] (fun ω => N.N ω B))
    (a b c d : NNReal) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hFin : referenceIntensity ν (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ≠ ⊤)
    (H K : Ω → ℝ) (hH : StronglyMeasurable[F a] H) (hK : StronglyMeasurable[F c] K)
    (hK2 : Integrable (fun ω => (K ω)^2) P)
    (hE2 : Integrable (fun ω => (H ω *
      N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω)^2) P)
    (hL2 : Integrable (fun ω => (K ω *
      N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω)^2) P) :
    ∫ ω, (H ω * N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω) *
      (K ω * N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω) ∂P = 0 := by
  let E := fun ω => H ω * N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω
  let L := fun ω => K ω * N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω
  have hsub : Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A ⊆
      Set.Icc (0 : ℝ) (c : ℝ) ×ˢ Set.univ := by
    intro z hz
    exact ⟨⟨(NNReal.coe_nonneg a).trans hz.1.1.le,
      hz.1.2.trans (by exact_mod_cast hbc)⟩, Set.mem_univ _⟩
  have hcount := hPast c _ (measurableSet_Ioc.prod hA) hsub
  have hE : StronglyMeasurable[F c] E :=
    (hH.mono (F.mono (hab.trans hbc))).mul
      ((ENNReal.measurable_toReal.comp hcount).sub_const _).stronglyMeasurable
  have hLm : AEStronglyMeasurable L P :=
    ((hK.mono (F.le' c)).mul
      ((ENNReal.measurable_toReal.comp
        (N.measurable_eval (measurableSet_Ioc.prod hB))).sub_const _).stronglyMeasurable
    ).aestronglyMeasurable
  have hG := Kyprianou.Ch04.integrableProductOfSquareIntegrable P E K
    (hE.mono (F.le' c)).aestronglyMeasurable
    (hK.mono (F.le' c)).aestronglyMeasurable hE2 hK2
  have hEL := Kyprianou.Ch04.integrableProductOfSquareIntegrable P E L
    (hE.mono (F.le' c)).aestronglyMeasurable hLm hE2 hL2
  have hp : Integrable (fun ω => (E ω * K ω) *
      N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω) P := by
    convert hEL using 1
    ext ω
    simp only [L, mul_assoc]
  have hz := Kyprianou.Ch04.pastWeightCompensatedFutureBoxCentered
    P ν F N hFuture c d hcd B hB hFin (fun ω => E ω * K ω)
    (hE.mul hK) hG hp
  simpa only [E, mul_assoc] using hz
