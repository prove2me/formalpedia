-- Prove2me | solution 1 for Kyprianou.Ch04.finitePredictableTailRectangleIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:45:30.972056+00:00
-- url     : https://prove2.me/submissions/5f9b6d8d-e892-43c6-b4f6-83b709de246b

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableTailRectangleCovariance
import Theorems.Thm_Kyprianou_Ch04_finiteFamilyCovarianceExpansion
import Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorSquareIntegral
import Theorems.Thm_Kyprianou_Ch04_finiteCoefficientCrossMomentIntegral
import Theorems.Thm_Kyprianou_Ch04_predictableWeightedPoissonBoxL2
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Isometry for finite predictable tail rectangles with arbitrary overlaps. -/
theorem solution
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (s : Finset ι) (a : ι → NNReal) (t : NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hat : ∀ i ∈ s, a i ≤ t)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    let S := fun i => Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i
    let Z := fun ω => ∑ i ∈ s, H i ω * N.compensated (S i) ω
    let K := fun ω z => ∑ i ∈ s, (S i).indicator (fun _ => H i ω) z
    MemLp Z 2 P ∧
      (∫ ω, (Z ω)^2 ∂P) =
      ∫ ω, (∫ z, (K ω z)^2 ∂referenceIntensity ν) ∂P := by
  dsimp only
  let S := fun i => Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i
  let Z := fun i ω => H i ω * N.compensated (S i) ω
  let c := fun i j => (referenceIntensity ν (S i ∩ S j)).toReal
  have hS (i : ι) (hi : i ∈ s) : MeasurableSet (S i) :=
    measurableSet_Ioc.prod (hB i hi)
  have hHm (i : ι) (hi : i ∈ s) : AEStronglyMeasurable (H i) P :=
    ((hH i hi).mono (F.le' (a i))).aestronglyMeasurable
  have hZm (i : ι) (hi : i ∈ s) : AEStronglyMeasurable (Z i) P :=
    (hHm i hi).mul ((ENNReal.measurable_toReal.comp
      (N.measurable_eval (hS i hi))).sub_const _).aestronglyMeasurable
  have hZ2 (i : ι) (hi : i ∈ s) :=
    (Kyprianou.Ch04.predictableWeightedPoissonBoxL2
      P ν F N hFuture (a i) t (hat i hi) (B i) (hB i hi)
      (hFin i hi) (H i) (hH i hi) (hH2 i hi)).1
  have hLp (i : ι) (hi : i ∈ s) : MemLp (Z i) 2 P :=
    (memLp_two_iff_integrable_sq (hZm i hi)).2 (hZ2 i hi)
  have hp (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :=
    Kyprianou.Ch04.integrableProductOfSquareIntegrable P (Z i) (Z j)
      (hZm i hi) (hZm j hj) (hZ2 i hi) (hZ2 j hj)
  have hInter (i j : ι) : S i ∩ S j =
      Set.Ioc (↑(max (a i) (a j)) : ℝ) (t : ℝ) ×ˢ (B i ∩ B j) := by
    ext z
    simp only [S, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, NNReal.coe_max, max_lt_iff]
    tauto
  have hc (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      (∫ ω, Z i ω * Z j ω ∂P) =
        (∫ ω, H i ω * H j ω ∂P) * c i j := by
    change (∫ ω, Z i ω * Z j ω ∂P) = _ * (referenceIntensity ν (S i ∩ S j)).toReal
    rw [hInter]
    exact Kyprianou.Ch04.predictableTailRectangleCovariance
      P ν F N hFuture hPast (a i) (a j) t (hat i hi) (hat j hj)
      (B i) (B j) (hB i hi) (hB j hj) (hFin i hi) (hFin j hj)
      (H i) (H j) (hH i hi) (hH j hj) (hH2 i hi) (hH2 j hj)
  change MemLp (fun ω => ∑ i ∈ s, Z i ω) 2 P ∧
    (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) =
      ∫ ω, (∫ z, (∑ i ∈ s, (S i).indicator (fun _ => H i ω) z)^2 ∂referenceIntensity ν) ∂P
  refine ⟨memLp_finsetSum s hLp, ?_⟩
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω, Z i ω * Z j ω ∂P :=
      Kyprianou.Ch04.finiteFamilyCovarianceExpansion P s Z hp
    _ = ∑ i ∈ s, ∑ j ∈ s, (∫ ω, H i ω * H j ω ∂P) * c i j :=
      Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (hc i hi))
    _ = ∫ ω, ∑ i ∈ s, ∑ j ∈ s, (H i ω * H j ω) * c i j ∂P :=
      (Kyprianou.Ch04.finiteCoefficientCrossMomentIntegral P s H c hHm hH2).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (Kyprianou.Ch04.finiteWeightedIndicatorSquareIntegral
        (referenceIntensity ν) s S (fun i => H i ω) hS hFin).symm
