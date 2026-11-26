-- Prove2me | solution 1 for Kyprianou.Ch04.finitePredictableTailBoxPhysicalIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:53:15.316618+00:00
-- url     : https://prove2.me/submissions/4d2ad9ab-0d65-4ab1-ad89-ad4bd0b7a6e8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxSecondMoment
import Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorExpectedSquareIntegral
import Theorems.Thm_Kyprianou_Ch04_finitePoissonIndicatorIntegralAE
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Physical compensated integral isometry for finite predictable tail boxes with overlaps. -/
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
    (s : Finset ι) (t : NNReal) (a : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hat : ∀ i ∈ s, a i ≤ t)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    let C := fun i => Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i
    let K := fun ω z => ∑ i ∈ s, (C i).indicator (fun _ => H i ω) z
    let X := fun ω => (∫ z, K ω z ∂(N.N ω)) -
      (∫ z, K ω z ∂referenceIntensity ν)
    Integrable (fun ω => (X ω)^2) P ∧
      (∫ ω, (X ω)^2 ∂P) = ∫ ω, ∫ z, (K ω z)^2 ∂referenceIntensity ν ∂P := by
  dsimp only
  let C := fun i => Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i
  let K := fun ω z => ∑ i ∈ s, (C i).indicator (fun _ => H i ω) z
  let X := fun ω => (∫ z, K ω z ∂(N.N ω)) -
    (∫ z, K ω z ∂referenceIntensity ν)
  let Z := fun ω => ∑ i ∈ s, H i ω * N.compensated (C i) ω
  have hC (i : ι) (hi : i ∈ s) : MeasurableSet (C i) :=
    measurableSet_Ioc.prod (hB i hi)
  have hphys : X =ᵐ[P] Z :=
    Kyprianou.Ch04.finitePoissonIndicatorIntegralAE P ν N s C H hC hFin
  have hsec := Kyprianou.Ch04.finitePredictableTailBoxSecondMoment
    P ν F N hFuture hPast s t a B H hat hB hFin hH hH2
  have hen := Kyprianou.Ch04.finiteWeightedIndicatorExpectedSquareIntegral
    P (referenceIntensity ν) s C H hC hFin
    (fun i hi => ((hH i hi).mono (F.le' (a i))).aestronglyMeasurable) hH2
  have hinter (i j : ι) :
      C i ∩ C j = Set.Ioc (↑(max (a i) (a j)) : ℝ) (t : ℝ) ×ˢ (B i ∩ B j) := by
    ext z
    simp only [C, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, NNReal.coe_max, max_lt_iff]
    tauto
  have hsq : (fun ω => (X ω)^2) =ᵐ[P] (fun ω => (Z ω)^2) :=
    hphys.fun_comp (fun x : ℝ => x^2)
  change Integrable (fun ω => (X ω)^2) P ∧
    (∫ ω, (X ω)^2 ∂P) = ∫ ω, ∫ z, (K ω z)^2 ∂referenceIntensity ν ∂P
  refine ⟨hsec.1.congr hsq.symm, ?_⟩
  rw [integral_congr_ae hsq]
  change (∫ ω, (Z ω)^2 ∂P) = _
  rw [show (∫ ω, (Z ω)^2 ∂P) = _ from hsec.2]
  rw [show (∫ ω, ∫ z, (K ω z)^2 ∂referenceIntensity ν ∂P) = _ from hen]
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
  rw [hinter]
