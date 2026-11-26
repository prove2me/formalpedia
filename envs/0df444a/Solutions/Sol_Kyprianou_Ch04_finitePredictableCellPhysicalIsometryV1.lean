-- Prove2me | solution 1 for Kyprianou.Ch04.finitePredictableCellPhysicalIsometryV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:44:26.898685+00:00
-- url     : https://prove2.me/submissions/ca6bde3e-c3ec-4c5d-8da8-5a3fed14ad91

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxPhysicalIsometry
import Theorems.Thm_Kyprianou_Ch04_cellTailAdmissibilityV1
import Theorems.Thm_Kyprianou_Ch04_cellTailKernelIdentityV1
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite predictable time cells inherit the physical isometry from tail boxes. -/
theorem solution {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ →
      Measurable[F u] (fun ω => N.N ω D))
    (s : Finset ι) (T : NNReal) (a b : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i) (hbT : ∀ i ∈ s, b i ≤ T)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFa : ∀ i ∈ s, referenceIntensity ν (Ioc (a i : ℝ) (T : ℝ) ×ˢ B i) ≠ ⊤)
    (hFb : ∀ i ∈ s, referenceIntensity ν (Ioc (b i : ℝ) (T : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    let K := fun ω z => ∑ i ∈ s, (Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i).indicator
      (fun _ => H i ω) z
    let J := fun ω => (∫ z, K ω z ∂(N.N ω)) - (∫ z, K ω z ∂referenceIntensity ν)
    Integrable (fun ω => (J ω)^2) P ∧
      (∫ ω, (J ω)^2 ∂P) = ∫ ω, ∫ z, (K ω z)^2 ∂referenceIntensity ν ∂P := by
  classical
  obtain ⟨hAt,hCt,hFt,hWt,hW2⟩ :=
    Kyprianou.Ch04.cellTailAdmissibilityV1 P ν F s T a b B H hab hbT hB hFa hFb hH hH2
  have hIso := Kyprianou.Ch04.finitePredictableTailBoxPhysicalIsometry
    P ν F N hFuture hPast (s.product (Finset.univ : Finset Bool)) T
    (fun i => if i.2 then a i.1 else b i.1) (fun i => B i.1)
    (fun i ω => if i.2 then H i.1 ω else -H i.1 ω)
    hAt hCt hFt hWt hW2
  dsimp only at hIso
  simp_rw [Kyprianou.Ch04.cellTailKernelIdentityV1 s T a b B H hab hbT] at hIso
  exact hIso
