-- Prove2me | solution 1 for Kyprianou.Ch04.cellTailAdmissibilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:41:35.628428+00:00
-- url     : https://prove2.me/submissions/4cafea77-67ba-4146-9ded-a34b2444772a

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxPhysicalIsometry
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false


/-- Signed duplicate coefficients retain the endpoint measurability and energy hypotheses. -/
theorem solution {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (s : Finset ι) (T : NNReal) (a b : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i) (hbT : ∀ i ∈ s, b i ≤ T)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFa : ∀ i ∈ s, referenceIntensity ν (Ioc (a i : ℝ) (T : ℝ) ×ˢ B i) ≠ ⊤)
    (hFb : ∀ i ∈ s, referenceIntensity ν (Ioc (b i : ℝ) (T : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    let U := s.product (Finset.univ : Finset Bool)
    let A (i : ι × Bool) := if i.2 then a i.1 else b i.1
    let C (i : ι × Bool) := B i.1
    let W (i : ι × Bool) (ω : Ω) := if i.2 then H i.1 ω else -H i.1 ω
    (∀ i ∈ U, A i ≤ T) ∧ (∀ i ∈ U, MeasurableSet (C i)) ∧
    (∀ i ∈ U, referenceIntensity ν (Ioc (A i : ℝ) (T : ℝ) ×ˢ C i) ≠ ⊤) ∧
    (∀ i ∈ U, StronglyMeasurable[F (A i)] (W i)) ∧
    (∀ i ∈ U, Integrable (fun ω => (W i ω)^2) P) := by
  classical
  let U := s.product (Finset.univ : Finset Bool)
  let A (i : ι × Bool) := if i.2 then a i.1 else b i.1
  let C (i : ι × Bool) := B i.1
  let W (i : ι × Bool) (ω : Ω) := if i.2 then H i.1 ω else -H i.1 ω
  have hmem (i : ι × Bool) (hi : i ∈ U) : i.1 ∈ s :=
    (Finset.mem_product.mp hi).1
  have hAt (i : ι × Bool) (hi : i ∈ U) : A i ≤ T := by
    have h := hmem i hi
    cases i with
    | mk j q => cases q <;> simp [A, hbT j h, (hab j h).trans (hbT j h)]
  have hCt (i : ι × Bool) (hi : i ∈ U) : MeasurableSet (C i) := hB _ (hmem i hi)
  have hFt (i : ι × Bool) (hi : i ∈ U) :
      referenceIntensity ν (Ioc (A i : ℝ) (T : ℝ) ×ˢ C i) ≠ ⊤ := by
    have h := hmem i hi
    cases i with
    | mk j q => cases q <;> simp [A, C, hFa j h, hFb j h]
  have hWt (i : ι × Bool) (hi : i ∈ U) : StronglyMeasurable[F (A i)] (W i) := by
    have h := hmem i hi
    cases i with
    | mk j q =>
      cases q
      · change StronglyMeasurable[F (b j)] (fun ω => -H j ω)
        exact ((hH j h).mono (F.mono (hab j h))).neg
      · simpa [A,W] using hH j h
  have hW2 (i : ι × Bool) (hi : i ∈ U) : Integrable (fun ω => (W i ω)^2) P := by
    have h := hmem i hi
    cases i with
    | mk j q => cases q <;> simpa [W, neg_sq] using hH2 j h
  exact ⟨hAt,hCt,hFt,hWt,hW2⟩
