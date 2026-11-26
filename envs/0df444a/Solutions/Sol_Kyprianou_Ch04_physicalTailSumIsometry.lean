-- Prove2me | solution 1 for Kyprianou.Ch04.physicalTailSumIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:14:39.461036+00:00
-- url     : https://prove2.me/submissions/6324d538-ee11-4c25-83ca-8a43c8edc603

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxPhysicalIsometry
import Theorems.Thm_Kyprianou_Ch04_poissonCountZeroOfReferenceZero
import Theorems.Thm_Kyprianou_Ch04_referenceIntensityTimeBoxFinite
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Isometry for a kernel equal to a finite predictable tail sum off time zero. -/
theorem solution
    {Omega ι : Type} [MeasurableSpace Omega] [DecidableEq ι]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P nu F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun w => N.N w D))
    (s : Finset ι) (t : NNReal) (a : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Omega → ℝ)
    (hat : ∀ i ∈ s, a i ≤ t)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, nu (B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun w => (H i w)^2) P)
    (K : Omega → (ℝ × ℝ) → ℝ)
    (hK : ∀ w z, z.1 ≠ 0 →
      K w z = ∑ i ∈ s, (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i).indicator
        (fun _ => H i w) z) :
    let X := fun w => (∫ z, K w z ∂(N.N w)) - ∫ z, K w z ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧
      (∫ w, (X w)^2 ∂P) = ∫ w, ∫ z, (K w z)^2 ∂referenceIntensity nu ∂P := by
  let C : Set (ℝ × ℝ) := {0} ×ˢ Set.univ
  have hCm : MeasurableSet C := (measurableSet_singleton _).prod MeasurableSet.univ
  have hC0 : referenceIntensity nu C = 0 := by
    rw [referenceIntensity, show C = {0} ×ˢ (Set.univ : Set ℝ) from rfl,
      Measure.prod_prod, Measure.restrict_apply (measurableSet_singleton _)]
    simp
  have hCN := Kyprianou.Ch04.poissonCountZeroOfReferenceZero P nu N C hCm hC0
  let L := fun w z => ∑ i ∈ s, (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i).indicator
    (fun _ => H i w) z
  have hEq (w : Omega) (M : Measure (ℝ × ℝ)) (h0 : M C = 0) :
      K w =ᵐ[M] L w := by
    have hz : ∀ᵐ z ∂M, z ∉ C := (ae_iff.mpr (by simpa using h0))
    filter_upwards [hz] with z hz
    exact hK w z (fun h => hz (by simp [C, h]))
  let X := fun w => (∫ z, K w z ∂(N.N w)) - ∫ z, K w z ∂referenceIntensity nu
  let Y := fun w => (∫ z, L w z ∂(N.N w)) - ∫ z, L w z ∂referenceIntensity nu
  have hXY : X =ᵐ[P] Y := by
    filter_upwards [hCN] with w hw
    dsimp [X,Y]
    rw [integral_congr_ae (hEq w (N.N w) hw),
      integral_congr_ae (hEq w (referenceIntensity nu) hC0)]
  have hsq : (fun w => (X w)^2) =ᵐ[P] (fun w => (Y w)^2) :=
    hXY.fun_comp (fun x : ℝ => x^2)
  have hsec := Kyprianou.Ch04.finitePredictableTailBoxPhysicalIsometry P nu F N
    hFuture hPast s t a B H hat hB
    (fun i hi => Kyprianou.Ch04.referenceIntensityTimeBoxFinite nu (a i) t (B i) (hFin i hi))
    hH hH2
  change Integrable (fun w => (X w)^2) P ∧
    (∫ w, (X w)^2 ∂P) = ∫ w, ∫ z, (K w z)^2 ∂referenceIntensity nu ∂P
  refine ⟨hsec.1.congr hsq.symm, ?_⟩
  rw [integral_congr_ae hsq]
  change (∫ w, (Y w)^2 ∂P) = _
  rw [show (∫ w, (Y w)^2 ∂P) = _ from hsec.2]
  apply integral_congr_ae
  exact Eventually.of_forall fun w =>
    integral_congr_ae ((hEq w (referenceIntensity nu) hC0).fun_comp (fun x : ℝ => x^2)).symm
