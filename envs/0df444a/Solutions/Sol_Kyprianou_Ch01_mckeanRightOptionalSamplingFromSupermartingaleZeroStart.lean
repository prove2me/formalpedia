-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanRightOptionalSamplingFromSupermartingaleZeroStart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:05:12.294695+00:00
-- url     : https://prove2.me/submissions/69c8c24d-d75c-4fdd-82e3-f244fff32ff6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_rightStoppedMeasurable
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedClippedValue_tendsto
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_pointwiseBound
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_continuousPath
import Theorems.Thm_Kyprianou_Ch01_mckeanRightClippedDiscountedValueMeasurable
import Theorems.Thm_Kyprianou_Ch01_rightNaturalClippedSupermartingaleExpectedBound
import Theorems.Thm_Kyprianou_Ch01_boundedConvergenceExpectedUpper

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Genuine bounded optional sampling with the indispensable zero start. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (hStart : X 0 = fun _ => 0)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t)
    (hSM : Supermartingale
      (fun (t : ℝ≥0) ω => Real.exp (-q * (t : ℝ)) *
        mckeanValue K (Real.log (K * phi / (1 + phi))) phi
          (x + X t ω)) F P)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau) :
    let barrier := Real.log (K * phi / (1 + phi))
    let Z : Ω → ℝ := fun ω =>
      match tau ω with
      | none => 0
      | some t => Real.exp (-q * (t : ℝ)) *
          mckeanValue K barrier phi (x + X t ω)
    Integrable Z P ∧
      (∫ ω, Z ω ∂P) ≤ mckeanValue K barrier phi x := by
  dsimp only
  let b : ℝ := Real.log (K * phi / (1 + phi))
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-q * (t : ℝ)) * mckeanValue K b phi (x + X t ω)
  let T (n : ℕ) (ω : Ω) : ℝ≥0 :=
    (min (tau ω) ((n : ℝ≥0) : WithTop ℝ≥0)).untopD (n : ℝ≥0)
  let f (n : ℕ) (ω : Ω) : ℝ := M (T n ω) ω
  let Z : Ω → ℝ := fun ω =>
    match tau ω with
    | none => 0
    | some t => M t ω
  change Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ mckeanValue K b phi x
  have hMpoint (t : ℝ≥0) (ω : Ω) : 0 ≤ M t ω ∧ M t ω ≤ K := by
    exact Kyprianou.Ch01.mckeanDiscountedValue_pointwiseBound
      X x K q phi hK hq hphi t ω
  have hMbound (t : ℝ≥0) (ω : Ω) : ‖M t ω‖ ≤ K := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hMpoint t ω).1]
      using (hMpoint t ω).2
  have hfBound (n : ℕ) (ω : Ω) : ‖f n ω‖ ≤ K :=
    hMbound (T n ω) ω
  have hZbound (ω : Ω) : ‖Z ω‖ ≤ K := by
    cases ht : tau ω with
    | top => simpa [Z, ht] using hK.le
    | coe t => simpa [Z, ht] using hMbound t ω
  have hMeasZ : Measurable Z :=
    Kyprianou.Ch01.mckeanDiscountedValue_rightStoppedMeasurable
      X x K q phi hXmeas hAllContinuous tau hTau
  have hMeasF (n : ℕ) : Measurable (f n) :=
    Kyprianou.Ch01.mckeanRightClippedDiscountedValueMeasurable
      X x K q phi hXmeas hAllContinuous F hF tau hTau n
  have hLimit (ω : Ω) :
      Tendsto (fun n : ℕ => f n ω) atTop (nhds (Z ω)) :=
    Kyprianou.Ch01.mckeanDiscountedClippedValue_tendsto
      X x K q phi hK hq hphi tau ω
  have hRight (ω : Ω) (v : ℝ≥0) :
      ContinuousWithinAt (fun t : ℝ≥0 => M t ω) (Set.Ici v) v :=
    (Kyprianou.Ch01.mckeanDiscountedValue_continuousPath
      X x K q phi hK hphi hAllContinuous ω).continuousWithinAt
  have hStartM : (fun ω : Ω => M 0 ω) =
      (fun _ => mckeanValue K b phi x) := by
    funext ω
    have hx := congrFun hStart ω
    simp [M, hx]
  have hInt0 : (∫ ω, M 0 ω ∂P) = mckeanValue K b phi x := by
    rw [hStartM]
    simp
  have hUpper (n : ℕ) :
      (∫ ω, f n ω ∂P) ≤ mckeanValue K b phi x := by
    calc
      (∫ ω, f n ω ∂P) ≤ (∫ ω, M 0 ω ∂P) :=
        Kyprianou.Ch01.rightNaturalClippedSupermartingaleExpectedBound
          P (fun t ω => x + X t ω) M F hF hSM K hMbound hRight
          tau hTau (n : ℝ≥0)
      _ = mckeanValue K b phi x := hInt0
  exact Kyprianou.Ch01.boundedConvergenceExpectedUpper
    P f Z K (mckeanValue K b phi x)
    hMeasF hMeasZ hfBound hZbound hLimit hUpper
