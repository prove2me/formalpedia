-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedRightStronglyAdaptedIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:08:37.548262+00:00
-- url     : https://prove2.me/submissions/9835f360-38a0-44dc-9a2d-c9394d5ee8c1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_measurable_past
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_measurable
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_pointwiseBound

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The discounted candidate is right-naturally adapted and uniformly integrable at fixed times. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t) :
    let barrier := Real.log (K * phi / (1 + phi))
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      Real.exp (-q * (t : ℝ)) *
        mckeanValue K barrier phi (x + X t ω)
    StronglyAdapted F M ∧
      ∀ t : ℝ≥0, Integrable (M t) P := by
  dsimp only
  let b := Real.log (K * phi / (1 + phi))
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-q * (t : ℝ)) * mckeanValue K b phi (x + X t ω)
  change StronglyAdapted F M ∧ ∀ t : ℝ≥0, Integrable (M t) P
  have hAdapt : StronglyAdapted F M := by
    intro t
    have hY :
        @Measurable Ω ℝ (F t) inferInstance
          (fun ω : Ω => x + X t ω) := by
      rw [hF t]
      exact Kyprianou.Ch01.naturalSigmaRight_measurable_past
        (fun u ω => x + X u ω) t t le_rfl
    have hValue :
        @Measurable Ω ℝ (F t) inferInstance
          (fun ω : Ω => mckeanValue K b phi (x + X t ω)) :=
      (Kyprianou.Ch01.mckeanValue_measurable K b phi).comp hY
    have hMt :
        @Measurable Ω ℝ (F t) inferInstance (M t) :=
      measurable_const.mul hValue
    exact hMt.stronglyMeasurable
  refine ⟨hAdapt, ?_⟩
  intro t
  have hMt : StronglyMeasurable (M t) := hAdapt.stronglyMeasurable
  have hBound (ω : Ω) : ‖M t ω‖ ≤ K := by
    have hb := Kyprianou.Ch01.mckeanDiscountedValue_pointwiseBound
      X x K q phi hK hq hphi t ω
    exact (Real.norm_eq_abs _).symm ▸ (abs_of_nonneg hb.1 ▸ hb.2)
  exact Integrable.of_bound hMt.aestronglyMeasurable K
    (Filter.Eventually.of_forall hBound)
