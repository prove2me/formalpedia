-- Prove2me | solution 1 for Kyprianou.Ch04.signedKernelPositiveParts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:12:13.802684+00:00
-- url     : https://prove2.me/submissions/4dc75f51-e5d1-4a42-847b-b95897695b23

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Taking the positive and negative parts preserves marked kernel admissibility. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (k : ℝ → ℝ → Omega → ℝ)
    (hm : Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2))
    (ha : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => k (t : ℝ) z.2 z.1))
    (hc : ∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => k s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (k (t : ℝ) x w))) :
    let kp := fun s x w => max (k s x w) 0
    let kn := fun s x w => max (-k s x w) 0
    IsAdmissiblePoissonKernel P F kp ∧ IsAdmissiblePoissonKernel P F kn ∧
    (∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => kp s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (kp (t : ℝ) x w))) ∧
    (∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => kn s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (kn (t : ℝ) x w))) := by
  have hp : ∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => max (k s x w) 0) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (max (k (t : ℝ) x w) 0)) := by
    filter_upwards [hc] with w hw
    exact fun x t ht => (hw x t ht).max tendsto_const_nhds
  have hn : ∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => max (-k s x w) 0) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (max (-k (t : ℝ) x w) 0)) := by
    filter_upwards [hc] with w hw
    exact fun x t ht => (hw x t ht).neg.max tendsto_const_nhds
  refine ⟨⟨fun _ _ _ => le_max_right _ _,hm.max measurable_const,
    fun t => (ha t).max measurable_const,?_⟩,
    ⟨fun _ _ _ => le_max_right _ _,hm.neg.max measurable_const,
      fun t => (ha t).neg.max measurable_const,?_⟩,hp,hn⟩
  · intro x
    filter_upwards [hp] with w hw
    exact hw x
  · intro x
    filter_upwards [hn] with w hw
    exact hw x
