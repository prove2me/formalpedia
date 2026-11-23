-- Prove2me | solution 1 for Kyprianou.Ch01.measurableProductPMFSumLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:30:08.142132+00:00
-- url     : https://prove2.me/submissions/1ad36d21-645b-4dde-a618-93acd99f8d67

import Mathlib
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f g : Ω → ℕ) (hf : Measurable f) (hg : Measurable g)
    (p q : PMF ℕ)
    (hp : ∀ n : ℕ, Q {ω | f ω = n} = p n)
    (hq : ∀ n : ℕ, Q {ω | g ω = n} = q n)
    (k : ℕ) :
    (Q.prod Q) {z : Ω × Ω | f z.1 + g z.2 = k} =
      ((p.bind (fun n => q.map (fun m => n + m))) k) := by
  have hLawF : Q.map f = p.toMeasure := by
    apply Measure.ext_of_singleton
    intro n
    rw [Measure.map_apply hf (measurableSet_singleton n),
      PMF.toMeasure_apply_singleton p n (measurableSet_singleton n)]
    exact hp n
  have hLawG : Q.map g = q.toMeasure := by
    apply Measure.ext_of_singleton
    intro n
    rw [Measure.map_apply hg (measurableSet_singleton n),
      PMF.toMeasure_apply_singleton q n (measurableSet_singleton n)]
    exact hq n
  have hMap (n : ℕ) :
      Q {ω | n + g ω = k} =
        (q.map (fun m => n + m)) k := by
    have hM : Measurable (fun m : ℕ => n + m) :=
      Measurable.of_discrete
    calc
      Q {ω | n + g ω = k} =
          (Q.map g) {m : ℕ | n + m = k} := by
            have hmset : MeasurableSet {m : ℕ | n + m = k} :=
              hM (measurableSet_singleton k)
            simpa [Set.preimage] using
              (Measure.map_apply hg hmset).symm
      _ = q.toMeasure {m : ℕ | n + m = k} := by rw [hLawG]
      _ = (q.map (fun m => n + m)).toMeasure {k} := by
            exact (PMF.toMeasure_map_apply (fun m : ℕ => n + m)
              q ({k} : Set ℕ) hM (measurableSet_singleton k)).symm
      _ = (q.map (fun m => n + m)) k :=
            PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
  have hSet : MeasurableSet
      {z : Ω × Ω | f z.1 + g z.2 = k} :=
    (((hf.comp measurable_fst).add (hg.comp measurable_snd))
      (measurableSet_singleton k))
  calc
    (Q.prod Q) {z : Ω × Ω | f z.1 + g z.2 = k} =
        ∫⁻ x, Q {y | f x + g y = k} ∂Q :=
      Measure.prod_apply hSet
    _ = ∫⁻ x, (q.map (fun m => f x + m)) k ∂Q := by
      apply lintegral_congr
      intro x
      exact hMap (f x)
    _ = ∫⁻ n, (q.map (fun m => n + m)) k ∂(Q.map f) := by
      rw [lintegral_map (Measurable.of_discrete) hf]
    _ = ∫⁻ n, (q.map (fun m => n + m)) k ∂p.toMeasure := by
      rw [hLawF]
    _ = ∑' n : ℕ, (q.map (fun m => n + m)) k * p n := by
      rw [lintegral_countable']
      congr 1
      funext n
      rw [PMF.toMeasure_apply_singleton p n (measurableSet_singleton n)]
    _ = (p.bind (fun n => q.map (fun m => n + m))) k := by
      rw [PMF.bind_apply]
      congr 1
      funext n
      ring
