-- Prove2me | solution 1 for Kyprianou.Ch04.rightContinuousAdaptedVersionOffNull
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:55:31.47524+00:00
-- url     : https://prove2.me/submissions/6bcf3c5c-bcbb-4a40-82e2-edfb370f8725

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A common-null right-continuous adapted version with exact agreement outside its null set. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (J : NNReal → Ω → ℝ) (hJ : StronglyAdapted F J)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => J u w) (Ici t) t) :
    ∃ (N : Set Ω) (K : NNReal → Ω → ℝ), MeasurableSet N ∧ P N = 0 ∧
      (∀ t, Measurable[F t] (K t)) ∧
      (∀ w t, ContinuousWithinAt (fun u => K u w) (Ici t) t) ∧
      ∀ w, w ∉ N → ∀ t, K t w = J t w := by
  classical
  have hr' := hr
  rw [ae_iff] at hr'
  obtain ⟨N,hsub,hm,hzero⟩ := exists_measurable_superset_of_null hr'
  let K := fun t w => if w ∈ N then 0 else J t w
  have hK (t : NNReal) : Measurable[F t] (K t) :=
    Measurable.ite (hNull t N N hm hzero subset_rfl) measurable_const
      (hJ t).measurable
  have hKr (w : Ω) (t : NNReal) :
      ContinuousWithinAt (fun u => K u w) (Ici t) t := by
    by_cases hw : w ∈ N
    · simpa only [K,if_pos hw] using
        (continuousWithinAt_const : ContinuousWithinAt (fun _ : NNReal => (0:ℝ)) (Ici t) t)
    · have hgood : ∀ u : NNReal, ContinuousWithinAt (fun v => J v w) (Ici u) u :=
        not_not.mp (fun hbad => hw (hsub hbad))
      simpa only [K,if_neg hw] using hgood t
  exact ⟨N,K,hm,hzero,hK,hKr,fun w hw t => if_neg hw⟩
