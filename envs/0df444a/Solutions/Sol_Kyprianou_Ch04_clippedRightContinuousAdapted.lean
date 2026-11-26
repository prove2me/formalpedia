-- Prove2me | solution 1 for Kyprianou.Ch04.clippedRightContinuousAdapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:57:14.424519+00:00
-- url     : https://prove2.me/submissions/b0a9199e-451e-4f11-9539-e164e0b88cca

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rightContinuousAdaptedVersionOffNull
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_bounded_stop_eval_measurable
import Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
open MeasureTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- Clipping an adapted right-continuous path at a stopping time preserves adaptedness. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (J : NNReal → Ω → ℝ) (hJ : StronglyAdapted F J)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => J u w) (Ici t) t)
    (tau : Ω → WithTop NNReal) (ht : IsStoppingTime F tau) :
    StronglyAdapted F (fun (t : NNReal) w =>
      J ((min (tau w) (t : WithTop NNReal)).untopD t) w) := by
  classical
  let c := fun (t : NNReal) w => (min (tau w) (t : WithTop NNReal)).untopD t
  have hc (t : NNReal) : IsStoppingTime F (fun w => (c t w : WithTop NNReal)) := by
    simpa only [c,clippedClockCoe] using ht.min_const t
  have hle (t : NNReal) (w : Ω) : c t w ≤ t :=
    WithTop.coe_le_coe.mp ((clippedClockCoe (tau w) t).trans_le (min_le_right _ _))
  obtain ⟨N,K,hm,hzero,hK,hKr,hAgree⟩ := rightContinuousAdaptedVersionOffNull P F hNull J hJ hr
  show StronglyAdapted F (fun t w => J (c t w) w)
  intro t
  have h := Kyprianou.Ch08.StageB.p2m810_bounded_stop_eval_measurable F K hK hKr
    (c t) (hc t) t (hle t)
  apply Measurable.stronglyMeasurable
  intro B hB
  let U := {w | J (c t w) w ∈ B}
  let V := {w | K (c t w) w ∈ B}
  have he : U = (V \ N) ∪ (U ∩ N) := by
    ext w
    by_cases hw : w ∈ N
    · simp [U,V,hw]
    · simp [U,V,hw,hAgree w hw]
  change MeasurableSet[F t] U
  rw [he]
  exact ((h hB).diff (hNull t N N hm hzero subset_rfl)).union
    (hNull t N _ hm hzero Set.inter_subset_right)
