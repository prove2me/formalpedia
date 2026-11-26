-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41NoJumpFromZeroV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:13:18.207631+00:00
-- url     : https://prove2.me/submissions/f176ac6d-845d-487e-8b7f-6687dd0f35ca

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41PrezeroMarkedCountZeroV6
import Theorems.Thm_Kyprianou_Ch04_exercise41PrezeroProductNullV6
import Theorems.Thm_Kyprianou_Ch04_exercise41PredictableZeroSetV6
import Theorems.Thm_Kyprianou_Ch04_exercise41PhysicalMarkPositiveV6
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ s : NNReal, 0 < s →
      Function.leftLim (fun t => L.X t w) s = 0 → L.X s w = 0 := by
  let E (n : ℕ) : Set (NNReal × Ω) := {p | 0 < p.1 ∧ p.1 ≤ (n : NNReal) ∧
    Function.leftLim (fun t => L.X t p.2) p.1 = 0}
  let NX : Ω → Measure (NNReal × ℝ) := fun w =>
    ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
      Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
      (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
  have hn (n : ℕ) : ∀ᵐ w ∂P, NX w {p | (p.1,w) ∈ E n ∧ p.2 < 0} = 0 :=
    exercise41PrezeroMarkedCountZeroV6 P F L (n : NNReal) (E n)
      (exercise41PredictableZeroSetV6 P F L n).1
      (fun p hp => hp.2.1) (exercise41PrezeroProductNullV6 P F L hBV hd n)
  have hx := rightContinuous_measurable_sections_joint_evaluation L.X
    (fun t => (L.adapted t).mono (F.le t) le_rfl) L.rightCont
  have hl := avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits L.X hx
    (by
      have H : (fun w : Ω => Function.leftLim (fun t => L.X t w) (0 : NNReal)) =
          L.X 0 := by
        funext w
        exact leftLim_eq_of_isBot (fun _ => bot_le)
      rw [H]
      exact (L.adapted 0).mono (F.le 0) le_rfl) L.leftLim
  filter_upwards [ae_all_iff.mpr hn] with w hw s hs hz
  obtain ⟨n, hsn⟩ := exists_nat_ge s
  let A : Set (NNReal × ℝ) := {p | (p.1,w) ∈ E n ∧ p.2 < 0}
  have hA : MeasurableSet A := by
    have he : MeasurableSet (E n) := (exercise41PredictableZeroSetV6 P F L n).2
    exact (he.preimage (measurable_fst.prodMk measurable_const)).inter
      (measurableSet_Iio.preimage measurable_snd)
  have hneg : L.X s w ≤ 0 := by
    obtain ⟨l, hL⟩ := L.leftLim w s hs
    letI : NeBot (nhdsWithin s (Iio s)) := nhdsLT_neBot_of_exists_lt ⟨0,hs⟩
    have he := leftLim_eq_of_tendsto hL
    rw [hz] at he
    exact he ▸ L.noPosJumps w s l hs hL
  by_contra hne
  have hlt : L.X s w < 0 := lt_of_le_of_ne hneg hne
  have H := exercise41PhysicalMarkPositiveV6 (fun t => L.X t w)
    (fun t => Function.leftLim (fun v => L.X v w) t)
    (hx.comp measurable_prodMk_right) (hl.comp measurable_prodMk_right)
    A hA s hs (by rw [hz, sub_zero]; exact hne)
    (by exact ⟨⟨hs,hsn,hz⟩,by rw [hz,sub_zero];exact hlt⟩)
  change 1 ≤ NX w A at H
  rw [show NX w A = 0 from hw n] at H
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ≥0∞) < 1)) H
