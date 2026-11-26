-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_capped_history_weight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:17:08.166421+00:00
-- url     : https://prove2.me/submissions/394c65c8-5564-4892-b360-a721decf9026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stronglyProgressive
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A stopped position weighted by the finite-cap passage event is measurable in the stopped history. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F.rightCont τ)
    (n : NNReal) (T : Ω → NNReal)
    (hT : ∀ w, (T w : WithTop NNReal) = min (τ w) (n : WithTop NNReal))
    (hstop : IsStoppingTime F.rightCont (fun w => (T w : WithTop NNReal)))
    (β : ℝ) :
    Measurable[hstop.measurableSpace]
      (({w : Ω | τ w ≤ (n : WithTop NNReal)} : Set Ω).indicator
        (fun w => ENNReal.ofReal (Real.exp (β * L.X (T w) w)))) := by
  have hEq : (fun w => (T w : WithTop NNReal)) =
      (fun w => min (τ w) (n : WithTop NNReal)) := funext hT
  have hA : MeasurableSet[hstop.measurableSpace] {w : Ω | τ w ≤ (n : WithTop NNReal)} := by
    apply (hstop.measurableSet _).mpr
    refine ⟨le_iSup F.rightCont n _ (hτ.measurableSet_le n), ?_⟩
    intro s
    have hset : {w : Ω | τ w ≤ (n : WithTop NNReal)} ∩
        {w : Ω | (T w : WithTop NNReal) ≤ s} =
        {w : Ω | τ w ≤ (min n s : NNReal)} := by
      ext w
      simp only [mem_inter_iff, mem_setOf_eq, hT, WithTop.coe_min]
      constructor
      · rintro ⟨hn,hs⟩
        rw [min_eq_left hn] at hs
        exact le_min hn hs
      · intro h
        exact ⟨(le_min_iff.mp h).1, (min_le_left _ _).trans (le_min_iff.mp h).2⟩
    rw [hset]
    exact F.rightCont.mono (min_le_right n s) _ (hτ.measurableSet_le (min n s))
  have hp : IsStronglyProgressive F.rightCont L.X := by
    obtain ⟨Y,hY,_,_,_⟩ := levy_rightCont_process L
    simpa only [hY] using tauceti_original_levy_stronglyProgressive Y
  have hs := measurable_stoppedValue hp hstop
  have hx : Measurable[hstop.measurableSpace] (fun w => L.X (T w) w) := by
    have he : stoppedValue L.X (fun w => (T w : WithTop NNReal)) =
        (fun w => L.X (T w) w) := by
      funext w
      unfold stoppedValue
      rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
      rfl
    rwa [he] at hs
  exact (ENNReal.measurable_ofReal.comp ((measurable_const.mul hx).exp)).indicator hA
