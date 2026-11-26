-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41AtomicJumpIocV9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:39:54.521643+00:00
-- url     : https://prove2.me/submissions/1a583f77-415d-41a5-a28b-e261394d8317

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41HorizonAtomicV9
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (X Xleft : NNReal → Ω → ℝ) (w : Ω)
    (hNeg : ∀ s : NNReal, 0 < s → X s w ≤ Xleft s w)
    (hJ : Set.Countable {s : NNReal | 0 < s ∧ X s w ≠ Xleft s w})
    (t : NNReal)
    (g : ℝ → ℝ)
    (hs : Summable (fun s : Ioc (0 : NNReal) t => ‖g (X s w) - g (Xleft s w)‖)) :
    let μ := (pathJumpMeasure X Xleft w).restrict
        (Ioc (0 : ℝ) (t : ℝ) ×ˢ Iio (0 : ℝ))
    let J := fun z : ℝ × ℝ => g (Xleft z.1.toNNReal w + z.2) - g (Xleft z.1.toNNReal w)
    Integrable J μ ∧ (∫ z, J z ∂μ) =
      ∑' s : Ioc (0 : NNReal) t, (g (X s w) - g (Xleft s w)) := by
  classical
  let H : Set NNReal := {s | 0 < s ∧ s ≤ t ∧ X s w ≠ Xleft s w}
  have hsub : H ⊆ {s : NNReal | 0 < s ∧ X s w ≠ Xleft s w} := by
    intro s h
    exact ⟨h.1,h.2.2⟩
  letI : Countable H := (hJ.mono hsub).to_subtype
  let p : H → ℝ × ℝ := fun s => ((s : NNReal), X s w - Xleft s w)
  let J : ℝ × ℝ → ℝ := fun z => g (Xleft z.1.toNNReal w + z.2) -
    g (Xleft z.1.toNNReal w)
  have hp (s : H) : J (p s) = g (X s w) - g (Xleft s w) := by
    simp [J, p, add_sub_cancel_left]
  let i : H → Ioc (0 : NNReal) t := fun s => ⟨s, s.2.1, s.2.2.1⟩
  have hi : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun s : Ioc (0 : NNReal) t => (s : NNReal)) h
  have hs' : Summable (fun s : H => ‖J (p s)‖) := by
    have hsi : Summable (fun s : H => ‖g (X (i s) w) - g (Xleft (i s) w)‖) :=
      hs.comp_injective hi
    apply hsi.congr
    intro s
    rw [hp]
  dsimp only
  rw [exercise41HorizonAtomicV9 X Xleft w hNeg hJ t]
  change Integrable J (Measure.sum (fun s : H => Measure.dirac (p s))) ∧
    (∫ z, J z ∂Measure.sum (fun s : H => Measure.dirac (p s))) = _
  have hsw : Summable (fun s : H => (1 : ℝ≥0∞).toReal * ‖J (p s)‖) := by
    simpa using hs'
  have hc : ∀ s : H, (1 : ℝ≥0∞) ≠ ⊤ := fun _ => ENNReal.one_ne_top
  have hInt := integrable_sum_dirac hc hsw
  have hEq := integral_sum_dirac_eq_tsum hc hsw
  refine ⟨by simpa using hInt, ?_⟩
  simp only [ENNReal.toReal_one, one_smul, one_mul] at hEq
  rw [hEq]
  simp_rw [hp]
  rw [tsum_subtype H (fun s => g (X s w) - g (Xleft s w)),
    tsum_subtype (Ioc (0 : NNReal) t) (fun s => g (X s w) - g (Xleft s w))]
  apply tsum_congr
  intro s
  by_cases he : X s w = Xleft s w
  · simp [Set.indicator_apply, he]
  · simp [H, Set.indicator_apply, he, Set.mem_Ioc]
