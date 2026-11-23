-- Prove2me | solution 1 for Kyprianou.Ch02.realMarkL2ApproxEventuallyUniformL2BoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:17:21.432028+00:00
-- url     : https://prove2.me/submissions/542c3047-2e2b-43dc-9d76-6e4a7653e892

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) [SigmaFinite ν] (B : Set ℝ)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hfL2 : Filter.Tendsto
      (fun n => eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B))
      Filter.atTop (nhds 0)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ᶠ n in Filter.atTop,
        eLpNorm (fun x : ℝ => (f n) x) 2 (ν.restrict B) ≤ C := by
  have hsmall : ∀ᶠ n in Filter.atTop,
      eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B) < 1 := by
    apply hfL2.eventually
    exact isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1)
  refine ⟨1 + eLpNorm (fun x : ℝ => x) 2 (ν.restrict B), ?_, ?_⟩
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hsecond.2⟩
  filter_upwards [hsmall] with n hn
  let g : ℝ → ℝ := fun x => (f n) x - x
  have hg : AEStronglyMeasurable g (ν.restrict B) :=
    ((f n).measurable.sub measurable_id).aestronglyMeasurable
  have hid : AEStronglyMeasurable (fun x : ℝ => x) (ν.restrict B) :=
    measurable_id.aestronglyMeasurable
  have htri :
      eLpNorm (g + fun x : ℝ => x) 2 (ν.restrict B) ≤
      eLpNorm g 2 (ν.restrict B) +
        eLpNorm (fun x : ℝ => x) 2 (ν.restrict B) :=
    eLpNorm_add_le hg hid (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    eLpNorm (fun x : ℝ => (f n) x) 2 (ν.restrict B) =
        eLpNorm (g + fun x : ℝ => x) 2 (ν.restrict B) := by
          congr 1
          funext x
          change (f n) x = (f n) x - x + x
          ring
    _ ≤ eLpNorm g 2 (ν.restrict B) +
        eLpNorm (fun x : ℝ => x) 2 (ν.restrict B) := htri
    _ ≤ 1 + eLpNorm (fun x : ℝ => x) 2 (ν.restrict B) :=
      add_le_add_left (le_of_lt hn) _
