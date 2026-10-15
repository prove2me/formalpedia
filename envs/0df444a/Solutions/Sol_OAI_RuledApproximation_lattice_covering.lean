-- Prove2me | solution 1 for OAI.RuledApproximation.lattice_covering
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:39:16.745569+00:00
-- url     : https://prove2.me/submissions/e487fdff-c782-461d-bac6-f1c1fc535ec2

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Lattice.lean:L132-L149
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.lattice_covering. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Theorems.Thm_OAI_RuledApproximation_asymmetric_lattice_cover

-- ---- from OAI.Geometry.RuledCovering.Lattice ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma symmetric_lattice_distance (a x y : ℝ) (ha : |a| < 1)
    (hx : |x + a * y| ≤ 1 / 2) (hy : |y + a * x| ≤ 1 / 2) :
    max |x| |y| ≤ 1 / (2 * (1 - |a|)) := by
  have hax : |x| ≤ 1 / 2 + |a| * |y| := by
    calc
      |x| = |(x + a * y) - a * y| := by congr 1; ring
      _ ≤ |x + a * y| + |a * y| := abs_sub _ _
      _ ≤ 1 / 2 + |a| * |y| := by rw [abs_mul]; exact add_le_add hx le_rfl
  have hay : |y| ≤ 1 / 2 + |a| * |x| := by
    calc
      |y| = |(y + a * x) - a * x| := by congr 1; ring
      _ ≤ |y + a * x| + |a * x| := abs_sub _ _
      _ ≤ 1 / 2 + |a| * |x| := by rw [abs_mul]; exact add_le_add hy le_rfl
  have hm : max |x| |y| ≤ 1 / 2 + |a| * max |x| |y| := by
    apply max_le
    · exact hax.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_max_right _ _) (abs_nonneg a)))
    · exact hay.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_max_left _ _) (abs_nonneg a)))
  apply (le_div_iff₀ (by positivity : 0 < 2 * (1 - |a|))).2
  nlinarith

/-- Lattice covering with a uniform distance estimate. -/
theorem lattice_covering (a : ℝ) (ha : |a| < 1) (z₁ z₂ : ℝ) :
    ∃ i j : ℤ,
      |(z₁ - i) + a * (z₂ - j)| ≤ 1 / 2 ∧
      |(z₂ - j) + a * (z₁ - i)| ≤ 1 / 2 ∧
      max |z₁ - i| |z₂ - j| ≤ 1 / (2 * (1 - |a|)) := by
  have haa : a * a < 1 := by nlinarith [sq_abs a, abs_nonneg a]
  obtain ⟨i, j, hi, hj⟩ := asymmetric_lattice_cover a a (mul_self_nonneg a)
    haa (z₁ + a * z₂) (z₂ + a * z₁)
  have hi' : |(z₁ - i) + a * (z₂ - j)| ≤ 1 / 2 := by
    convert hi using 1
    congr 1
    ring
  have hj' : |(z₂ - j) + a * (z₁ - i)| ≤ 1 / 2 := by
    convert hj using 1
    congr 1
    ring
  exact ⟨i, j, hi', hj', symmetric_lattice_distance a _ _ ha hi' hj'⟩

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.lattice_covering := @_root_.OAI.RuledApproximation.lattice_covering
