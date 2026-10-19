-- Prove2me | solution 1 for OAI.MainGap.cut_cut
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:27:31.007162+00:00
-- url     : https://prove2.me/submissions/fcc71b57-8f38-44c1-b147-7336ea6b033e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Cutoffs.lean:L161-L180
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.cut_cut. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section MoreHer
variable [PartialOrder A] [StarOrderedRing A]

end MoreHer
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section Ramps
variable [PartialOrder A] [StarOrderedRing A]

lemma cut_cut {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u) :
    cut (cut a l) u = cut a (l+u) := by
  let f : ℝ → ℝ := fun t => max (t-l) 0
  let g : ℝ → ℝ := fun t => max (t-u) 0
  have hcomp := cfcₙ_comp g f a
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [g, max_eq_right (neg_nonpos.mpr hu)])
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [f, max_eq_right (neg_nonpos.mpr hl)]) (.of_nonneg ha)
  change cfcₙ g (cfcₙ f a) = _
  rw [← hcomp]
  apply cfcₙ_congr
  intro t _
  dsimp [f, g]
  by_cases ht : l ≤ t
  · rw [max_eq_left (sub_nonneg.mpr ht)]
    congr 1
    ring
  · rw [max_eq_right (by linarith : t-l ≤ 0), zero_sub,
      max_eq_right (neg_nonpos.mpr hu), max_eq_right (by linarith : t-(l+u) ≤ 0)]

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.cut_cut := @_root_.OAI.MainGap.cut_cut
