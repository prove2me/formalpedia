-- Prove2me | solution 1 for OAI.MainGap.norm_sub_cut_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:28:57.188115+00:00
-- url     : https://prove2.me/submissions/f21a784d-7947-477a-b955-b1c81c821181

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Cutoffs.lean:L182-L197
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.norm_sub_cut_le. The node keeps its source
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

lemma norm_sub_cut_le {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 ≤ l) :
    ‖a - cut a l‖ ≤ l := by
  conv_lhs => arg 1; lhs; rw [← cfcₙ_id ℝ a (.of_nonneg ha)]
  rw [cut, ← cfcₙ_sub id (fun t : ℝ => max (t-l) 0) a continuousOn_id rfl
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hl)])]
  apply norm_cfcₙ_le
  intro t ht
  have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg a ha t ht
  dsimp only [id_eq]
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hh : max (t-l) 0 ≤ t := max_le (by linarith) ht0
    linarith
  · have hh := le_max_left (t-l) 0
    linarith

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


theorem solution : type_of% @_root_.OAI.MainGap.norm_sub_cut_le := @_root_.OAI.MainGap.norm_sub_cut_le
