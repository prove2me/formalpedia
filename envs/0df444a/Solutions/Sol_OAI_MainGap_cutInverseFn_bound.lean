-- Prove2me | solution 1 for OAI.MainGap.cutInverseFn_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:58:16.397964+00:00
-- url     : https://prove2.me/submissions/672f313b-58fd-44ee-baac-65d5269fdd4c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean:L27-L43
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.cutInverseFn_bound. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Compression ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma cutInverseFn_bound {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    0 ≤ cutInverseFn δ t ∧ cutInverseFn δ t ≤ 1/δ := by
  refine ⟨div_nonneg ht (sq_nonneg _), ?_⟩
  by_cases htδ : t ≤ δ
  · dsimp [cutInverseFn]
    rw [max_eq_left htδ]
    apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
    calc
      t ≤ δ := htδ
      _ = 1/δ*δ^2 := by field_simp
  · have htpos : 0 < t := hδ.trans (lt_of_not_ge htδ)
    have he : cutInverseFn δ t=1/t := by
      dsimp [cutInverseFn]
      rw [max_eq_right (le_of_not_ge htδ)]
      field_simp
    rw [he]
    exact one_div_le_one_div_of_le hδ (le_of_not_ge htδ)

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.cutInverseFn_bound := @_root_.OAI.MainGap.cutInverseFn_bound
