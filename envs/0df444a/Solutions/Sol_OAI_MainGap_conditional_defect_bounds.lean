-- Prove2me | solution 1 for OAI.MainGap.conditional_defect_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:02:31.367568+00:00
-- url     : https://prove2.me/submissions/ab83cc9d-3e0a-4cbe-a5db-ef41a2489bd6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean:L141-L160
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.conditional_defect_bounds. The node keeps its source
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

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma conditional_defect_bounds {p y c : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1) :
    0 ≤ y*(1-star c*(p*p)*c)*y ∧
    y*(1-star c*(p*p)*c)*y ≤ y*y ∧ y*y ≤ 1 := by
  have hm : ‖p*c‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg p, norm_nonneg c])
  have hm₁ : star (p*c)*(p*c) ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg (p*c)]
  have he : star (p*c)*(p*c) = star c*(p*p)*c := by
    simp only [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc]
  have hn : 0 ≤ 1-star c*(p*p)*c := sub_nonneg.mpr (he ▸ hm₁)
  have hl : 1-star c*(p*p)*c ≤ 1 := sub_le_self _ (he ▸ star_mul_self_nonneg (p*c))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hy.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg hn y
  · simpa only [hy.isSelfAdjoint.star_eq, mul_one] using star_left_conjugate_le_conjugate hl y
  · apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ ?_).mp
    · rw [hy.isSelfAdjoint.norm_mul_self]
      nlinarith [norm_nonneg y]
    · simpa only [hy.isSelfAdjoint.star_eq] using star_mul_self_nonneg y

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


theorem solution : type_of% @_root_.OAI.MainGap.conditional_defect_bounds := @_root_.OAI.MainGap.conditional_defect_bounds
