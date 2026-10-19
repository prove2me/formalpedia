-- Prove2me | solution 1 for OAI.MainGap.lp_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:15:33.793767+00:00
-- url     : https://prove2.me/submissions/1c397fc6-32ea-4ac5-ba0b-300437e54168

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Products.lean:L126-L139
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.lp_nonneg_iff. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Products ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.boundedSlotsOrder
attribute [local instance] OAI.MainGap.boundedSlotsStarOrder
end MainGap

namespace MainGap
open scoped ENNReal
variable {I : Type*} {E : I → Type*} [∀ i, NonUnitalCStarAlgebra (E i)]
attribute [local instance] OAI.MainGap.productFactorOrder
attribute [local instance] OAI.MainGap.productFactorStarOrder
attribute [local instance] OAI.MainGap.boundedProductOrder
attribute [local instance] OAI.MainGap.boundedProductStarOrder
lemma lp_nonneg_iff (d : lp E ∞) : 0 ≤ d ↔ ∀ i, 0 ≤ d i := by
  constructor
  · intro hd i
    exact map_nonneg (lpEval i) hd
  · intro hd
    let v := lpBuild (fun i => CFC.sqrt (d i)) (Real.sqrt ‖d‖) (fun i => by
      rw [CFC.norm_sqrt (d i) (hd i)]
      exact Real.sqrt_le_sqrt (lp.norm_apply_le_norm ENNReal.top_ne_zero d i))
    have he : star v*v=d := by
      ext i
      change star (CFC.sqrt (d i))*CFC.sqrt (d i)=d i
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ (hd i)]
    rw [← he]
    exact star_mul_self_nonneg v

end MainGap

namespace MainGap
open scoped ENNReal
variable {I : Type*} {E : I → Type*} [∀ i, NonUnitalCStarAlgebra (E i)] [DecidableEq I]

end MainGap

namespace MainGap
open scoped ENNReal
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.sequenceFactorOrder
attribute [local instance] OAI.MainGap.sequenceFactorStarOrder
attribute [local instance] OAI.MainGap.boundedSequenceOrder
attribute [local instance] OAI.MainGap.boundedSequenceStarOrder
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open scoped ENNReal
attribute [local instance] OAI.MainGap.productFactorOrder
attribute [local instance] OAI.MainGap.productFactorStarOrder
attribute [local instance] OAI.MainGap.boundedProductOrder
attribute [local instance] OAI.MainGap.boundedProductStarOrder


theorem solution : type_of% @_root_.OAI.MainGap.lp_nonneg_iff := @_root_.OAI.MainGap.lp_nonneg_iff
