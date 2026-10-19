-- Prove2me | solution 1 for OAI.MainGap.Her_cut_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:29:58.607788+00:00
-- url     : https://prove2.me/submissions/82b079bf-14dc-488a-9c44-f1c0a51445da

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Signal.lean:L19-L32
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.Her_cut_lower. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal
import Theorems.Thm_OAI_MainGap_cut_sandwich_lower

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

namespace RegularTransport
variable {h v : A} (T : RegularTransport h v)

end RegularTransport

section Order
variable [PartialOrder A] [StarOrderedRing A]

lemma cut_nonneg (d : A) (ε : ℝ) : 0 ≤ cut d ε := by
  exact cfcₙ_nonneg (fun _ _ => le_max_right _ _)

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Signal ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalCutPartialOrder
attribute [local instance] OAI.MainGap.signalCutStarOrderedRing
lemma Her_cut_lower {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 ≤ δ)
    {p : A} (hp : p ∈ Her (cut a δ)) :
    δ • (star p * p) ≤ star p * a * p := by
  have hc : IsClosed {p : A | δ • (star p * p) ≤ star p * a * p} :=
    isClosed_le (by fun_prop) (by fun_prop)
  apply closure_minimal (s := Set.range (fun w : A => cut a δ * w * star (cut a δ))) _ hc hp
  rintro _ ⟨w, rfl⟩
  change δ • (star (cut a δ * w * star (cut a δ)) *
      (cut a δ * w * star (cut a δ))) ≤
    star (cut a δ * w * star (cut a δ)) * a * (cut a δ * w * star (cut a δ))
  have hh := star_left_conjugate_le_conjugate (cut_sandwich_lower ha.isSelfAdjoint hδ)
    (w * cut a δ)
  simpa only [star_mul, (cut_nonneg a δ).isSelfAdjoint.star_eq,
    mul_smul_comm, smul_mul_assoc, mul_assoc] using hh

end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalComparisonPartialOrder
attribute [local instance] OAI.MainGap.signalComparisonStarOrderedRing
attribute [local instance] OAI.MainGap.signalOperatorPartialOrder
attribute [local instance] OAI.MainGap.signalOperatorStarOrderedRing
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalCoefficientPartialOrder
attribute [local instance] OAI.MainGap.signalCoefficientStarOrderedRing
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalProductsPartialOrder
attribute [local instance] OAI.MainGap.signalProductsStarOrderedRing
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.signalCutPartialOrder
attribute [local instance] OAI.MainGap.signalCutStarOrderedRing


theorem solution : type_of% @_root_.OAI.MainGap.Her_cut_lower := @_root_.OAI.MainGap.Her_cut_lower
