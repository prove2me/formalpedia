-- Prove2me | solution 1 for OAI.MainGap.cut_sqrt_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:59:42.631094+00:00
-- url     : https://prove2.me/submissions/c41a8ae1-09ba-4deb-8fae-069ba3772166

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean:L87-L109
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.cut_sqrt_lower. The node keeps its source
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

lemma cut_sqrt_lower {d : A} (hd : 0 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ) :
    δ • cut d δ ≤ CFC.sqrt (cut d δ) * d * CFC.sqrt (cut d δ) := by
  let f : ℝ → ℝ := fun t => max (t-δ) 0
  have hf : Continuous f := (continuous_id.sub continuous_const).max continuous_const
  have hf0 : f 0=0 := by simp [f, max_eq_right (neg_nonpos.mpr hδ)]
  have hl : δ • cut d δ ≤ d * cut d δ := by
    change δ • cfcₙ f d ≤ d * cfcₙ f d
    have hu : cfcₙ (fun t => t*f t) d = d*cfcₙ f d := by
      rw [cfcₙ_mul (fun t : ℝ => t) f d continuousOn_id rfl hf.continuousOn hf0]
      exact congrArg (fun x => x*cfcₙ f d) (cfcₙ_id ℝ d hd.isSelfAdjoint)
    rw [← cfcₙ_const_mul δ f d hf.continuousOn hf0, ← hu]
    apply (cfcₙ_le_iff _ _ d (continuous_const.mul hf).continuousOn
      (continuous_id.mul hf).continuousOn (by simp [hf0]) (by simp [hf0]) hd.isSelfAdjoint).mpr
    intro t _
    by_cases ht : δ ≤ t
    · exact mul_le_mul_of_nonneg_right ht (le_max_right _ _)
    · simp [f, max_eq_right (by linarith : t-δ ≤ 0)]
  have hc : Commute (cut d δ) d := (Commute.refl d).cfcₙ_real f
  have hs : Commute (CFC.sqrt (cut d δ)) d := hc.cfcₙ_nnreal NNReal.sqrt
  calc
    δ • cut d δ ≤ d * cut d δ := hl
    _ = CFC.sqrt (cut d δ) * d * CFC.sqrt (cut d δ) := by
      rw [hs.eq, mul_assoc, CFC.sqrt_mul_sqrt_self (cut d δ) (cut_nonneg d δ)]

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


theorem solution : type_of% @_root_.OAI.MainGap.cut_sqrt_lower := @_root_.OAI.MainGap.cut_sqrt_lower
