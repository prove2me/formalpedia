-- Prove2me | solution 1 for OAI.MainGap.cut_sandwich_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:13:07.221127+00:00
-- url     : https://prove2.me/submissions/10b05abe-e7d7-4842-ae07-c9a439503f98

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Hereditary.lean:L514-L538
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.cut_sandwich_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary

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

lemma cut_sandwich_lower {d : A} (hd : IsSelfAdjoint d) {ε : ℝ} (hε : 0 ≤ ε) :
    ε • (cut d ε * cut d ε) ≤ cut d ε * d * cut d ε := by
  let f : ℝ → ℝ := fun t => max (t - ε) 0
  have hf : Continuous f := (continuous_id.sub continuous_const).max continuous_const
  have hf0 : f 0 = 0 := by simp [f, max_eq_right (neg_nonpos.mpr hε)]
  have hid : cfcₙ (fun t : ℝ => t) d = d := cfcₙ_id ℝ d hd
  have hl : cfcₙ (fun t => ε * (f t * f t)) d = ε • (cut d ε * cut d ε) := by
    rw [cfcₙ_const_mul ε (fun t => f t * f t) d (hf.mul hf).continuousOn
      (by simp [hf0]), cfcₙ_mul f f d hf.continuousOn hf0 hf.continuousOn hf0]
    rfl
  have hu : cfcₙ (fun t => f t * t * f t) d = cut d ε * d * cut d ε := by
    rw [cfcₙ_mul (fun t => f t * t) f d (hf.mul continuous_id).continuousOn
      (by simp [hf0]) hf.continuousOn hf0,
      cfcₙ_mul f (fun t => t) d hf.continuousOn hf0 continuousOn_id rfl, hid]
    rfl
  rw [← hl, ← hu]
  apply (cfcₙ_le_iff _ _ d (continuous_const.mul (hf.mul hf)).continuousOn
    ((hf.mul continuous_id).mul hf).continuousOn (by simp [hf0]) (by simp [hf0]) hd).mpr
  intro t _
  by_cases ht : ε ≤ t
  · calc
      ε * (f t * f t) ≤ t * (f t * f t) :=
        mul_le_mul_of_nonneg_right ht (mul_self_nonneg _)
      _ = f t * t * f t := by ring
  · simp [f, max_eq_right (by linarith : t - ε ≤ 0)]

end Order

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.cut_sandwich_lower := @_root_.OAI.MainGap.cut_sandwich_lower
