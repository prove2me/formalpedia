-- Prove2me | solution 1 for OAI.MainGap.last_pair_kills_defect
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:37:34.5345+00:00
-- url     : https://prove2.me/submissions/96305f8d-05b3-4f7c-a89a-28d18a91a919

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/ChoicePairs.lean:L230-L245
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.last_pair_kills_defect. The node keeps its source
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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.ChoicePairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.choicePairsPartialOrder
attribute [local instance] OAI.MainGap.choicePairsStarOrderedRing
end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma last_pair_kills_defect {P B₃ B₄ : A} {h : ℝ} (hh : h ≠ 0)
    (hPB₄ : P * B₄ = B₄) (hcross : star B₃ * B₄ = 0)
    (hmod : star B₃ * B₃ = star B₄ * B₄)
    (hD : (B₃ * star B₃) * P = h • P) : P = 0 := by
  have hB₄ : h • B₄ = 0 := by
    calc
      h • B₄ = (h • P) * B₄ := by rw [smul_mul_assoc, hPB₄]
      _ = ((B₃ * star B₃) * P) * B₄ := by rw [hD]
      _ = B₃ * (star B₃ * B₄) := by rw [mul_assoc, hPB₄, mul_assoc]
      _ = 0 := by rw [hcross, mul_zero]
  have hB₄zero : B₄ = 0 := (smul_eq_zero.mp hB₄).resolve_left hh
  have hB₃zero : B₃ = 0 := (CStarRing.star_mul_self_eq_zero_iff B₃).mp (by
    rw [hmod, hB₄zero, star_zero, zero_mul])
  have hP : h • P = 0 := by simpa only [hB₃zero, zero_mul] using hD.symm
  exact (smul_eq_zero.mp hP).resolve_left hh

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.instPartialOrder_oAI
attribute [local instance] OAI.MainGap.instStarOrderedRing_oAI
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.last_pair_kills_defect := @_root_.OAI.MainGap.last_pair_kills_defect
