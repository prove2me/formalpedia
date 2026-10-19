-- Prove2me | solution 1 for OAI.MainGap.conditional_q_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:06:00.461609+00:00
-- url     : https://prove2.me/submissions/38d54720-2e4e-4de4-80c0-5f629ce38f14

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean:L219-L247
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.conditional_q_zero. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_conditional_defect_bounds
import Theorems.Thm_OAI_MainGap_cut_sqrt_lower
import Theorems.Thm_OAI_MainGap_norm_sub_cut_le

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

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma conditional_q_zero {p y c : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : y*cut (y*(1-star c*(p*p)*c)*y) δ*y=0) :
    ‖y*(1-star c*(p*p)*c)*y‖ ≤ δ := by
  let d := y*(1-star c*(p*p)*c)*y
  let h := cut d δ
  let s := CFC.sqrt h
  have hs : IsSelfAdjoint s := (CFC.sqrt_nonneg h).isSelfAdjoint
  have hd := conditional_defect_bounds hp hy hpn hyn hcn
  have hzz : (y*s)*star (y*s) = y*h*y := by
    simp only [star_mul, hs.star_eq, hy.isSelfAdjoint.star_eq]
    calc
      y*s*(s*y)= y*(s*s)*y := by simp only [mul_assoc]
      _ = y*h*y := by rw [show s*s=h from CFC.sqrt_mul_sqrt_self h (cut_nonneg d δ)]
  have hz : y*s=0 := (CStarRing.mul_star_self_eq_zero_iff _).mp (hzz.trans hq)
  have hl : δ • h ≤ 0 := by
    calc
      δ • h ≤ s*d*s := cut_sqrt_lower hd.1 hδ.le
      _ ≤ s*(y*y)*s := by
        simpa only [hs.star_eq] using star_left_conjugate_le_conjugate hd.2.1 s
      _ = star (y*s)*(y*s) := by
        simp only [star_mul, hs.star_eq, hy.isSelfAdjoint.star_eq, mul_assoc]
      _ = 0 := by rw [hz, star_zero, mul_zero]
  have hsm : δ • h=0 := le_antisymm hl (smul_nonneg hδ.le (cut_nonneg d δ))
  have hh : h=0 := (smul_eq_zero.mp hsm).resolve_left (ne_of_gt hδ)
  have hb := norm_sub_cut_le hd.1 hδ.le
  change ‖d-h‖ ≤ δ at hb
  simpa only [hh, sub_zero] using hb

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.conditional_q_zero := @_root_.OAI.MainGap.conditional_q_zero
