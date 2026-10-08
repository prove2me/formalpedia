-- Prove2me | solution 1 for MazurProof.TateOrder13.exists_tate_parameters_of_order_thirteen
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T21:50:46.878984+00:00
-- url     : https://prove2.me/submissions/04f7db61-866a-42e9-9c2f-f8c7f4ec623a

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.TateOrder13
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateNFDivision_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateNormalFormBridge_p0
import Definitions.Def_MazurN13_KeystoneInterface
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateOrder13_p0

set_option autoImplicit false

open Polynomial
open scoped WeierstrassCurve.Affine
namespace MazurProof.TateOrder13
open Scratch.TateZ2xZ10Reduction
noncomputable section
theorem _root_.solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 13) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
        addOrderOf (tateOrigin b c) = 13 ∧
          b ≠ 0 ∧ TateNFDivision.F13 b c = 0 := by
  obtain ⟨b, c, hEll, hord, hb⟩ :=
    TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three
      E P 13 (by norm_num) hP
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have horigin : addOrderOf (tateOrigin b c) = 13 := by
    rw [tateOrigin_eq_normalized_origin]
    exact hord
  exact ⟨b, c, inferInstance, horigin, hb,
    F13_eq_zero_of_tateOrigin_order_thirteen b c hb horigin⟩
end
end MazurProof.TateOrder13
