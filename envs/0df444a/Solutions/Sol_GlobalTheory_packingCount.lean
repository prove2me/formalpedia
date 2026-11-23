-- Prove2me | solution 1 for GlobalTheory.packingCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:44.746801+00:00
-- url     : https://prove2.me/submissions/272f1657-5516-41f5-9640-3d6bb85af101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Theorems.Thm_GlobalTheory_finset_card_le_of_separated
import Theorems.Thm_GlobalTheory_one_add_two_mul_div_pow_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount
  intro n P δ R hδ hR hP hsep
  have h1 := _root_.GlobalTheory.finset_card_le_of_separated P hδ (hδ.le.trans hR) 0
    (by simpa [dist_zero_right] using hP) (fun x hx y hy hxy => hsep x hx y hy hxy)
  rw [finrank_euclideanSpace_fin] at h1
  exact h1.trans (_root_.GlobalTheory.one_add_two_mul_div_pow_le hδ hR n)
end _root_.GlobalTheory
end GlobalTheory
