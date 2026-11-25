-- Prove2me | solution 1 for GlobalTheory.T.fromSpecStalk_comp_eq_of_agree_on_closedThickenings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:06.807795+00:00
-- url     : https://prove2.me/submissions/676843bc-e3fa-4ea6-b7b6-2044a4e2c5bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FromSpecStalkCompEqOfAgreeOnClosedThickenings
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FromSpecStalkCompEqOfAgreeOnClosedThickeningsStatement
import Theorems.Thm_GlobalTheory_ThickStalkEq_fromSpecStalk_comp_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G), (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → ∀ x : G.left, G.hom x = closedPoint R → G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := by
  first | exact @GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq | exact GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq | (intros; apply GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq <;> assumption)
end _root_.GlobalTheory.T
