-- Prove2me | solution 1 for GlobalTheory.T.formallyUnramified_mul_invertible_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:32.109895+00:00
-- url     : https://prove2.me/submissions/b6dc8792-f3b0-4dc5-a4e3-9ac6693c9e90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FormallyUnramifiedMulInvertibleInteger
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FormallyUnramifiedMulInvertibleIntegerStatement
import Theorems.Thm_GlobalTheory_formallyUnramified_mulA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ), IsUnit (n : Γ(S, ⊤)) → FormallyUnramified (mulA G n).left := by
  first | exact @GlobalTheory.formallyUnramified_mulA | exact GlobalTheory.formallyUnramified_mulA | (intros; apply GlobalTheory.formallyUnramified_mulA <;> assumption)
end _root_.GlobalTheory.T
