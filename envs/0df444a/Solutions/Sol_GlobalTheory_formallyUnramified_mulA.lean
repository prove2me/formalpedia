-- Prove2me | solution 1 for GlobalTheory.formallyUnramified_mulA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:49:47.937317+00:00
-- url     : https://prove2.me/submissions/759dea50-37af-4169-b7c3-64e1c6091675

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FormallyUnramifiedMulInvertibleInteger
import Theorems.Thm_GlobalTheory_MulUnramified_comp_mulN
import Theorems.Thm_GlobalTheory_formallyUnramified_mulN


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulA G n).left := by
  have h : mulN G n = mulA G n :=
    (Category.id_comp _).symm.trans (MulUnramified.comp_mulN G (𝟙 G) n)
  rw [← h]
  exact formallyUnramified_mulN S G n hn
end GlobalTheory
