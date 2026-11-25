-- Prove2me | solution 1 for GlobalTheory.AbLaw.isLB_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:59:10.264556+00:00
-- url     : https://prove2.me/submissions/350d2bcc-baf6-4219-a98f-bc8a8a40465c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Theorems.Thm_GlobalTheory_AbLaw_isLB_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_div


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
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.AbLaw
theorem _root_.solution {M H : LB X} (hM : M.IsLB) (hH : H.IsLB) (t : ℤ) : (tw M H t).IsLB :=
  LB.isLB_div hM (isLB_pw hH (-t))
end GlobalTheory.AbLaw
