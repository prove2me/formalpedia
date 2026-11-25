-- Prove2me | solution 1 for GlobalTheory.IntAct.rosatiAdj_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:10.845284+00:00
-- url     : https://prove2.me/submissions/5b92bd4f-5b8a-475d-9c3c-27551f022197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RosatiAdjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RosatiAdjOfPoints
import Theorems.Thm_GlobalTheory_IntAct_rosatiAdj_of_points
import Theorems.Thm_GlobalTheory_IntAct_isGen_oneGen

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
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.IntAct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
namespace GlobalTheory.IntAct
theorem _root_.solution (hL : L.IsLB) : RosatiAdj A L (𝟙 A) (𝟙 A) :=
  rosatiAdj_of_points hL _ _ fun _ => ⟨⊤, trivial, fun T x y _ =>
    ⟨PEmpty, inferInstance, _, _, LB.oneGen L, isGen_oneGen L, fun V _ k => by
      rw [Category.comp_id, Category.comp_id, Fintype.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel⟩⟩
end GlobalTheory.IntAct
