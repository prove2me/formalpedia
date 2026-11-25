-- Prove2me | solution 1 for GlobalTheory.GenScheme.res_extend_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:58.109126+00:00
-- url     : https://prove2.me/submissions/a41594f6-04e5-492c-8e39-10bca4e36eba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_GenScheme_res_pb
import Theorems.Thm_GlobalTheory_GenScheme_pb_res
import Theorems.Thm_GlobalTheory_GenScheme_res_res
import Theorems.Thm_GlobalTheory_GenScheme_res_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory
open GlobalTheory.GenScheme
variable {B Z : Scheme.{0}} (L : LB B) (b : Z ⟶ B)
variable (j : L.ι) (hj : ⊤ ≤ b ⁻¹ᵁ L.U j)
variable {L}
namespace GlobalTheory.GenScheme
theorem _root_.solution (hL : L.IsLB) (t : Γ(Z, ⊤)ˣ) : res hj (extend L b j hj t j) = t := by
  have h := congrArg (pb b (L.U j) ⊤ hj) (hL.g_self j)
  rw [pb_res, map_one] at h
  simp only [extend, map_mul, res_pb, res_res, res_self]
  rw [h, _root_.one_mul]
end GlobalTheory.GenScheme
