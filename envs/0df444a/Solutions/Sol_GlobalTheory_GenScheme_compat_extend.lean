-- Prove2me | solution 1 for GlobalTheory.GenScheme.compat_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:19:40.710828+00:00
-- url     : https://prove2.me/submissions/bcd5bda5-c8f8-4922-9475-f4cb4b441a3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_GenScheme_res_pb
import Theorems.Thm_GlobalTheory_GenScheme_pb_res
import Theorems.Thm_GlobalTheory_GenScheme_pullU_eq
import Theorems.Thm_GlobalTheory_GenScheme_res_res

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
theorem _root_.solution (hL : L.IsLB) (t : Γ(Z, ⊤)ˣ) : Compat L b (extend L b j hj t) := by
  intro i i'
  have h := congrArg (pb b (L.U j ⊓ L.U i ⊓ L.U i') (b ⁻¹ᵁ (L.U i ⊓ L.U i'))
    (fun x hx => ⟨⟨hj trivial, hx.1⟩, hx.2⟩)) (hL.cocycle j i i')
  rw [map_mul, pb_res, pb_res, pb_res] at h
  simp only [extend, map_mul, res_pb, res_res, pullU_eq]
  rw [← h, ← _root_.mul_assoc, _root_.mul_comm (pb b _ _ _ (L.g i i'))]
end GlobalTheory.GenScheme
