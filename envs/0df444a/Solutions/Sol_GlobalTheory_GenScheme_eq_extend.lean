-- Prove2me | solution 1 for GlobalTheory.GenScheme.eq_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:16:22.058621+00:00
-- url     : https://prove2.me/submissions/1adb5108-66fb-4813-b432-cc9769c3c827

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_GenScheme_res_pb
import Theorems.Thm_GlobalTheory_GenScheme_pullU_eq
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
theorem _root_.solution {s : ∀ i : L.ι, Γ(Z, b ⁻¹ᵁ L.U i)ˣ} (hs : Compat L b s) (i : L.ι) :
    s i = extend L b j hj (res hj (s j)) i := by
  have h := congrArg (res (show b ⁻¹ᵁ L.U i ≤ b ⁻¹ᵁ (L.U j ⊓ L.U i) from
    fun x hx => ⟨hj trivial, hx⟩)) (hs j i)
  rw [map_mul, res_res, res_res, res_self, pullU_eq, res_pb] at h
  rw [h, extend, res_res]
end GlobalTheory.GenScheme
