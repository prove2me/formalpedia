-- Prove2me | solution 1 for GlobalTheory.SecAff.cocycle_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:49.296254+00:00
-- url     : https://prove2.me/submissions/1eac66d1-5806-49d0-a58b-00e10d9a8a5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_cocycle


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
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}
namespace GlobalTheory.SecAff
theorem _root_.solution {M : LB X} (hM : M.IsLB) (i j k : M.ι) {W : X.Opens}
    (h₁ : W ≤ M.U i ⊓ M.U j) (h₂ : W ≤ M.U j ⊓ M.U k) (h₃ : W ≤ M.U i ⊓ M.U k) :
    rs h₁ (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs h₂ (M.g j k : Γ(X, M.U j ⊓ M.U k)) =
      rs h₃ (M.g i k : Γ(X, M.U i ⊓ M.U k)) :=
  congrArg Units.val (LB.res_cocycle hM i j k h₁ h₂ h₃)
end GlobalTheory.SecAff
