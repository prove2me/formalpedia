-- Prove2me | solution 1 for GlobalTheory.SecAff.sec_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:54.57728+00:00
-- url     : https://prove2.me/submissions/464bddae-42f3-4cbd-9ef8-675046562095

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_rs_rs

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
theorem _root_.solution {M : LB X} (s : LB.Sec M) (i j : M.ι) {W : X.Opens} (hi : W ≤ M.U i)
    (hj : W ≤ M.U j) :
    rs hi (s.f i) = rs (le_inf hi hj) (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs hj (s.f j) := by
  have : rs inf_le_left (s.f i) = (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs inf_le_right (s.f j) :=
    s.compat i j
  have := congrArg (rs (le_inf hi hj)) this
  rwa [map_mul, rs_rs, rs_rs] at this
end GlobalTheory.SecAff
