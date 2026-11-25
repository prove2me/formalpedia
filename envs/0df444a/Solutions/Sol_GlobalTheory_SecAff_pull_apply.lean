-- Prove2me | solution 1 for GlobalTheory.SecAff.pull_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:10:08.670279+00:00
-- url     : https://prove2.me/submissions/27c24fc5-ce27-4cc6-9b9b-d1a3d578d3c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

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
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
namespace GlobalTheory.SecAff
theorem _root_.solution (h : T' ⟶ T) (s : SecM A L a T) (j : Fin 1 → L.ι) :
    (pull A L a h s).1 j = pa (h ▷ A).left (chart_le A L a h j) (s.1 j) := rfl
end GlobalTheory.SecAff
