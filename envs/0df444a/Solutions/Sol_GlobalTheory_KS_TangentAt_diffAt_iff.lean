-- Prove2me | solution 1 for GlobalTheory.KS.TangentAt.diffAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:01.768476+00:00
-- url     : https://prove2.me/submissions/c362320d-feed-4854-b95e-3432fe4f034d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationUniformisedAbelianVarietyUniqueVec
import Theorems.Thm_GlobalTheory_KS_TangentAt_tr_neg_tr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.TangentAt
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
namespace GlobalTheory.KS.TangentAt
theorem _root_.solution (v : Sp (DualNumber ℂ) ⟶ A.left) (z w : Fin g → ℂ) :
    DiffAt u v z w ↔ DiffAt u (v ≫ (tr u (-z)).left) 0 w := by
  constructor
  · intro h
    have h' := DiffAt.tr u h (-z)
    rwa [neg_add_cancel] at h'
  · intro h
    have h' := DiffAt.tr u h z
    rwa [add_zero, Category.assoc, ← Over.comp_left, tr_neg_tr, Over.id_left, Category.comp_id] at h'
end GlobalTheory.KS.TangentAt
