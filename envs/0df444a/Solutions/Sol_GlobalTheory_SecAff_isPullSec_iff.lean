-- Prove2me | solution 1 for GlobalTheory.SecAff.isPullSec_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:45.508938+00:00
-- url     : https://prove2.me/submissions/a85edf1d-058b-469b-a68f-2d1b4104128b

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
theorem _root_.solution (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L a T')) :
    IsPullSec A L a (h ▷ A) (whiskerRight_snd h A) s s' ↔
      SecM.ofSec A s' = pull A L a h (SecM.ofSec A s) :=
  ⟨fun H => Subtype.ext (funext H), fun H j => congrFun (congrArg Subtype.val H) j⟩
end GlobalTheory.SecAff
