-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsFnT.isValueAt_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:29.433086+00:00
-- url     : https://prove2.me/submissions/6d08dfcb-72bc-412e-9be5-087a17335d6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnAt_isValueAt_origin_iff
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnT_isValueAt_origin_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable {u}
namespace GlobalTheory.ThetaFn
namespace IsFnT
theorem _root_.solution (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))}
    (hrig : u.IsRig rig) {k : ℤ} {s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u k s θ) :
    IsValueAt A L k s 1 (rigT A L rig (baseOver (Sp ℂ)) k) (constT (θ 0)) :=
  (h.isValueAt_origin_iff hL hrig _).2 (numT_constT _)
end IsFnT
end GlobalTheory.ThetaFn
