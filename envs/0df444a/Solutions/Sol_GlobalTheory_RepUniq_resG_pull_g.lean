-- Prove2me | solution 1 for GlobalTheory.RepUniq.resG_pull_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:04:38.164805+00:00
-- url     : https://prove2.me/submissions/013b06b0-9dcb-4a44-98da-73dc535dcb5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace
variable {σ : Type} {T T' X X' X'' : Scheme.{0}}
variable {M : LB X} {th : σ → M.Sec} {M' : LB X'} {th' : σ → M'.Sec} {M'' : LB X''} {th'' : σ → M''.Sec}
  {x : T ⟶ X} {x' : T ⟶ X'} {x'' : T ⟶ X''}
namespace GlobalTheory.RepUniq
theorem _root_.solution (x : T ⟶ X) (j k : PUnit → M.ι) {W : T.Opens} (hj : W ≤ (M.pull x).U j)
    (hk : W ≤ (M.pull x).U k) :
    resG T (le_inf hj hk) ((M.pull x).g j k).val =
      (x.appLE (M.U (j ⟨⟩) ⊓ M.U (k ⟨⟩)) W
        (le_inf (hj.trans (pull_U M x j).le) (hk.trans (pull_U M x k).le))).hom (M.g (j ⟨⟩) (k ⟨⟩)).val := by
  refine (congrArg (fun u => resG T (le_inf hj hk) (Units.val u)) (pull_g M x j k)).trans ?_
  exact resG_resG _ _ _
end GlobalTheory.RepUniq
