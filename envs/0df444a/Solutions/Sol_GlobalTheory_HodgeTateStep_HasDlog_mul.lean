-- Prove2me | solution 1 for GlobalTheory.HodgeTateStep.HasDlog.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:21.503563+00:00
-- url     : https://prove2.me/submissions/a8c029b7-72d2-49bf-83c3-95b24a927028

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLeadingMinorsGeOfLeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_mul
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.HodgeTateStep
variable {O : Type} [CommRing O]
variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
namespace GlobalTheory.HodgeTateStep
namespace HasDlog
theorem _root_.solution {p : ℕ} {L : Type} {e : L → LieG G}
    {κ κ' : torsion G (p ^ 1) ⟶ Gm (Spec (CommRingCat.of O))} {y y' : L → O}
    (h : HasDlog p e κ y) (h' : HasDlog p e κ' y') : HasDlog p e (κ * κ') (y + y') := by
  refine ⟨fun T a b c hc => ?_, ?_⟩
  · rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, h.1 T a b c hc, h'.1 T a b c hc]
    exact mul_mul_mul_comm _ _ _ _
  · intro l R _ _ hp w hw
    rw [MonObj.comp_mul, GmPoints.unitOf_mul, Units.val_mul, h.2 l R hp w hw, h'.2 l R hp w hw]
    ext <;> simp [add_comm, Algebra.algebraMap_eq_smul_one, add_smul]
end HasDlog
end GlobalTheory.HodgeTateStep
