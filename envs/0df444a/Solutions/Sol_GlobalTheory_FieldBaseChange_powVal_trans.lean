-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.powVal_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:19.970228+00:00
-- url     : https://prove2.me/submissions/4635c0f2-7738-4fcb-b4ce-d2a3373d85dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {Y Y' X₁ X₂ Z₁ Z₂ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution {L : LB X₁} {g : Z₁ ⟶ X₁} {k : ℤ}
    (a : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) (r : Z ⟶ Z₁) (z : Z) {i j : L.ι}
    (hi : g (r z) ∈ L.U i) (hj : g (r z) ∈ L.U j) :
    powVal a r z i = (gm (r ≫ g) z _ (L.g i j) ^ k).val * powVal a r z j :=
  (sec_trans a r z (mem_wchart.2 fun _ => hi) (mem_wchart.2 fun _ => hj)).trans
    (congrArg (fun u : (Z.presheaf.stalk z)ˣ => u.val * _) (Fin.prod_univ_one _))
end GlobalTheory.FieldBaseChange
