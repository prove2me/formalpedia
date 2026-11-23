-- Prove2me | solution 1 for GlobalTheory.CubeValues.val_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:38.768293+00:00
-- url     : https://prove2.me/submissions/268c98c5-bb11-4fda-9623-c3bbca05e715

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_mul
import Theorems.Thm_GlobalTheory_CubeValues_val_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.CubeValues
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.CubeValues
theorem _root_.solution (hv : ValueRules) {L : LB X} (t : L.Gen) (ht : t.IsGen) (i j : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U i) (t.s i).val =
      valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j) (t.s j).val := by
  have hij : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  have e := congrArg (fun w : Γ(X, L.U i ⊓ L.U j)ˣ => valAt' x (L.U i ⊓ L.U j) w.val) (ht i j)
  rw [val_unit_mul x hv hij, val_res x hv _ hij, val_res x hv _ hij] at e
  exact e
end GlobalTheory.CubeValues
