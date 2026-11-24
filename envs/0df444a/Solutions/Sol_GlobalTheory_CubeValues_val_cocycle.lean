-- Prove2me | solution 1 for GlobalTheory.CubeValues.val_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:47.676748+00:00
-- url     : https://prove2.me/submissions/8254d3b8-145b-4686-8b69-27f2eb80a42e

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
theorem _root_.solution (hv : ValueRules) {L : LB X} (hL : L.IsLB) (i j k : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j ⊓ L.U k) (L.g j k).val =
      valAt' x (L.U i ⊓ L.U k) (L.g i k).val := by
  obtain ⟨-, -, hc⟩ := hL
  have hij : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  have hijk : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := (le_preimage_inf x _ _).2 ⟨hij, hk⟩
  have e := congrArg (fun w : Γ(X, L.U i ⊓ L.U j ⊓ L.U k)ˣ => valAt' x _ w.val) (hc i j k)
  rw [val_unit_mul x hv hijk, val_res x hv _ hijk, val_res x hv _ hijk, val_res x hv _ hijk] at e
  exact e
end GlobalTheory.CubeValues
