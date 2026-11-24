-- Prove2me | solution 1 for GlobalTheory.SelfCube.val_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:41:12.920798+00:00
-- url     : https://prove2.me/submissions/c2a42f6f-aa21-4696-81fb-9f26968f271d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_res
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_mul
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_ne_zero


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
open GlobalTheory GlobalTheory.SelfCube
open GlobalTheory.CubeValues
namespace GlobalTheory.SelfCube
theorem _root_.solution (hv : ValueRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (M L : LB X)
    (p q : M.ι × L.ι) (hp : ⊤ ≤ x ⁻¹ᵁ (M.U p.1 ⊓ L.U p.2)) (hq : ⊤ ≤ x ⁻¹ᵁ (M.U q.1 ⊓ L.U q.2)) :
    valAt' x ((LB.div M L).U p ⊓ (LB.div M L).U q) ((LB.div M L).g p q).val *
      valAt' x (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2).val =
      valAt' x (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1).val := by
  have hp' := (le_preimage_inf x _ _).1 hp
  have hq' := (le_preimage_inf x _ _).1 hq
  have hL : ⊤ ≤ x ⁻¹ᵁ (L.U p.2 ⊓ L.U q.2) := (le_preimage_inf x _ _).2 ⟨hp'.2, hq'.2⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ ((M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2)) :=
    (le_preimage_inf x _ _).2 ⟨hp, hq⟩
  obtain ⟨e, he⟩ := (hv X x).2.1 _ hW
  have hinv : ∀ u : Γ(X, (M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2))ˣ,
      valAt' x _ (u⁻¹).val = (valAt' x _ u.val)⁻¹ := fun u => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [he, he, ← map_mul, Units.inv_mul, map_one]
  unfold LB.div
  dsimp only
  rw [val_unit_mul x hv hW, hinv, val_res x hv _ hW, val_res x hv _ hW,
    inv_mul_cancel_right₀ (val_unit_ne_zero x hv hL _)]
end GlobalTheory.SelfCube
