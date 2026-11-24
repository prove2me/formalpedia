-- Prove2me | solution 1 for GlobalTheory.CubeValues.val_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:24:53.301812+00:00
-- url     : https://prove2.me/submissions/89130f06-a0d9-4f55-92bf-80542665bfc8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_prod_zpow
import Theorems.Thm_GlobalTheory_CubeValues_val_res
import Theorems.Thm_GlobalTheory_CubeValues_val_pullU

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
theorem _root_.solution (hv : ValueRules) {Y : Scheme.{0}} (L : LB Y) {K : Type} [Fintype K]
    (φ : K → (X ⟶ Y)) (ε : K → ℤ) (j j' : K → L.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j) (hj' : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j') :
    valAt' x (L.wchart φ j ⊓ L.wchart φ j') ((L.LinComb φ ε).g j j').val =
      ∏ k, valAt' (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  have h2 : ⊤ ≤ x ⁻¹ᵁ (L.wchart φ j ⊓ L.wchart φ j') := (le_preimage_inf x _ _).2 ⟨hj, hj'⟩
  simp only [LB.LinComb]
  rw [val_unit_prod_zpow x hv h2]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  congr 1
  refine (val_res x hv _ h2 _).trans ?_
  exact val_pullU x hv (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k))
end GlobalTheory.CubeValues
