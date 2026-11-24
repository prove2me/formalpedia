-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.exists_regOn_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:11.408261+00:00
-- url     : https://prove2.me/submissions/651a6e22-85ae-4c02-a240-0a4c48e927ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
import Theorems.Thm_GlobalTheory_ThetaModelGroup_RegOn_mono
import Theorems.Thm_GlobalTheory_ThetaModelGroup_exists_regOn_family
import Theorems.Thm_GlobalTheory_top_le_preimage_basicOpen_iff
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c
import Theorems.Thm_P2M_GlobalTheory_valAt__units_inv_d8876f25a60d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}
namespace GlobalTheory.ThetaModelGroup
theorem _root_.solution {κ : Type} [Finite κ] {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y}
    {s : κ → (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (h : ∀ c, RegAt y (s c)) (c : κ) (hc : s c y ≠ 0) :
    ∃ U : Y.left.Opens, ⊤ ≤ y.left ⁻¹ᵁ U ∧ (∀ y' : 𝟙_ (Over (Sp ℂ)) ⟶ Y, ⊤ ≤ y'.left ⁻¹ᵁ U → s c y' ≠ 0) ∧
      ∀ c', RegOn U (fun y' => s c' y' / s c y') := by
  obtain ⟨U, hU, hR⟩ := exists_regOn_family h
  obtain ⟨q, hq⟩ := hR c
  have e : Y.left.basicOpen q ≤ U := Y.left.basicOpen_le q
  have hne : ∀ y' : 𝟙_ (Over (Sp ℂ)) ⟶ Y, ⊤ ≤ y'.left ⁻¹ᵁ Y.left.basicOpen q → s c y' ≠ 0 := fun y' hy' => by
    rw [← hq y' (top_le_preimage_mono _ e hy')]
    exact (top_le_preimage_basicOpen_iff _ _ _).1 hy'
  refine ⟨Y.left.basicOpen q, (top_le_preimage_basicOpen_iff _ _ _).2 (by rwa [hq y hU]), hne, fun c' => ?_⟩
  obtain ⟨ρ, hρ⟩ := (hR c').mono e
  obtain ⟨u, hu⟩ : IsUnit (resG _ e q) := Y.left.toRingedSpace.isUnit_res_basicOpen q
  refine ⟨ρ * (u⁻¹).val, fun y' hy' => ?_⟩
  rw [valAt'_mul, valAt'_units_inv _ hy', hρ y' hy', hu, valAt'_res _ e q hy', hq y' (top_le_preimage_mono _ e hy')]
  exact (div_eq_mul_inv _ _).symm
end GlobalTheory.ThetaModelGroup
