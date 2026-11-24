-- Prove2me | solution 1 for GlobalTheory.SerreField.exists_odd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:30.99205+00:00
-- url     : https://prove2.me/submissions/79564e29-97b8-4a1f-985c-f0d0add18bff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsOddNeZero

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SerreField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.MulPull
namespace GlobalTheory.SerreField
theorem _root_.solution (K : Type) [Field K] : ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ (n : K) ≠ 0 := by
  by_cases h : ((5 : ℕ) : K) = 0
  · refine ⟨11, by decide, by decide, fun h' => ?_⟩
    have : (1 : K) = ((11 : ℕ) : K) - 2 * ((5 : ℕ) : K) := by push_cast; ring
    rw [h, h'] at this
    simp at this
  · exact ⟨5, by decide, le_rfl, h⟩
end GlobalTheory.SerreField
