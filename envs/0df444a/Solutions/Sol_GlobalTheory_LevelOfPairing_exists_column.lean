-- Prove2me | solution 1 for GlobalTheory.LevelOfPairing.exists_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:28.447597+00:00
-- url     : https://prove2.me/submissions/e0d7db7f-71f9-4998-9f09-52e74dbfacdf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing

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
open GlobalTheory GlobalTheory.LevelOfPairing
variable {G U : Type} [Group G] [CommGroup U] {R : G → G → U → Prop} {M : ℕ}
namespace GlobalTheory.LevelOfPairing
theorem _root_.solution (g : ℕ) (i : Fin (2 * g)) :
    ∃ j : Fin (2 * g), (stdSymp g i j = 1 ∨ stdSymp g i j = -1) ∧ ∀ i', i' ≠ i → stdSymp g i' j = 0 := by
  have hi := i.2
  by_cases h : (i : ℕ) < g
  · refine ⟨⟨i + g, by omega⟩, Or.inl (by simp [stdSymp, h]), fun i' hi' => ?_⟩
    have : (i' : ℕ) ≠ i := fun e => hi' (Fin.ext e)
    have := i'.2
    unfold stdSymp
    rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
  · refine ⟨⟨i - g, by omega⟩, Or.inr ?_, fun i' hi' => ?_⟩
    · unfold stdSymp
      rw [if_neg (by simp only; omega), if_pos (by simp only; omega)]
    · have : (i' : ℕ) ≠ i := fun e => hi' (Fin.ext e)
      have := i'.2
      unfold stdSymp
      rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
end GlobalTheory.LevelOfPairing
