-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZSlope.propZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:54:14.293863+00:00
-- url     : https://prove2.me/submissions/cac70e36-a3de-4c1a-9714-f4568c1b449b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
namespace PropZSlope
theorem _root_.solution (h : PropZSlope) : PropZ := by
  intro O _ _ _ ϖ hϖ Z f D hD sig hs
  obtain ⟨ρ, hρ⟩ := h O ϖ hϖ Z f D hD sig hs
  refine ⟨ρ.den, ρ.num, ρ.den_pos, hρ _ _ ρ.den_pos ?_⟩
  rw [mul_comm]
  exact (Rat.mul_den_eq_num ρ).symm
end PropZSlope
end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
