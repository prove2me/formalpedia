-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.isFracImage_V
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:53:04.28881+00:00
-- url     : https://prove2.me/submissions/83f2e987-37ca-4046-aa21-99cf5741e2db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l)
variable {c}
namespace GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
theorem _root_.solution (W : ValuationSubring ℂ) : IsFracImage (c.V W).subtype := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, 1, by simp, by simp⟩
  rcases (c.V W).mem_or_inv_mem x with h | h
  · exact ⟨⟨x, h⟩, 1, by simp, by simp⟩
  · exact ⟨1, ⟨x⁻¹, h⟩, by simpa using hx, by simpa using mul_inv_cancel₀ hx⟩
end GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
