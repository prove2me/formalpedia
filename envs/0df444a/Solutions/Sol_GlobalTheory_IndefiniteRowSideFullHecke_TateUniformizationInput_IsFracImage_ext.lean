-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput.IsFracImage.ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:06.681182+00:00
-- url     : https://prove2.me/submissions/f8a3bd13-645b-4e58-8070-aee5577b9867

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
namespace IsFracImage
theorem _root_.solution {O K : Type} [CommRing O] [Field K] {β : O →+* c.F} (h : IsFracImage β)
    {gam gam' : c.F →+* K} (hgam : ∀ x, gam (β x) = gam' (β x)) : gam = gam' := by
  ext x
  obtain ⟨a, s, hs, hx⟩ := h x
  have h1 : gam x * gam (β s) = gam' x * gam (β s) := by
    rw [← map_mul, hx, hgam a, hgam s, ← map_mul, hx]
  exact mul_right_cancel₀ ((map_ne_zero gam).mpr hs) h1
end IsFracImage
end GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
