-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence.le_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:50:47.024771+00:00
-- url     : https://prove2.me/submissions/c9a2f51b-5ac4-44a3-b329-36c3b9ab5f41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FractionLevelCorrespondence

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
variable {X X' T : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
theorem _root_.solution {L' : LB X'} {L : LB X} {φ : X' ⟶ X} {a : K → (T ⟶ X')} {b : K → (T ⟶ X)}
    {ε : K → ℤ} (hb : ∀ k, b k = a k ≫ φ) {j' : K → L'.ι} {j : K → L.ι} {V : T.Opens}
    (h' : V ≤ (LB.LinComb L' a ε).U j') (h : V ≤ (LB.LinComb L b ε).U j) (k : K) :
    V ≤ a k ⁻¹ᵁ ((L.pull φ).U (fun _ => j k) ⊓ L'.U (j' k)) := by
  intro p hp
  have h1 : p ∈ b k ⁻¹ᵁ L.U (j k) := LB.wchart_le L b j k (h hp)
  have h2 : p ∈ a k ⁻¹ᵁ L'.U (j' k) := LB.wchart_le L' a j' k (h' hp)
  rw [hb k] at h1
  exact ⟨Set.mem_iInter.2 fun _ => h1, h2⟩
end GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
