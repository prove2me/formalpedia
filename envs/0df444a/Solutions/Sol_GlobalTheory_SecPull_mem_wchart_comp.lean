-- Prove2me | solution 1 for GlobalTheory.SecPull.mem_wchart_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:26.959335+00:00
-- url     : https://prove2.me/submissions/d28c99be-1716-4074-8ed7-d3a72ec4e680

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecPull
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.SecPull
theorem _root_.solution {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {h : Y' ⟶ Y}
    (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) {p : K → L.ι} {y : Y'}
    (hy : y ∈ LB.wchart L (fun k => φ' k ≫ F) p) : h y ∈ LB.wchart L φ p :=
  Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    show (h ≫ φ k) y ∈ L.U (p k)
    rw [← hc]; exact this
end GlobalTheory.SecPull
