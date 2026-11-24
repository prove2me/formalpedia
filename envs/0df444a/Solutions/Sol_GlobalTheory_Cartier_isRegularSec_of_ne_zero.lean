-- Prove2me | solution 1 for GlobalTheory.Cartier.isRegularSec_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:29.686801+00:00
-- url     : https://prove2.me/submissions/27c6f716-5c95-40d6-b78b-0215483c4fba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_ext_germ
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_germ
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_of_ne_zero

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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
theorem _root_.solution [IsIntegral X] {L : LB X} (s : L.Sec) {i : L.ι} (hi : s.f i ≠ 0) :
    IsRegularSec s := fun j => isRegularFn_iff_germ.2 fun x hx => by
  have hne : (L.U i : Set X).Nonempty := by
    by_contra h
    exact hi (ext_germ fun y hy => (h ⟨y, hy⟩).elim)
  obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (L.U i).isOpen (L.U j).isOpen hne ⟨x, hx⟩
  have hj : s.f j ≠ 0 := fun h0 => hi (germ_injective_of_isIntegral X y hy.1 (by
    have e := congrArg (X.presheaf.germ (L.U i ⊓ L.U j) y hy).hom (s.compat i j)
    rw [map_mul, germ_resG, germ_resG, h0, map_zero, mul_zero] at e
    exact e.trans (map_zero _).symm))
  exact isRegularFn_iff_germ.1 (isRegularFn_of_ne_zero hj) x hx
end GlobalTheory.Cartier
