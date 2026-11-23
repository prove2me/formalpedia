-- Prove2me | solution 1 for GlobalTheory.RelConstThickening.res_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:22.528799+00:00
-- url     : https://prove2.me/submissions/f8d2db1e-410c-464f-a0b5-c23812cc94d3

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Theorems.Thm_GlobalTheory_RelConstThickening_res_constFn
import Theorems.Thm_GlobalTheory_RelConstThickening_res_app

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.RelConstThickening
variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {π : Y' ⟶ Sp R} {ρ : Y' ⟶ Y} {ε : R}
namespace GlobalTheory.RelConstThickening
theorem _root_.solution {U V : Y.Opens} (h : V ≤ U) (h' : ρ ⁻¹ᵁ V ≤ ρ ⁻¹ᵁ U) (a b : Γ(Y, U)) :
    (Y'.presheaf.map (homOfLE h').op).hom ((ρ.app U).hom a + constFn π _ ε * (ρ.app U).hom b) =
      (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom a) +
        constFn π _ ε * (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom b) := by
  rw [map_add, map_mul, res_app ρ h, res_app ρ h, res_constFn]
end GlobalTheory.RelConstThickening
