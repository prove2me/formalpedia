-- Prove2me | solution 1 for GlobalTheory.ThickeningDivisible.cst_comp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:27:43.498809+00:00
-- url     : https://prove2.me/submissions/c8349c16-e7b9-4860-801b-e4b2161ab139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecDivOfThickenings
import Theorems.Thm_GlobalTheory_ThickeningDivisible_gs_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
open ThickeningDetermines ThickeningClosed
namespace GlobalTheory.ThickeningDivisible
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {r : R}
    (hr : φ r = 0) {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R')) (z : Z) :
    cst (q ≫ Spec.map (CommRingCat.ofHom φ)) z r = 0 := by
  have h : ((Spec.map (CommRingCat.ofHom φ)).app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
    have := congrArg (fun k ↦ k.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [hr, map_zero] at this
    exact this.symm
  rw [cst, ← gs_pull q _ z ⊤ trivial, h, gs_zero]
end GlobalTheory.ThickeningDivisible
