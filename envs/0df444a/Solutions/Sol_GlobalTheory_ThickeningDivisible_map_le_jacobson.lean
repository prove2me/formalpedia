-- Prove2me | solution 1 for GlobalTheory.ThickeningDivisible.map_le_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:56:15.560449+00:00
-- url     : https://prove2.me/submissions/68cf0567-df6f-4356-b7ce-ba196b3a1b41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecDivOfThickenings

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
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥) :
    I.map φ ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_jacobson_of_surjective hφ]
  exact hI.trans (Ideal.jacobson_mono bot_le)
end GlobalTheory.ThickeningDivisible
