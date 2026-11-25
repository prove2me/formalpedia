-- Prove2me | solution 1 for GlobalTheory.Spread.isSchemeTheoreticallyDominant_bcMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:26.346504+00:00
-- url     : https://prove2.me/submissions/6155597b-4cbe-43e9-90cc-910be4cb57a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_ExtUnique_isSchemeTheoreticallyDominant_spec_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
variable {R R' A : Type} [CommRing R] [CommRing R'] [CommRing A] [Algebra k R] [Algebra k R']
  [Algebra k A]
namespace GlobalTheory.Spread
theorem _root_.solution [Flat pB] (f : R →ₐ[k] A) (hf : Function.Injective f) :
    IsSchemeTheoreticallyDominant (bcMap pB f) := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective
    (CommRingCat.ofHom f.toRingHom) hf
  exact .of_isPullback (isPullback_bcMap pB f).flip
end GlobalTheory.Spread
