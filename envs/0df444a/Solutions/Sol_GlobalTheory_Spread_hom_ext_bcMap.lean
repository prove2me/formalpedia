-- Prove2me | solution 1 for GlobalTheory.Spread.hom_ext_bcMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:47:03.471975+00:00
-- url     : https://prove2.me/submissions/3ab682a1-abe8-4c17-a476-e24dd7a2ce09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_isSchemeTheoreticallyDominant_bcMap
import Theorems.Thm_GlobalTheory_ExtUnique_hom_ext_of_dominant


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
variable (A : Type) [CommRing A] [Algebra k A]
variable {A} (pZ : Z ⟶ Sp k)
namespace GlobalTheory.Spread
theorem _root_.solution [Flat pB] {R : Type} [CommRing R] [Algebra k R] (f : R →ₐ[k] A)
    (hf : Function.Injective f) {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s]
    {a b : pullback pB (spMap (algebraMap k R)) ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : bcMap pB f ≫ a = bcMap pB f ≫ b) : a = b :=
  have := isSchemeTheoreticallyDominant_bcMap pB f hf
  ExtUnique.hom_ext_of_dominant s h (bcMap pB f) hab
end GlobalTheory.Spread
