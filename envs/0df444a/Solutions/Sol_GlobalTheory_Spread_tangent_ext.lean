-- Prove2me | solution 1 for GlobalTheory.Spread.tangent_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:22:20.27675+00:00
-- url     : https://prove2.me/submissions/24a2ca9c-2c9a-46f3-ba29-2c196427c0fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_point_ext
import Theorems.Thm_GlobalTheory_Spread_dualMapR_injective

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
open Chart
namespace GlobalTheory.Spread
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (hf : Function.Injective f)
    {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s] {a b : Sp (DualNumber R) ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : spMap (dualMapR f) ≫ a = spMap (dualMapR f) ≫ b) : a = b :=
  point_ext _ (dualMapR_injective hf) s h hab
end GlobalTheory.Spread
