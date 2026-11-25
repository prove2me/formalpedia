-- Prove2me | solution 1 for GlobalTheory.Spread.point_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:42.388637+00:00
-- url     : https://prove2.me/submissions/3933625e-ca89-4df8-a433-df26e80bb644

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_ExtUnique_hom_ext_of_dominant
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
variable (A : Type) [CommRing A] [Algebra k A]
variable {A} (pZ : Z ⟶ Sp k)
namespace GlobalTheory.Spread
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (hf : Function.Injective f)
    {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s] {a b : Sp R ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : spMap f ≫ a = spMap f ≫ b) : a = b :=
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  ExtUnique.hom_ext_of_dominant s h (spMap f) hab
end GlobalTheory.Spread
