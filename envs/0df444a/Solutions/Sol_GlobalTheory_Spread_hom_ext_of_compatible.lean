-- Prove2me | solution 1 for GlobalTheory.Spread.hom_ext_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:11:15.488394+00:00
-- url     : https://prove2.me/submissions/54dce4d2-22c3-4eb4-95b1-a427327ff6ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_dominant_of_compatible
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
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
namespace GlobalTheory.Spread
theorem _root_.solution (R : Subalgebra k A)
    {j : pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R))}
    (h₁ : j ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R.val.toRingHom)
    {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s]
    {a b : pullback pB (spMap (algebraMap k R)) ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : j ≫ a = j ≫ b) : a = b :=
  have := (dominant_of_compatible pB R h₁ h₂).2
  ExtUnique.hom_ext_of_dominant s h j hab
end GlobalTheory.Spread
