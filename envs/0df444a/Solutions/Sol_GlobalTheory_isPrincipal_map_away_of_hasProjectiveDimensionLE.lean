-- Prove2me | solution 1 for GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:44.526916+00:00
-- url     : https://prove2.me/submissions/68a08a5c-6584-44c1-ac87-7e59f1ed5d81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Theorems.Thm_GlobalTheory_isStablyFree_baseChange_of_hasProjectiveDimensionLE
import Theorems.Thm_GlobalTheory_isPrincipal_of_isStablyFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R) (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ), HasProjectiveDimensionLE (ModuleCat.of R I) n → Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal := by
  intro R _ _ _ _ x R' _ _ _ I n h hp
  have hflat : Module.Flat R R' := IsLocalization.flat R' (Submonoid.powers x)
  have hb : IsBaseChange R' (Algebra.idealMap R' I) :=
    IsLocalizedModule.isBaseChange (Submonoid.powers x) R' _
  have hp' : Module.Projective R' (R' ⊗[R] I) := Module.Projective.of_equiv hb.equiv.symm
  have hs := isStablyFree_baseChange_of_hasProjectiveDimensionLE R R' n I h hp'
  have := Module.IsStablyFree.equiv hb.equiv
  have := Module.Finite.equiv hb.equiv
  exact isPrincipal_of_isStablyFree _
end GlobalTheory
