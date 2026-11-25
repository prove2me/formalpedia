-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.add_eq_of_ordered
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:38:06.72931+00:00
-- url     : https://prove2.me/submissions/f3157c33-c99a-4500-9de9-748d68d31355

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen

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
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution {κ G : Type} [LinearOrder κ] [AddCommGroup G] (F : κ → κ → G)
    (h0 : ∀ a, F a a = 0) (hs : ∀ a b, F b a = -F a b)
    (h : ∀ a b c, a < b → b < c → F a b + F b c = F a c) (a b c : κ) : F a b + F b c = F a c := by
  have key : ∀ a b c, a < b → F a b + F b c = F a c := by
    intro a b c hab
    rcases lt_trichotomy b c with hbc | rfl | hbc
    · exact h a b c hab hbc
    · rw [h0, add_zero]
    · rcases lt_trichotomy a c with hac | rfl | hac
      · rw [← h a c b hac hbc, hs c b]; abel
      · rw [h0, hs a b]; abel
      · rw [hs c b, hs c a, ← h c a b hac hab]; abel
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact key a b c hab
  · rw [h0, zero_add]
  · rw [← key b a c hab, hs b a]; abel
end GlobalTheory.AbLaw.CechOne
