-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.IsCocycle.swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:30.422987+00:00
-- url     : https://prove2.me/submissions/6b327416-5675-4694-8ad1-f34d32b4afa1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_IsCocycle_diag

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
variable {κ : Type} (D : κ → X.Opens)
variable [LinearOrder κ]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M)
variable {D f M}
namespace GlobalTheory.AbLaw.CechOne
namespace IsCocycle
theorem _root_.solution {I : Type} {O : I → X.Opens} {φ : ∀ a b, SecOn M (O a ⊓ O b)}
    (hφ : IsCocycle M O φ) (a b : I) :
    φ a b = -restrict M (le_inf inf_le_right inf_le_left) (φ b a) := by
  have h := hφ a b a (O a ⊓ O b) inf_le_left inf_le_right inf_le_left
  rw [restrict_self, hφ.diag, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h
end IsCocycle
end GlobalTheory.AbLaw.CechOne
