-- Prove2me | solution 1 for GlobalTheory.trdeg_eq_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:47.157189+00:00
-- url     : https://prove2.me/submissions/9c24a25c-de73-44c0-9ce0-e4ae1f613125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Theorems.Thm_GlobalTheory_trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension

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
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X), IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g := by
  intro K _ X _ f g hf B _ _ _ j hj hjf
  have : IsIntegral (Spec (CommRingCat.of B)) := isIntegral_of_isOpenImmersion j
  have : IsDomain B := (affine_isIntegral_iff (CommRingCat.of B)).mp this
  have h0 : SmoothOfRelativeDimension (0 + g) (j ≫ f) := inferInstance
  rw [Nat.zero_add, hjf] at h0
  have hloc := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).mp h0
  exact trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension hloc
end GlobalTheory
