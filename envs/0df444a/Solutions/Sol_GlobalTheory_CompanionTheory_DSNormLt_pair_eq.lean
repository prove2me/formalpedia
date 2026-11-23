-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.pair_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:32.472027+00:00
-- url     : https://prove2.me/submissions/dad93cfe-34c1-4919-bf9a-0bb297a9f8a5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSNormLt
theorem _root_.solution (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (x : Fin n → ℝ) :
    4 * ∑ a, x a * ((∑ b, t a b) / 2) = ∑ a, ∑ b, t a b * (x a - x b) := by
  have h1 : ∑ a, ∑ b, t a b * x b = - ∑ a, ∑ b, t a b * x a := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ht a b]; ring
  have h2 : ∑ a, x a * ((∑ b, t a b) / 2) = (∑ a, ∑ b, t a b * x a) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul]; ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2]; ring
end GlobalTheory.CompanionTheory.DSNormLt
