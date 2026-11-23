-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.sig_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:21.007798+00:00
-- url     : https://prove2.me/submissions/eb2d1ad6-69a0-4cb6-8497-69bfe88b219a

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
theorem _root_.solution {y : Fin n → ℝ} (hy : Antitone y) (a b : Fin n) : sig a b * (y a - y b) = |y a - y b| := by
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · rw [if_pos h, one_mul, abs_of_nonneg (sub_nonneg.2 (hy h.le))]
  · simp [h]
  · rw [if_neg h.not_gt, if_pos h, abs_of_nonpos (sub_nonpos.2 (hy h.le))]; ring
end GlobalTheory.CompanionTheory.DSNormLt
