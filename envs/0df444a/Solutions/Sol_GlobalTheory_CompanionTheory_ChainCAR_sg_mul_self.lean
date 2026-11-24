-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainCAR.sg_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:22:56.989489+00:00
-- url     : https://prove2.me/submissions/8e483636-4c12-4e31-abc8-7010f687b8ca

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
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
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainCAR
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.ChainCAR
theorem _root_.solution (i : NC ε) (A : Finset (NC ε)) : sg i A * sg i A = 1 := by
  unfold sg
  rw [← mul_pow]; simp
end GlobalTheory.CompanionTheory.ChainCAR
