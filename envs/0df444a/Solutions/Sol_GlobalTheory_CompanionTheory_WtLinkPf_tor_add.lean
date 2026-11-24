-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WtLinkPf.tor_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:28.659928+00:00
-- url     : https://prove2.me/submissions/3f179b2a-4478-49cb-846c-3981cf2fa687

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExpMul
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
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WtLinkPf
open PI.UpqRep
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.WtLinkPf
theorem _root_.solution (θ η : Fin n → ℝ) : tor (θ + η) = tor θ * tor η := by
  unfold tor
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  ring
end GlobalTheory.CompanionTheory.WtLinkPf
