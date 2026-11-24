-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WtLinkPf.exp_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:58:36.217855+00:00
-- url     : https://prove2.me/submissions/3c906b9f-1414-4fd3-8498-7e3146091424

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
theorem _root_.solution (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) = tor (t • θ) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  unfold tor
  congr 1
  funext a
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring
end GlobalTheory.CompanionTheory.WtLinkPf
