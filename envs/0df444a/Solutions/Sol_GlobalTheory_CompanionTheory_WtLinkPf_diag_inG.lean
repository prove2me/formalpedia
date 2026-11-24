-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WtLinkPf.diag_inG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:58:35.22496+00:00
-- url     : https://prove2.me/submissions/dae71c86-356d-4916-88a4-c72a820214a8

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExpMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WtLinkPf
open PI.UpqRep
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.WtLinkPf
theorem _root_.solution (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inG ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  show (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I).conjTranspose * PI.UpqRep.Jm ε +
      PI.UpqRep.Jm ε * Matrix.diagonal (fun a => (θ a : ℂ) * Complex.I) = 0
  unfold PI.UpqRep.Jm
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add, ← Matrix.diagonal_zero]
  congr 1
  funext a
  rw [Pi.star_apply, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring
end GlobalTheory.CompanionTheory.WtLinkPf
