-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.inG_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:24.082847+00:00
-- url     : https://prove2.me/submissions/2ed5bc2d-a459-4863-940b-73a6589bfcfe

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_UJ_inv
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
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.SmoothModule
theorem _root_.solution {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) :
    inG ε (g * X * g⁻¹) := by
  rw [inG_iff] at *
  conv_rhs => rw [← hX]
  rw [UJ_inv hg]
  simp only [thetaJ, conjTranspose_mul, J_conj, conjTranspose_conjTranspose, Matrix.mul_assoc, J_J_mul,
    Matrix.mul_neg, Matrix.neg_mul]
end GlobalTheory.CompanionTheory.SmoothModule
