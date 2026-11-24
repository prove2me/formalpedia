-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.UJ_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:13.370152+00:00
-- url     : https://prove2.me/submissions/95c61fc1-3a60-4a57-9da2-7fd4a4c76809

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_UJ_left_inv
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
theorem _root_.solution {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : g⁻¹ ∈ UJset ε := by
  change (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε
  have h := mul_eq_one_comm.1 (UJ_left_inv hg)
  rw [UJ_inv hg]
  simp only [conjTranspose_mul, J_conj, conjTranspose_conjTranspose, Matrix.mul_assoc, J_J_mul] at h ⊢
  rw [h, Matrix.mul_one]
end GlobalTheory.CompanionTheory.SmoothModule
