-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSStabLink.inK_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:21.5701+00:00
-- url     : https://prove2.me/submissions/f0af39ca-4b31-45b1-a362-209df6431eef

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExpMemUJ
import Theorems.Thm_GlobalTheory_CompanionTheory_DSStabLink_inK_iff
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
open Matrix Finset Filter Topology Set
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSStabLink
open PI.UpqRep CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSStabLink
theorem _root_.solution (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  rw [inK_iff] at hX ⊢
  refine ⟨fun c d h => by simp [hX.1 c d h], fun c d => ?_⟩
  have := hX.2 c d
  simp only [Matrix.smul_apply, smul_eq_mul, star_mul', this]
  simp
end GlobalTheory.CompanionTheory.DSStabLink
