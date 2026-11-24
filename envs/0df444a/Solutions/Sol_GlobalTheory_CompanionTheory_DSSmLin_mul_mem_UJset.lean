-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSSmLin.mul_mem_UJset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:33.221968+00:00
-- url     : https://prove2.me/submissions/10d00fc4-baf0-4a16-aae7-81e43a3c2679

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MulMemUJset
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
open Matrix PI.UpqRep CompanionTheory.D.Upq.Sm
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSSmLin
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.DSSmLin
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  simp only [UJset, Set.mem_setOf_eq, inUJ, Matrix.conjTranspose_mul] at *
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]
end GlobalTheory.CompanionTheory.DSSmLin
