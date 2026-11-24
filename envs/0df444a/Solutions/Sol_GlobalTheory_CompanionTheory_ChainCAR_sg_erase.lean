-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainCAR.sg_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:39:05.755935+00:00
-- url     : https://prove2.me/submissions/a90a6ebb-e748-47ed-8c5d-fdf1f60b8ef0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_tw_mul_self
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_sg_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainCAR
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.ChainCAR
theorem _root_.solution (i : NC ε) {j : NC ε} {A : Finset (NC ε)} (h : j ∈ A) :
    sg i (A.erase j) = tw i j * sg i A := by
  have h1 := sg_insert i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]
end GlobalTheory.CompanionTheory.ChainCAR
