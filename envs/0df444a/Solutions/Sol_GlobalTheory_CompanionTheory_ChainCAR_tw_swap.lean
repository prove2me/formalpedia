-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainCAR.tw_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:39:25.265771+00:00
-- url     : https://prove2.me/submissions/cea4720f-0fd0-4cc9-9726-21f81265d347

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_key_inj
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
theorem _root_.solution {i j : NC ε} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : key i ≠ key j := fun e => h (key_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]
end GlobalTheory.CompanionTheory.ChainCAR
