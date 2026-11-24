-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliBlocks.co0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:10:51.269812+00:00
-- url     : https://prove2.me/submissions/6c99a45b-7a10-4858-b66a-29c29c982087

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_qminor_equiv
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_block_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_blk_val
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_blk_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliBlocks
open Formalism.REAL CompanionTheory.D.DSIC
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CapelliBlocks
theorem _root_.solution : CompanionTheory.D.DSIC.CapelliDeterminantBlockProduct := by
  intro n ε V _ _ E hE u v
  have h := block_mem ε E hE (Sum.elim (blk ε false) (blk ε true)) (blk_val ε false) (blk_val ε true) u v
  have h2 := qminor_equiv E hE (finSumFinEquiv.symm.trans (Equiv.ofBijective _ (blk_bijective ε))) u
  rw [← h2]
  exact h
end GlobalTheory.CompanionTheory.CapelliBlocks
