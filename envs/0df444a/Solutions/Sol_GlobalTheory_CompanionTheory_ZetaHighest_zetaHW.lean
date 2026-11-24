-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZetaHighest.zetaHW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:46.198597+00:00
-- url     : https://prove2.me/submissions/d7fc8f74-3173-43cc-a806-8ff2ba58a9df

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkStrictMono
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_prod_blk
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_gam_false
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_gam_true
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_block_eigen
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
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZetaHighest
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ZetaHighest
theorem _root_.solution : CompanionTheory.D.DSIC.ZetaHW := by
  intro n ε lam V _ _ F x hF hx Y
  unfold zeta
  rw [Module.End.mul_apply, block_eigen ε true _ V F x hF hx, map_smul, block_eigen ε false _ V F x hF hx,
    smul_smul]
  congr 1
  have e1 : ∀ i : Fin (nb ε true), (Y + ((n : ℂ) - 1) / 2 - (nb ε false : ℂ) - (i : ℂ) +
      (gam ε lam (blk ε true i) : ℂ)) = Y + lam (blk ε true i) := by
    intro i; rw [gam_true]; push_cast; ring
  have e2 : ∀ i : Fin (nb ε false), (Y + ((n : ℂ) - 1) / 2 - (i : ℂ) +
      (gam ε lam (blk ε false i) : ℂ)) = Y + lam (blk ε false i) := by
    intro i; rw [gam_false]; push_cast; ring
  simp only [e1, e2]
  rw [prod_blk ε true fun a => Y + (lam a : ℂ), prod_blk ε false fun a => Y + (lam a : ℂ), Formalism.QuantumDeterminants.capP,
    ← Finset.prod_filter_mul_prod_filter_not univ (fun a => ε a = true)]
  simp only [Bool.not_eq_true]
end GlobalTheory.CompanionTheory.ZetaHighest
