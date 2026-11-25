-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrinSumP.ins_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:42.038276+00:00
-- url     : https://prove2.me/submissions/525d0baa-05b0-4370-8cd8-c420890d18ac

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSum
import Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_ins_succAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrinSumP
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (capEntry cminor)
open Formalism.REAL (Tm qminor qdet)
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.PrinSumP
theorem _root_.solution {m : ℕ} (d : Fin (m + 1)) : Function.Injective (ins d) := by
  intro τ τ' h
  ext i
  have := congrArg (fun s : Equiv.Perm (Fin (m + 1)) => s (d.succAbove i)) h
  simp only [ins_succAbove] at this
  exact congrArg Fin.val (Fin.succAbove_right_injective this)
end GlobalTheory.CompanionTheory.PrinSumP
