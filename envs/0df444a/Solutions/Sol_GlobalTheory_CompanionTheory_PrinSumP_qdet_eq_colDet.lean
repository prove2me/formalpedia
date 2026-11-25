-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrinSumP.qdet_eq_colDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:04:43.631137+00:00
-- url     : https://prove2.me/submissions/10129329-31c6-4b2a-b102-6ce5b29eb82b

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSum
import Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_Tm_eq_capEntry

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    qdet E u = colDet E (fun j => u - ((j : ℕ) : ℂ)) := by
  unfold qdet qminor colDet
  refine sum_congr rfl fun σ _ => ?_
  rw [← zsmul_eq_mul]
  congr 2
  simp only [Tm_eq_capEntry, id]
end GlobalTheory.CompanionTheory.PrinSumP
