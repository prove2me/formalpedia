-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrinSumP.sum_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:58.879708+00:00
-- url     : https://prove2.me/submissions/0183ac49-a307-456c-85a7-888ea7584ce9

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSum
import Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_qdet_eq_colDet
import Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_hyb_step

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
theorem _root_.solution {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (x : ℂ) :
    ∑ d : Fin (m + 1), cminor E d.succAbove d.succAbove (x - 1) = qdet E x - qdet E (x - 1) := by
  have h0 : qdet E x = colDet E (hyb x 0) := by
    rw [qdet_eq_colDet]
    congr 1
  have h1 : qdet E (x - 1) = colDet E (hyb x (m + 1)) := by
    rw [qdet_eq_colDet]
    congr 1
    funext j
    simp [hyb, j.2]
  rw [h0, h1, ← sum_congr rfl fun d _ => hyb_step E x d,
    Fin.sum_univ_eq_sum_range (fun k => colDet E (hyb x k) - colDet E (hyb x (k + 1))) (m + 1),
    sum_range_sub']
end GlobalTheory.CompanionTheory.PrinSumP
