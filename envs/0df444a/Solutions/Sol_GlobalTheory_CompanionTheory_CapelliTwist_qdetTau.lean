-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliTwist.qdetTau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:15:59.816529+00:00
-- url     : https://prove2.me/submissions/ff48e692-65ca-4684-8b72-2ee85bc195e2

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeDuality_GlRelTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTau
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_qdet_eq_capelliC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_eq_rminor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_capelliC_negT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliTwist
open Formalism.REAL (qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open CompanionTheory.RgExh.Hk
namespace GlobalTheory.CompanionTheory.CapelliTwist
theorem _root_.solution : QdetTau := by
  intro n X u
  have hgl : GlRelR X.E := X.gl
  have hrow : capelliC X.E (-u + ((n : ℂ) - 1)) = rminor X.E id id ((n : ℂ) - 1 - u) := by
    rw [show -u + ((n : ℂ) - 1) = (n : ℂ) - 1 - u by ring]
    exact cminor_eq_rminor X.E hgl id id _
  rw [GlobalTheory.CompanionTheory.RgExhHecke.qdet_eq_capelliC, GlobalTheory.CompanionTheory.RgExhHecke.qdet_eq_capelliC, hrow]
  show capelliC (fun a b => -X.E b a) u = _
  rw [ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.capelliC_negT]
  rw [show ((-1 : Module.End ℂ X.V)) ^ n = algebraMap ℂ _ ((-1 : ℂ) ^ n) by simp,
    Algebra.smul_def]
end GlobalTheory.CompanionTheory.CapelliTwist
