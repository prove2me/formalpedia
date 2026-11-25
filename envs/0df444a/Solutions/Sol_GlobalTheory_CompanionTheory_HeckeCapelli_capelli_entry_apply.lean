-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCapelli.capelli_entry_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:59:26.9446+00:00
-- url     : https://prove2.me/submissions/13e6a83f-f27a-49fc-8be4-b73f1eac117f

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEqualityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelliExpand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCapelli
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry capelliExpand)
namespace GlobalTheory.CompanionTheory.HeckeCapelli
theorem _root_.solution {n : ℕ} (X : GMod n) (x : ℂ) (d b : Fin n) (v : X.V) :
    capEntry X.E x d b v = X.E d b v + if d = b then x • v else 0 := by
  unfold capEntry
  split_ifs <;> simp [Module.algebraMap_end_apply]
end GlobalTheory.CompanionTheory.HeckeCapelli
