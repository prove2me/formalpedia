-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.compLeft_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:01.677177+00:00
-- url     : https://prove2.me/submissions/e37051d9-ac8e-4212-b7e6-8026f9d797ba

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk
namespace GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (c : ℂ) (w : Fin n → V) :
    (c • (1 : Module.End ℂ V)).compLeft (Fin n) w = c • w := by
  funext i
  simp [LinearMap.compLeft_apply]
end GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
