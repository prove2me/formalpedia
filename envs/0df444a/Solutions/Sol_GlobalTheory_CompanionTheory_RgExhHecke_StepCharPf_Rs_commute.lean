-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.Rs.commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:45:19.062697+00:00
-- url     : https://prove2.me/submissions/5070a812-32f2-491f-bd1d-4af82dfd86b4

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_Rs_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_PolF_mul


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet qminor Tm)
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Submodule ℂ V}
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
namespace Rs
theorem _root_.solution {G G' : Module.End ℂ S} {F F' : Module.End ℂ V} (h : Rs G F) (h' : Rs G' F')
    (hc : Commute F F') : Commute G G' := by
  have e := h'.mul h
  rw [← hc.eq] at e
  exact (h.mul h').ext e
end Rs
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
