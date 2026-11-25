-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.Rs.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:23:16.656024+00:00
-- url     : https://prove2.me/submissions/d15ab9ad-a1a6-4852-b29b-fbe0dcf04c5f

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement

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
theorem _root_.solution {G G' : Module.End ℂ S} {F F' : Module.End ℂ V} (h : Rs G F) (h' : Rs G' F') :
    Rs (G - G') (F - F') := fun x => by
  simp only [LinearMap.sub_apply, Submodule.coe_sub]
  rw [h, h']
end Rs
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
