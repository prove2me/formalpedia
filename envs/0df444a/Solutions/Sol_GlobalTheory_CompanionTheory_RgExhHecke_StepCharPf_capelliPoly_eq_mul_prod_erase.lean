-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.capelliPoly_eq_mul_prod_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:21:38.101148+00:00
-- url     : https://prove2.me/submissions/93fc9c13-1918-491a-b08c-47d1aa42382e

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
open Formalism.QuantumDeterminants (capP)
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
theorem _root_.solution (χ : Fin n → ℂ) (s : Fin n) (Y : ℂ) :
    capP χ Y = (∏ t ∈ univ.erase s, (Y + χ t)) * (Y + χ s) := by
  unfold capP
  rw [Finset.prod_erase_mul _ _ (mem_univ s)]
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
