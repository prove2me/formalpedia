-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.capelliPoly_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:54.513055+00:00
-- url     : https://prove2.me/submissions/7c80b6ce-9d67-417a-b1f2-723411fde816

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_capelliPoly_eq_mul_prod_erase

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
    capP (χ + Pi.single s 1) Y = (∏ t ∈ univ.erase s, (Y + χ t)) * (Y + χ s + 1) := by
  rw [capelliPoly_eq_mul_prod_erase _ s]
  congr 1
  · refine Finset.prod_congr rfl fun t ht => ?_
    simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase ht)]
  · simp [add_assoc]
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
