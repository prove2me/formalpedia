-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.commute_T_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:44.328041+00:00
-- url     : https://prove2.me/submissions/ba4e6873-5788-4e2f-a052-c1632766351a

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_commute_qdet

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
theorem _root_.solution (X : GMod n) (u : ℂ) : Commute (qdet (tensE X) u) (om X) :=
  (commute_qdet (om X) (fun a b => (commute_om X a b).symm) u).symm
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
