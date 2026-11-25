-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.commute_C_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:58.201344+00:00
-- url     : https://prove2.me/submissions/5f5245cc-8215-4cd1-98db-86f253fa2951

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_Rs_ext
import Theorems.Thm_Formalism_REAL_qDetCentral


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
theorem _root_.solution (X : GMod n) (u : ℂ) : Commute ((qdet X.E u).compLeft (Fin n)) (om X) := by
  refine LinearMap.ext fun f => funext fun b => ?_
  simp only [Module.End.mul_apply, om_apply, LinearMap.compLeft_apply, Function.comp, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact LinearMap.congr_fun (Formalism.REAL.qDetCentral _ n X.E X.gl u a b) (f a)
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
