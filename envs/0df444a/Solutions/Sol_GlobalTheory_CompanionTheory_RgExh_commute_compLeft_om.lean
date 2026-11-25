-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExh.commute_compLeft_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:55:46.38567+00:00
-- url     : https://prove2.me/submissions/a9778fee-eaab-4961-92da-354f1d6f40df

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOneStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensor
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExh
open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk
namespace GlobalTheory.CompanionTheory.RgExh
theorem _root_.solution {n : ℕ} (X : GMod n) (u : ℂ) :
    Commute ((qdet X.E u).compLeft (Fin n)) (om X) := by
  have hc := Formalism.REAL.qDetCentral (Module.End ℂ X.V) n X.E X.gl u
  unfold Commute SemiconjBy
  refine LinearMap.ext fun f => funext fun b => ?_
  simp only [Module.End.mul_apply, LinearMap.compLeft_apply, Function.comp_apply, om, LinearMap.coe_mk,
    AddHom.coe_mk, map_sum]
  exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hc a b) (f a)
end GlobalTheory.CompanionTheory.RgExh
