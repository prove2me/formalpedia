-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.polyFn_tm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:38:35.519306+00:00
-- url     : https://prove2.me/submissions/1e8d01e2-c4a7-4a6d-add5-99ce03795b98

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_PolyFn_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_PolF_add


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
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (c : ℂ) (a b : Fin n) :
    PolyFn (fun u : ℂ => Tm E (u - c) a b) := by
  unfold Tm
  by_cases h : a = b
  · simp only [h, if_true, map_sub]
    exact (PolyFn.alg.sub (PolyFn.const _)).add (PolyFn.const _)
  · simp only [h, if_false]
    exact (PolyFn.const _).add (PolyFn.const _)
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
