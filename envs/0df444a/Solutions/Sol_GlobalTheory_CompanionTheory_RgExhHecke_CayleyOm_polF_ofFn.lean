-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.polF_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:39.416275+00:00
-- url     : https://prove2.me/submissions/3ccd12b0-7a5c-4250-a25c-ebf03ce86d96

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_polF_const
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
open Polynomial Formalism.REAL CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
theorem _root_.solution {m : ℕ} (f : Fin m → ℂ → A) (h : ∀ i, PolF (f i)) :
    PolF fun y => (List.ofFn fun i => f i y).prod := by
  induction m with
  | zero => simpa using polF_const (1 : A)
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (h 0).mul (ih _ fun i => h i.succ)
end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
