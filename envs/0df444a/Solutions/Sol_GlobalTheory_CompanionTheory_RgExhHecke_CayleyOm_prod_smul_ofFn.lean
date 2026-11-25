-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.prod_smul_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:38.177073+00:00
-- url     : https://prove2.me/submissions/8bd73089-c18c-45fa-99ba-c9cdc3907986

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement

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
theorem _root_.solution {m : ℕ} (s : ℂ) (f : Fin m → A) :
    (List.ofFn fun i => s • f i).prod = s ^ m • (List.ofFn f).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih, smul_mul_smul_comm, pow_succ']
end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
