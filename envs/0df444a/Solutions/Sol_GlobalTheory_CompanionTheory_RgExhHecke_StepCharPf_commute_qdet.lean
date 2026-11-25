-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.commute_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:11.159425+00:00
-- url     : https://prove2.me/submissions/8cc43f67-b733-4e7e-be55-305cb91579e7

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
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
theorem _root_.solution {n : ℕ} {E : Fin n → Fin n → A} (O : A) (h : ∀ a b, Commute O (E a b)) (u : ℂ) :
    Commute O (qdet E u) := by
  unfold qdet qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine (Int.cast_commute _ O).symm.mul_right (Commute.list_prod_right _ _ fun T hT => ?_)
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact (Algebra.commutes _ _).symm
  · exact Commute.zero_right _
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
