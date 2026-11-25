-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExh.commute_qdet_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:11.649799+00:00
-- url     : https://prove2.me/submissions/c79f3504-eeba-481d-9057-4bc2a299b10c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOneStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensor

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (T : A)
    (h : ∀ a b, Commute (E a b) T) (u : ℂ) : Commute (qdet E u) T := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) ?_
  refine Commute.list_prod_left _ _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  unfold Formalism.REAL.Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _
end GlobalTheory.CompanionTheory.RgExh
