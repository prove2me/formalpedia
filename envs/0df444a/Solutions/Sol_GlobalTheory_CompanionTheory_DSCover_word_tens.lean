-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCover.word_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:01:33.473033+00:00
-- url     : https://prove2.me/submissions/c931e60a-418c-43ce-958f-caf9343347f5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_word_pol
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_word_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
variable {σ : Type}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.DSCover
theorem _root_.solution (z : V ⊗[ℂ] MvPolynomial σ ℂ) : ∃ m : ℕ, ∀ l : List σ, m ≤ l.length →
    (l.map fun i => ((pd i).lTensor V : Module.End ℂ (V ⊗[ℂ] MvPolynomial σ ℂ))).prod z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, fun l _ => map_zero _⟩
  | tmul v f =>
    obtain ⟨m, hm⟩ := word_pol f
    exact ⟨m, fun l hl => by rw [word_tmul, hm l hl, TensorProduct.tmul_zero]⟩
  | add p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨k, hk⟩ := hq
    exact ⟨max m k, fun l hl => by
      rw [map_add, hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩
end GlobalTheory.CompanionTheory.DSCover
