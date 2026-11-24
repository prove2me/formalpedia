-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCover.word_pol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:45:13.432316+00:00
-- url     : https://prove2.me/submissions/25898c2e-d2e5-4c5e-88e0-9d0e7016441c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_word_monomial

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
namespace GlobalTheory.CompanionTheory.DSCover
theorem _root_.solution (f : MvPolynomial σ ℂ) : ∃ m : ℕ, ∀ l : List σ, m ≤ l.length → (l.map pd).prod f = 0 := by
  induction f using MvPolynomial.induction_on' with
  | monomial s c => exact ⟨s.degree + 1, fun l hl => word_monomial l s c (by omega)⟩
  | add p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨k, hk⟩ := hq
    exact ⟨max m k, fun l hl => by
      rw [map_add, hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩
end GlobalTheory.CompanionTheory.DSCover
