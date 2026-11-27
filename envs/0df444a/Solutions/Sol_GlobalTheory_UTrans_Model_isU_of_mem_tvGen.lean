-- Prove2me | solution 1 for GlobalTheory.UTrans.Model.isU_of_mem_tvGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:24.788131+00:00
-- url     : https://prove2.me/submissions/de661deb-4a06-4c39-a447-10c456cee4e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection
import Theorems.Thm_GlobalTheory_UTrans_Model_isU_tv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.UTrans.Model
theorem _root_.solution (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a)
    (hG : ∀ a b, σ (G a b) = G b a) {m} (hm : m ∈ TvGen σ G) : IsU σ G m := by
  induction hm using Submonoid.closure_induction with
  | mem m hm =>
    obtain ⟨x, t, hx, ht, rfl⟩ := hm
    exact isU_tv σ G hσ hG x t (by rw [hx, mul_zero, add_zero]; exact ht)
  | one => intro v w; simp only [Matrix.one_mulVec]
  | mul p q _ _ hp hq =>
    intro v w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp, hq]
end GlobalTheory.UTrans.Model
