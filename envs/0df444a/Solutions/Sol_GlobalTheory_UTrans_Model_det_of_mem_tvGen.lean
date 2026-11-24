-- Prove2me | solution 1 for GlobalTheory.UTrans.Model.det_of_mem_tvGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:05.676042+00:00
-- url     : https://prove2.me/submissions/479b17ce-ec77-44c7-8603-d8dcc1c41e7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection
import Theorems.Thm_GlobalTheory_UTrans_Model_det_tv

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
theorem _root_.solution (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) {m} (hm : m ∈ TvGen σ G) : m.det = 1 := by
  induction hm using Submonoid.closure_induction with
  | mem m hm =>
    obtain ⟨x, t, hx, _, rfl⟩ := hm
    rw [det_tv, hx, mul_zero, add_zero]
  | one => exact Matrix.det_one
  | mul p q _ _ hp hq => rw [Matrix.det_mul, hp, hq, mul_one]
end GlobalTheory.UTrans.Model
