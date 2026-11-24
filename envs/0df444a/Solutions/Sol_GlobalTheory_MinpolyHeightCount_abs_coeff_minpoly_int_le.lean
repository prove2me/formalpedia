-- Prove2me | solution 1 for GlobalTheory.MinpolyHeightCount.abs_coeff_minpoly_int_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:19.586032+00:00
-- url     : https://prove2.me/submissions/a8086888-c83e-4e55-b074-b2fca432b314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
variable (K : Type) [Field K] [NumberField K]
namespace GlobalTheory.MinpolyHeightCount
theorem _root_.solution {x : K} (hx : IsIntegral ℤ x) {R : ℝ}
    (h : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R) (i : ℕ) :
    (|(minpoly ℤ x).coeff i| : ℝ) ≤ max R 1 ^ Module.finrank ℚ K *
      (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) := by
  refine Eq.trans_le ?_ (Embeddings.coeff_bdd_of_norm_le h i)
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map, eq_intCast,
    Int.norm_cast_rat, Int.norm_eq_abs]
end GlobalTheory.MinpolyHeightCount
