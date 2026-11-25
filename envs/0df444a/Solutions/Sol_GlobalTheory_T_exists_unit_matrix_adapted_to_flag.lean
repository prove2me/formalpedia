-- Prove2me | solution 1 for GlobalTheory.T.exists_unit_matrix_adapted_to_flag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:31.253328+00:00
-- url     : https://prove2.me/submissions/1b2f4bc0-bb0a-4c77-8801-3cd5a9f5208e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasisStatement
import Theorems.Thm_GlobalTheory_LaurentFlagBasis_adapted_integral_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (n R : ℕ) (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W → ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n), (j : ℕ) < Module.finrank (LaurentSeries F) (W k) → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W k := by
  first | exact @GlobalTheory.LaurentFlagBasis.adapted_integral_basis | exact GlobalTheory.LaurentFlagBasis.adapted_integral_basis | (intros; apply GlobalTheory.LaurentFlagBasis.adapted_integral_basis <;> assumption)
end _root_.GlobalTheory.T
