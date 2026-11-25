-- Prove2me | solution 1 for GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:32.21244+00:00
-- url     : https://prove2.me/submissions/25b05217-4e26-4693-8b4d-ec5d6f51f62e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PosSemidefRealOfIntQuadFormNonneg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PosSemidefRealOfIntQuadFormNonnegStatement
import Theorems.Thm_GlobalTheory_intSymm_posSemidef_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm → (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) → (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  first | exact @GlobalTheory.intSymm_posSemidef_real | exact GlobalTheory.intSymm_posSemidef_real | (intros; apply GlobalTheory.intSymm_posSemidef_real <;> assumption)
end _root_.GlobalTheory.T
