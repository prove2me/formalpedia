-- Prove2me | solution 1 for GlobalTheory.HermGram.reForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:50.210018+00:00
-- url     : https://prove2.me/submissions/677f6ac3-00ca-40c3-b17e-da06176bb860

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefRealGramPairHermitianForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.HermGram
namespace GlobalTheory.HermGram
theorem _root_.solution {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    reForm H z w = (z ⬝ᵥ H *ᵥ star w).re := rfl
end GlobalTheory.HermGram
