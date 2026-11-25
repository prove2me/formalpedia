-- Prove2me | solution 1 for GlobalTheory.LevelStabiliser.liftVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:06.127882+00:00
-- url     : https://prove2.me/submissions/e67dad64-286d-4da1-8d26-7a809b00009b

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Theorems.Thm_GlobalTheory_LevelUnitary_incl_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.LevelStabiliser
open GlobalTheory.LevelUnitary
variable (k i r' : ℕ)
namespace GlobalTheory.LevelStabiliser
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k i r' v = incl k i r' *ᵥ v := by
  ext p
  have h := incl_mul k i r' (Matrix.of fun a (_ : Unit) => v a) p ()
  exact h.symm
end GlobalTheory.LevelStabiliser
