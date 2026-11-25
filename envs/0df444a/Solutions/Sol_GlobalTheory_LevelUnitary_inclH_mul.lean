-- Prove2me | solution 1 for GlobalTheory.LevelUnitary.inclH_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:48.207213+00:00
-- url     : https://prove2.me/submissions/f6a5627b-3d3f-4a27-ae94-14b0d59cd0aa

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight

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
open GlobalTheory GlobalTheory.LevelUnitary
variable (k i r' : ℕ)
namespace GlobalTheory.LevelUnitary
theorem _root_.solution {m : Type} (M : Matrix (Fin (2 * (i + r') + k + 1)) m ℂ) (p : m) (j) :
    ((incl k i r')ᴴ * M) j p = M (levPos k i r' j) p := by
  simp [Matrix.mul_apply, incl, conjTranspose_apply, apply_ite star]
end GlobalTheory.LevelUnitary
