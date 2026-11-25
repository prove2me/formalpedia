-- Prove2me | solution 1 for GlobalTheory.LevelUnitary.mul_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:11:32.680936+00:00
-- url     : https://prove2.me/submissions/cfaad182-0bb3-4788-bbe6-0400bdcd3d29

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
theorem _root_.solution {m : Type} (M : Matrix m (Fin (2 * (i + r') + k + 1)) ℂ) (p : m) (j) :
    (M * incl k i r') p j = M p (levPos k i r' j) := by
  simp [Matrix.mul_apply, incl]
end GlobalTheory.LevelUnitary
