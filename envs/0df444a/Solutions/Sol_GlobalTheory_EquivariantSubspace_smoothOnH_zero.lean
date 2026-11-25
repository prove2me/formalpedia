-- Prove2me | solution 1 for GlobalTheory.EquivariantSubspace.smoothOnH_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:38.152492+00:00
-- url     : https://prove2.me/submissions/c00bad6d-5700-4308-87a2-58a243ea7162

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EquivariantSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.QuantumDeterminants
open GlobalTheory GlobalTheory.EquivariantSubspace
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.EquivariantSubspace
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) :
    SmoothOnH H (0 : Matrix (Fin n) (Fin n) ℂ → E) :=
  fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
end GlobalTheory.EquivariantSubspace
