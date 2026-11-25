-- Prove2me | solution 1 for GlobalTheory.kUnit_of_isUnitary_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:55:59.681862+00:00
-- url     : https://prove2.me/submissions/06f2860c-70d2-45ed-a10d-fe4bc7a5d9bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeTensorOperatorRaiseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirBoundProjectionDualTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (h : IsUnitary ε E) : KUnit ε E := by
  intro a b hab u v
  have := h a b u v
  simpa [Formalism.REAL.sgn, hab] using this
end GlobalTheory
