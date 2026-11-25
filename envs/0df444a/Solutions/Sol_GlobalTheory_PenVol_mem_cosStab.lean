-- Prove2me | solution 1 for GlobalTheory.PenVol.mem_cosStab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:00.275664+00:00
-- url     : https://prove2.me/submissions/59f2bd8c-5773-46a5-bb9e-22d1674f6237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ToBlocksMulFinZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ValuativeRel
open GlobalTheory GlobalTheory.PenVol
variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]
namespace GlobalTheory.PenVol
theorem _root_.solution {J : Subgroup (GL (n ⊕ Fin 0) k)} {M : Submodule 𝒪[k] (n → k)} {c : (n → k) ⧸ M}
    {g : GL (n ⊕ Fin 0) k} : g ∈ cosStab J M c ↔ g ∈ J ∧ ∀ y : n → k,
      (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ M) = c ↔ Submodule.Quotient.mk y = c := Iff.rfl
end GlobalTheory.PenVol
