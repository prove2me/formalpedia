-- Prove2me | solution 1 for GlobalTheory.EquivariantSubspace.smoothOnH_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:32.36191+00:00
-- url     : https://prove2.me/submissions/99c34b20-dca7-4a32-a351-9047c563e9a5

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
theorem _root_.solution {H : Matrix (Fin n) (Fin n) ℂ} {f f' : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) (hf' : SmoothOnH H f') : SmoothOnH H (f + f') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), ?_⟩
  intro g hg hH
  rw [Pi.add_apply, hfF g hg.1 hH, hfF' g hg.2 hH]
end GlobalTheory.EquivariantSubspace
