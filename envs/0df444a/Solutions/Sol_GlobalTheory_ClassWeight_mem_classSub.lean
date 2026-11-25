-- Prove2me | solution 1 for GlobalTheory.ClassWeight.mem_classSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:32.23578+00:00
-- url     : https://prove2.me/submissions/a277eac3-6697-4357-b39f-1423b0092a2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassWeight
variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}
variable {E : Type} [AddCommGroup E] [Module F E] {W : X → Type} [∀ α, AddCommGroup (W α)] [∀ α, Module F (W α)]
namespace GlobalTheory.ClassWeight
theorem _root_.solution {S : ∀ α, E →ₗ[F] W α} {α : X} {v : E} :
    v ∈ classSub S N α ↔ ∀ β, (¬ ∃ mu, β = α + N • mu) → S β v = 0 := Iff.rfl
end GlobalTheory.ClassWeight
