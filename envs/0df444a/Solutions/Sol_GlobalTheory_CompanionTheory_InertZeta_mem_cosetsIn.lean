-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.mem_cosetsIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:59:18.456645+00:00
-- url     : https://prove2.me/submissions/6621b73d-f42a-44dc-9190-b40da82ca6c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DoubleCosetSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution {hK : IsCommensurated K} {g : G} {x : G ⧸ K} :
    x ∈ cosetsIn hK g ↔ x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
  rw [cosetsIn, Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, a.2, b, b.2, h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩
end GlobalTheory.CompanionTheory.InertZeta
