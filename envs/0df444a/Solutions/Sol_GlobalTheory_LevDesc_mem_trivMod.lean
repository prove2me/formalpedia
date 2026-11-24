-- Prove2me | solution 1 for GlobalTheory.LevDesc.mem_trivMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:41:30.36696+00:00
-- url     : https://prove2.me/submissions/990ceca9-6a42-4d12-a637-7a97b55bf393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {O : Type} [CommRing O] (N : Type) [AddCommGroup N] [Module O N]
variable {N} {I J : Ideal O}
namespace GlobalTheory.LevDesc
theorem _root_.solution {γ : QAut N I} : γ ∈ trivMod N I J ↔ ∀ q, γ q - q ∈ J • (⊤ : Submodule O (QMod N I)) := Iff.rfl
end GlobalTheory.LevDesc
