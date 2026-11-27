-- Prove2me | solution 1 for GlobalTheory.coneExact_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:42.265589+00:00
-- url     : https://prove2.me/submissions/c5cc373b-4a1c-44f4-b5d5-2cf7baf0399d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : ℕ → Type v} [∀ p, AddCommGroup (K p)] (d : ∀ p, K p →+ K (p + 1)) :
    ConeExact (fun p => d p) (fun p => d p) (fun _ x => x) :=
  ⟨fun _ h _ => h, fun c _ h _ => ⟨c, rfl, h⟩, fun p c _ h _ => ⟨0, c, by simp, h⟩⟩
end GlobalTheory
