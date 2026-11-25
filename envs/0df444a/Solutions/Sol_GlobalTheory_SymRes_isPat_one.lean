-- Prove2me | solution 1 for GlobalTheory.SymRes.isPat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:16:12.017015+00:00
-- url     : https://prove2.me/submissions/24c51a9a-8f99-4432-810c-0d62030fc981

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsPatOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SymRes
namespace GlobalTheory.SymRes
theorem _root_.solution {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) : IsPat ρ κ (1 : GL (Fin r) K) := fun _ _ _ => rfl
end GlobalTheory.SymRes
