-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StrictCone.IsStrict.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:42:47.695879+00:00
-- url     : https://prove2.me/submissions/b43ea5ed-d3a9-4111-933a-914a7a154f1e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativeCharacterOnCone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StrictCone
namespace GlobalTheory.CompanionTheory.StrictCone
namespace IsStrict
theorem _root_.solution {n : ℕ} {x y : Fin n → ℤ} (hx : IsStrict x) (hy : IsStrict y) :
    IsStrict (x + y) := by
  intro i j hij
  have := hx i j hij
  have := hy i j hij
  simp only [Pi.add_apply]
  omega
end IsStrict
end GlobalTheory.CompanionTheory.StrictCone
