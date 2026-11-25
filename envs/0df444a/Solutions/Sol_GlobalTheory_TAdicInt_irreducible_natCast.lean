-- Prove2me | solution 1 for GlobalTheory.TAdicInt.irreducible_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:27.133472+00:00
-- url     : https://prove2.me/submissions/1790d29e-2d0a-4ee8-b657-3b9ec67de5bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PadicResidueFieldCardAndPrimeIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.TAdicInt
namespace GlobalTheory.TAdicInt
theorem _root_.solution (T : ℕ) [Fact T.Prime] : Irreducible (T : 𝒪[ℚ_[T]]) := by
  have := (PadicInt.irreducible_p (p := T)).map (intEquiv T).symm.toMulEquiv
  rwa [show (intEquiv T).symm.toMulEquiv (T : ℤ_[T]) = (T : 𝒪[ℚ_[T]]) from
    map_natCast (intEquiv T).symm T] at this
end GlobalTheory.TAdicInt
