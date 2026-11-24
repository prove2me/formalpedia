-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PairCount.card_comap_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:55:18.906996+00:00
-- url     : https://prove2.me/submissions/a2d06617-2130-4d18-a031-7239723bc54a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorIntersectionCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PairCount
namespace GlobalTheory.CompanionTheory.PairCount
theorem _root_.solution {R X : Type} [Ring R] [AddCommGroup X] [Module R X]
    (p q : Submodule R X) :
    Nat.card ↥(q.comap p.subtype) = Nat.card ↥(p ⊓ q) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end GlobalTheory.CompanionTheory.PairCount
