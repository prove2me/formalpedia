-- Prove2me | solution 1 for GlobalTheory.PenVol.cosStab_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:38.555653+00:00
-- url     : https://prove2.me/submissions/10d00b3a-1778-4fa5-9296-82900cfbddbf

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
theorem _root_.solution (J : Subgroup (GL (n ⊕ Fin 0) k)) (M : Submodule 𝒪[k] (n → k)) (c : (n → k) ⧸ M) :
    cosStab J M c ≤ J := fun _ h => h.1
end GlobalTheory.PenVol
