-- Prove2me | solution 1 for GlobalTheory.posDef_realExt_iff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:15.333287+00:00
-- url     : https://prove2.me/submissions/3e4f9a3b-c489-4ddc-8195-f38c6d469bf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_posDef_realExt_of_tendsto
import Theorems.Thm_GlobalTheory_tendsto_of_posDef_realExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q : QuadraticMap ℤ X ℝ) : (realExt Q).PosDef ↔ Tendsto Q cofinite atTop :=
  ⟨tendsto_of_posDef_realExt, posDef_realExt_of_tendsto Q⟩
end GlobalTheory
