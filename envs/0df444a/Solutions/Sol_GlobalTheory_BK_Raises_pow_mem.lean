-- Prove2me | solution 1 for GlobalTheory.BK.Raises.pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:54:06.871847+00:00
-- url     : https://prove2.me/submissions/d75a9141-7c4d-4ebf-abef-ddd49ce6110b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {K : Type} [NormedField K] {a : ℕ} {ι κ : Type}
namespace GlobalTheory.BK
namespace Raises
theorem _root_.solution {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) (n : ℕ) : (T ^ n) w ∈ uPow K a ι (n + 1) := by
  induction n with
  | zero => exact hw
  | succ n ih => rw [pow_succ']; exact hT n _ ih
end Raises
end GlobalTheory.BK
