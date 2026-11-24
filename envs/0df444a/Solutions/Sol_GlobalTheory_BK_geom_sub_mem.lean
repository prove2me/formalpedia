-- Prove2me | solution 1 for GlobalTheory.BK.geom_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:12:42.698823+00:00
-- url     : https://prove2.me/submissions/42324523-2ce0-43f0-9e00-60a9388af43a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_uPow_anti
import Theorems.Thm_GlobalTheory_BK_Raises_pow_mem

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
theorem _root_.solution {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) (n : ℕ) :
    geom T w - (∑ j ∈ Finset.range n, T ^ j) w ∈ uPow K a ι (n + 1) := by
  have h : geom T w - (∑ j ∈ Finset.range (n + 1), T ^ j) w ∈ uPow K a ι (n + 1) := fun τ i =>
    ulim_sub_dvd (s := fun n => (∑ j ∈ Finset.range (n + 1), T ^ j) w τ i) (fun n => by
      rw [Finset.sum_range_succ _ (n + 1), LinearMap.add_apply, Pi.add_apply, Pi.add_apply,
        add_sub_cancel_left]
      exact uPow_anti n.succ.le_succ (hT.pow_mem hw (n + 1)) τ i) n
  have := add_mem h (hT.pow_mem hw n)
  rwa [Finset.sum_range_succ, LinearMap.add_apply, ← sub_sub, sub_add_cancel] at this
end GlobalTheory.BK
