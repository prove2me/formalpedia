-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.zeta_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:27.091652+00:00
-- url     : https://prove2.me/submissions/b3467cc4-7109-4e49-81ee-d3a2c7cc4ede

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_Raises_eq_zero
import Theorems.Thm_GlobalTheory_BK_PhiMod_raises_lphi
import Theorems.Thm_GlobalTheory_BK_PhiMod_zeta_mem_uPow
import Theorems.Thm_GlobalTheory_BK_PhiMod_zeta_eq

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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {y z : Vec K a ι} (h1 : z ∈ uPow K a ι 1) (h : z = P.lphi (z - P.conn y)) :
    z = P.zeta y := by
  rw [← sub_eq_zero]
  refine P.raises_lphi.eq_zero (σ := (id : Unit → Unit)) Function.surjective_id
    (δ := fun _ => z - P.zeta y) (fun _ => sub_mem h1 (P.zeta_mem_uPow y)) (fun _ => ?_) ()
  conv_lhs => rw [h, zeta_eq, ← map_sub, sub_sub_sub_cancel_right]
end GlobalTheory.BK.PhiMod
