-- Prove2me | solution 1 for GlobalTheory.BK.geom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:29:22.868611+00:00
-- url     : https://prove2.me/submissions/5bea294f-0c19-4c62-a085-e9d30e344dc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_uPow_anti
import Theorems.Thm_GlobalTheory_BK_eq_zero_of_mem_uPow
import Theorems.Thm_GlobalTheory_BK_geom_sub_mem
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {K : Type} [NormedField K] {a : ℕ} {ι κ : Type}
namespace GlobalTheory.BK
theorem _root_.solution {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) : geom T w = w + T (geom T w) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_uPow fun m => uPow_anti (Nat.le_succ _) ?_
  have := sub_mem (geom_sub_mem hT hw (m + 1)) (hT m _ (geom_sub_mem hT hw m))
  convert this using 1
  simp only [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum, LinearMap.add_apply,
    Module.End.mul_apply, map_sub, pow_zero, Module.End.one_apply]
  abel
end GlobalTheory.BK
