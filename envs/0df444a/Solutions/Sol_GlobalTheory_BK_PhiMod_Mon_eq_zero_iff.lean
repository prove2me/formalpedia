-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.Mon_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:14:04.5568+00:00
-- url     : https://prove2.me/submissions/0addbaba-214f-4b4f-aeb2-3f1c65f3fbe8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_PhiMod_mem_Man
import Theorems.Thm_GlobalTheory_BK_PhiMod_cls_eq_zero_iff
import Theorems.Thm_GlobalTheory_BK_PhiMod_Mon_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_eisenstein_x_eq_neg
import Theorems.Thm_GlobalTheory_BK_PhiMod_plusInl_app


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
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) :
    P.Mon y = 0 ↔ (P.plus hy).EN xVec ∈ (P.plus hy).Man := by
  rw [eisenstein_x_eq_neg, neg_mem_iff, plusInl_app, mem_Man, P.join_mem_Mext hy, Mon_apply, cls_eq_zero_iff]
  exact ⟨fun h => ⟨h, fun _ => zero_mem _⟩, fun h => h.1⟩
end GlobalTheory.BK.PhiMod
