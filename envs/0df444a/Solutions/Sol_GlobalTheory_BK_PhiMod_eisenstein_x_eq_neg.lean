-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.eisenstein_x_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:08.608651+00:00
-- url     : https://prove2.me/submissions/3da37ae9-f7de-4d02-8a16-03b73765377a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_PhiMod_EN_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_plus_conn_xVec_eq


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
    (P.plus hy).EN xVec = -(P.plusInl hy).app (P.EN y - E K l e • P.zeta y) := by
  rw [EN_apply, plus_conn_xVec_eq, EN_apply, ← smul_sub, ← map_smul, ← map_neg, ← smul_neg, neg_sub]
end GlobalTheory.BK.PhiMod
