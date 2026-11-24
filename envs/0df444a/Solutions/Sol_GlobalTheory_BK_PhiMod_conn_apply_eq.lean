-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.conn_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:24.601938+00:00
-- url     : https://prove2.me/submissions/12abe3c1-13cd-487c-acc0-e4595e145335

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_smul_tot
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_eq_sum_bas
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
variable [NormedAlgebra ℚ_[l] K] [NeZero e]
variable [CompleteSpace K]
omit [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (v : Vec K a ι) (τ : ZMod a) (i : ι) :
    P.conn v τ i = N K (v τ i) + ∑ j, v τ j * P.conn (bas j) τ i := by
  conv_lhs => rw [eq_sum_bas v]
  simp [conn_smul_tot, Finset.sum_apply, Finset.sum_add_distrib, bas, NTot, Pi.single_apply]
end GlobalTheory.BK.PhiMod
