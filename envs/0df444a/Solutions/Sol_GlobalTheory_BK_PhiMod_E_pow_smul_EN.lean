-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.E_pow_smul_EN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:47.79679+00:00
-- url     : https://prove2.me/submissions/8055630a-3a68-4092-afa4-83d2cbb4db36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_PhiMod_EN_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_smul
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (n : ℕ) (y : Vec K a ι) : E K l e ^ n • P.EN y =
    P.EN (E K l e ^ n • y) - ((n : K⟦X⟧) * N K (E K l e)) • E K l e ^ n • y := by
  rw [EN_apply, EN_apply, conn_smul, Derivation.leibniz_pow]
  cases n with
  | zero => simp
  | succ n =>
    ext τ i : 2
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, Pi.smul_apply, Pi.sub_apply,
      Pi.add_apply]
    ring
end GlobalTheory.BK.PhiMod
