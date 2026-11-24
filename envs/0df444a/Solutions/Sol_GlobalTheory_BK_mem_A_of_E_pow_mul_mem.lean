-- Prove2me | solution 1 for GlobalTheory.BK.mem_A_of_E_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:13:26.965219+00:00
-- url     : https://prove2.me/submissions/899efdbf-61c9-4ddb-a491-42330426de34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_mem_A_of_E_mul_mem
import Theorems.Thm_GlobalTheory_BK_Raises_pow_mem
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
variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
namespace GlobalTheory.BK
theorem _root_.solution (m : ℕ) {h : K⟦X⟧} (hh : h ∈ Rpi O K l e)
    (hE : E K l e ^ m * h ∈ A O K) : h ∈ A O K := by
  induction m with
  | zero => simpa using hE
  | succ m ih =>
    refine ih (mem_A_of_E_mul_mem l e (mul_mem (pow_mem (E_mem l e _) m) hh) ?_)
    rwa [← mul_assoc, ← pow_succ']
end GlobalTheory.BK
