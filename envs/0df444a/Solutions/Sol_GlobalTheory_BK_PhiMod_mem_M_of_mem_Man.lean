-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.mem_M_of_mem_Man
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:31:02.261744+00:00
-- url     : https://prove2.me/submissions/c0c334d5-777e-41c3-bb50-b1e41e9f7dc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_mem_A_of_E_pow_mul_mem
import Theorems.Thm_GlobalTheory_BK_mem_tot


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
variable [NormedAlgebra ℚ_[l] K] [NeZero e]
variable [CompleteSpace K]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {η : ℕ} {y : Vec K a ι} (hy : y ∈ P.EM η) (h : y ∈ P.Man) : y ∈ P.M :=
  mem_tot.2 fun τ i => mem_A_of_E_pow_mul_mem l e η (mem_tot.1 h τ i) (mem_tot.1 hy τ i)
end GlobalTheory.BK.PhiMod
