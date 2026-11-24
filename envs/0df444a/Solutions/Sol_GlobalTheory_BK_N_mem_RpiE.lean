-- Prove2me | solution 1 for GlobalTheory.BK.N_mem_RpiE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:38.290858+00:00
-- url     : https://prove2.me/submissions/d69a7e65-233e-4641-850e-715216892eb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_N_mem
import Theorems.Thm_GlobalTheory_BK_derivative_mem_R
import Theorems.Thm_GlobalTheory_BK_derivative_mem_away


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
variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
omit [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
namespace GlobalTheory.BK
theorem _root_.solution {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) : N K f ∈ RpiE O K l e :=
  N_mem (derivative_mem_away _ (fun _ => derivative_mem_R l) hf)
end GlobalTheory.BK
