-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.hatTot_mem_Mhat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:39.437166+00:00
-- url     : https://prove2.me/submissions/4a5e5317-33e1-4432-b604-bc00d945eaa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_hat_mem_range_iff
import Theorems.Thm_GlobalTheory_BK_PhiMod_mem_Mhat
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
theorem _root_.solution {v : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e)) :
    P.hatTot v ∈ P.Mhat ↔ v ∈ P.Man :=
  P.mem_Mhat.trans <| Iff.trans (forall₂_congr fun τ i => hat_mem_range_iff l e (mem_tot.1 hv τ i))
    (mem_tot (P := fun _ => vecs ι (Rpi O K l e))).symm
end GlobalTheory.BK.PhiMod
