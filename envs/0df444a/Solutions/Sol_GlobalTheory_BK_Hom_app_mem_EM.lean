-- Prove2me | solution 1 for GlobalTheory.BK.Hom.app_mem_EM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:44.010398+00:00
-- url     : https://prove2.me/submissions/e39b5ca1-6311-43c6-b6ab-2f80001f6b14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_mem_divE
import Theorems.Thm_GlobalTheory_BK_Hom_app_mem_M


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
open GlobalTheory.BK.Hom
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
omit [NormedAlgebra ℚ_[l] K] [NeZero e]
namespace GlobalTheory.BK.Hom
theorem _root_.solution {η : ℕ} {y : Vec K a ι} (hy : y ∈ P.EM η) : F.app y ∈ Q.EM η := by
  rw [mem_divE, ← map_smul]
  exact F.app_mem_M hy
end GlobalTheory.BK.Hom
