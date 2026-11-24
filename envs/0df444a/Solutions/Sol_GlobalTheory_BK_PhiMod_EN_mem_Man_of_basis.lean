-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.EN_mem_Man_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:20:42.86324+00:00
-- url     : https://prove2.me/submissions/27696af6-f9a0-4006-8836-1172692be19d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_N_mem
import Theorems.Thm_GlobalTheory_BK_PhiMod_EN_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_M_le_Man
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_mem_M
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_smul_tot
import Theorems.Thm_GlobalTheory_BK_PhiMod_smul_tot_mem_Mext
import Theorems.Thm_GlobalTheory_BK_derivative_mem_R
import Theorems.Thm_GlobalTheory_BK_eq_sum_bas
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
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.PhiMod
omit [NeZero a] [TameDescentExponentData K l e a]
variable (P : PhiMod O K l e a ι)
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (h : ∀ i, P.EN (bas i) ∈ P.Man) {m : Vec K a ι} (hm : m ∈ P.Man) :
    P.EN m ∈ P.Man := by
  rw [eq_sum_bas m, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc (τ) : m τ i ∈ Rpi O K l e := mem_tot.1 hm τ i
  rw [EN_apply, conn_smul_tot, smul_add, smul_comm (E K l e) (fun τ => m τ i)]
  exact add_mem (P.smul_mem_Man (E_mem l e _) (P.smul_tot_mem_Mext
    (fun τ => N_mem (derivative_mem_R l (hc τ))) (P.M_le_Man (P.bas_mem_M i))))
    (P.smul_tot_mem_Mext hc (h i))
end GlobalTheory.BK.PhiMod
