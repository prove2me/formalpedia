-- Prove2me | solution 1 for GlobalTheory.BK.filL_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:51:24.261904+00:00
-- url     : https://prove2.me/submissions/98911970-5f47-4408-8a6d-e9bd2838aa2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_mem_shiftE_of_le
import Theorems.Thm_GlobalTheory_BK_Ezpow_add
import Theorems.Thm_GlobalTheory_BK_Rot_invL
import Theorems.Thm_GlobalTheory_BK_mem_ext_rankOne
import Theorems.Thm_GlobalTheory_BK_mem_shiftE
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
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
omit [NeZero a] [TameDescentExponentData K l e a]
namespace GlobalTheory.BK
theorem _root_.solution (j i : ℤ) : (rankOne O K l e fun _ : ZMod a => j).filL i =
    shiftE l e (if i ≤ j then j else j + 1)
      ((rankOne O K l e fun _ : ZMod a => j).Mext (invL l (A O K))) := by
  set P := rankOne O K l e fun _ : ZMod a => j
  have h0 : P.ext (invL l (A O K)) = shiftE l e j (P.Mext (invL l (A O K))) := by
    ext v
    exact (mem_ext_rankOne j).trans
      ⟨fun h => mem_tot.2 fun τ _ => h τ, fun h τ => mem_tot.1 h τ ()⟩
  have h1 : shiftE l e 1 (P.ext (invL l (A O K))) =
      shiftE l e (j + 1) (P.Mext (invL l (A O K))) := by
    ext v
    rw [h0, mem_shiftE, mem_shiftE, mem_shiftE, smul_smul, ← Ezpow_add, neg_add]
  rw [PhiMod.filL, h1, h0]
  split_ifs with h
  · rw [inf_of_le_left fun _ => mem_shiftE_of_le h,
      sup_of_le_left fun _ => mem_shiftE_of_le (by omega)]
  · exact sup_of_le_right (inf_le_right.trans fun _ => mem_shiftE_of_le (by omega))
end GlobalTheory.BK
