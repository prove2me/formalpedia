-- Prove2me | solution 1 for GlobalTheory.BK.jumps_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:15:39.593678+00:00
-- url     : https://prove2.me/submissions/09a7b647-44df-46f9-8205-5418c73c76f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_Ezpow_mem_invL_A_iff
import Theorems.Thm_GlobalTheory_BK_filL_rankOne
import Theorems.Thm_GlobalTheory_BK_Ezpow_add
import Theorems.Thm_GlobalTheory_BK_Ezpow_neg_mul
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_PhiMod_Mext_mono
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_mem_M
import Theorems.Thm_GlobalTheory_BK_Rot_invL
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_mem_shiftE
import Theorems.Thm_GlobalTheory_BK_mem_tot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



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
theorem _root_.solution (j : ℤ) : (rankOne O K l e fun _ : ZMod a => j).jumps = {j} := by
  ext i
  simp only [PhiMod.jumps, Set.mem_ofPred_eq, filL_rankOne, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hi
    exact h (by simp only [show i + 1 ≤ j ↔ i ≤ j by omega])
  · rintro rfl h
    rw [if_neg (by omega), if_pos le_rfl] at h
    have h1 : Ezpow K l e i • (bas () : Vec K a Unit) ∈ shiftE l e i
        ((rankOne O K l e fun _ : ZMod a => i).Mext (invL l (A O K))) := by
      rw [mem_shiftE, smul_smul, Ezpow_neg_mul, one_smul]
      exact PhiMod.Mext_mono _ (le_away _ _)
        ((rankOne O K l e fun _ : ZMod a => i).bas_mem_M ())
    rw [← h, mem_shiftE, smul_smul, ← Ezpow_add] at h1
    have h2 := mem_tot.1 h1 0 ()
    simp only [bas, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      Ezpow_mem_invL_A_iff] at h2
    omega
end GlobalTheory.BK
