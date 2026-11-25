-- Prove2me | solution 1 for GlobalTheory.BK.Lc_rankOneDat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:25.649739+00:00
-- url     : https://prove2.me/submissions/7cfd1492-ae53-4a92-9bcf-4b12aa2948ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_E_mul_N_Ezpow
import Theorems.Thm_GlobalTheory_BK_E_pow_mul_Ezpow_neg
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_N_E
import Theorems.Thm_GlobalTheory_BK_PhiMod_EN_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_M_le_Man
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_mem_M
import Theorems.Thm_GlobalTheory_BK_PhiMod_cls_eq_zero_iff
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_smul
import Theorems.Thm_GlobalTheory_BK_S_le_R
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
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
variable [CompleteSpace K] {j : ℤ} (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H)
namespace GlobalTheory.BK
theorem _root_.solution (χ : TameGal K l e a →* O) :
    (rankOneDat O K l e a η H j h₁ h₂ χ).Lc
        ((rankOneDat O K l e a η H j h₁ h₂ χ).cls (Ezpow K l e (-1) • bas ())) =
      (((j + 1) * e * l : ℤ) : K) •
        (rankOneDat O K l e a η H j h₁ h₂ χ).cls (Ezpow K l e (-1) • bas ()) := by
  obtain ⟨γ, hγ, h⟩ := exists_EN_bas_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
  have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h3 : (rankOneDat O K l e a η H j h₁ h₂ χ).EN (Ezpow K l e (-1) • bas ()) =
      (((j + 1) * e * l : ℤ) : K) • Ezpow K l e (-1) • (bas () : Vec K a Unit) +
        (γ - ((j + 1) * e : ℤ)) • bas () := by
    rw [PhiMod.EN_apply, PhiMod.conn_smul, smul_add, smul_comm (E K l e) (Ezpow K l e (-1)),
      ← PhiMod.EN_apply]
    erw [h]
    rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul K⟦X⟧]
    simp only [smul_smul, ← add_smul]
    congr 1
    rw [E_mul_N_Ezpow, N_E]
    rw [E] at h2 ⊢
    push_cast
    linear_combination (γ - (j + 1) * e) * h2
  rw [BKDat.Lc_cls, h3, map_add, map_smul, add_eq_left, PhiMod.cls_eq_zero_iff]
  exact PhiMod.smul_mem_Man _ (sub_mem (S_le_R l e hγ) (intCast_mem _ _))
    (PhiMod.M_le_Man _ (PhiMod.bas_mem_M _ _))
end GlobalTheory.BK
