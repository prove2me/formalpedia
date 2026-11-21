-- Prove2me | solution 1 for NewtonianLipschitz.candidateMaximum_gt_five_halves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:58:14.453044+00:00
-- url     : https://prove2.me/submissions/003825c4-1df9-480e-8f4f-0d0947ec4a04

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_le_at_criticalPoint
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_eq
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_one
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_two
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_zero
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_one
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_two
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.swapYZIndex_one
attribute [local simp] NewtonianLipschitz.swapYZIndex_two
attribute [local simp] NewtonianLipschitz.swapYZIndex_zero
attribute [local simp] NewtonianLipschitz.swapYZVec_one
attribute [local simp] NewtonianLipschitz.swapYZVec_two
attribute [local simp] NewtonianLipschitz.swapYZVec_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution :
    (5 / 2 : ℝ) < candidateMaximum := by
  let r : ℝ := Real.sqrt ((27 : ℝ) / 25)
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.mpr (by norm_num)
  have hrsq : r ^ 2 = (27 : ℝ) / 25 := by
    dsimp [r]
    exact Real.sq_sqrt (by norm_num)
  have hrupper : r ≤ (26 : ℝ) / 25 := by
    nlinarith [hrsq]
  have hrpow : r ^ 5 ≤ ((26 : ℝ) / 25) ^ 5 :=
    pow_le_pow_left₀ hrpos.le hrupper 5
  have hnumeric :
      (5 / 2 : ℝ) * r ^ 5 < (78 : ℝ) / 25 := by
    have hrprod :
        (5 / 2 : ℝ) * r ^ 5 ≤
          (5 / 2 : ℝ) * ((26 : ℝ) / 25) ^ 5 :=
      mul_le_mul_of_nonneg_left hrpow (by norm_num)
    have hrconst :
        (5 / 2 : ℝ) * ((26 : ℝ) / 25) ^ 5 <
          (78 : ℝ) / 25 := by norm_num
    exact lt_of_le_of_lt hrprod hrconst
  have heval :
      candidateCoefficient (1 / 5 : ℝ) =
        ((78 : ℝ) / 25) / r ^ 5 := by
    rw [candidateCoefficient_eq]
    have hinside :
        1 + 2 * (1 / 5 : ℝ) ^ 2 = (27 : ℝ) / 25 := by
      norm_num
    rw [hinside]
    change (2 + 6 * (1 / 5 : ℝ) - 2 * (1 / 5 : ℝ) ^ 2) /
        r ^ 5 = ((78 : ℝ) / 25) / r ^ 5
    congr 1
    norm_num
  have hone :
      (5 / 2 : ℝ) < candidateCoefficient (1 / 5 : ℝ) := by
    rw [heval]
    exact (lt_div_iff₀ (pow_pos hrpos 5)).2 hnumeric
  have hmax :
      candidateCoefficient (1 / 5 : ℝ) ≤ candidateMaximum := by
    rw [candidateMaximum_eq]
    exact candidateCoefficient_le_at_criticalPoint (1 / 5 : ℝ)
      ⟨by norm_num, by norm_num⟩
  exact hone.trans_le hmax
end NewtonianLipschitz
