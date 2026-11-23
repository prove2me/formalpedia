-- Prove2me | solution 1 for GlobalTheory.SiegelNormalForm.siegel_of_relations
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:10.392525+00:00
-- url     : https://prove2.me/submissions/ca74d58a-aeaf-4c6c-8c29-9fbbcc9cd8d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.SiegelNormalForm
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}
namespace GlobalTheory.SiegelNormalForm
namespace _root_.GlobalTheory.SiegelNormalForm
theorem _root_.solution (Y : Matrix (Fin g) (Fin g) ℝ)
    (hY : Y.PosDef) (τ : Matrix (Fin g) (Fin g) ℂ)
    (h₁ : ∀ i j, ((Pi.single i 1 : Fin g → ℂ) ⬝ᵥ Y.map (↑) *ᵥ star (τ *ᵥ Pi.single j 1)).im =
      if i = j then -1 else 0)
    (h₂ : ∀ i j, ((τ *ᵥ Pi.single i 1) ⬝ᵥ Y.map (↑) *ᵥ star (τ *ᵥ Pi.single j 1)).im = 0) :
    τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ Y * τ.map Complex.im = 1 := by
  set B : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hBdef
  have e1 := h₁
  have e2 := h₂
  simp [mulVec, dotProduct, Complex.im_sum, Pi.single_apply] at e1 e2
  have hsymY : ∀ i j, Y j i = Y i j := fun i j => by
    simpa using hY.isHermitian.apply i j
  have hrow : ∀ a i, ∑ x, Y a x * (τ x i).im = if a = i then 1 else 0 := by
    intro a i
    have := e1 a i
    split_ifs at this ⊢ <;> linarith
  have hYB : Y * B = 1 := by
    ext a i
    simp only [mul_apply, one_apply, hBdef, map_apply]
    exact hrow a i
  have hBY : B * Y = 1 := mul_eq_one_comm.mp hYB
  have hYt : Yᵀ = Y := by
    ext i j
    exact hsymY i j
  have hBt : Bᵀ = B := by
    calc Bᵀ = Bᵀ * (Y * B) := by rw [hYB, Matrix.mul_one]
      _ = (Y * B)ᵀ * B := by rw [transpose_mul, hYt, Matrix.mul_assoc]
      _ = B := by rw [hYB, transpose_one, Matrix.one_mul]
  have hsecond : ∀ i j, ∑ x, (τ x i).im * ∑ y, Y x y * (τ y j).re = (τ i j).re := by
    intro i j
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h : ∀ y, ∑ x, (τ x i).im * (Y x y * (τ y j).re) =
        (if y = i then 1 else 0) * (τ y j).re := by
      intro y
      rw [← hrow y i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsymY y x]
      ring
    simp [h]
  have hre : ∀ i j, (τ j i).re = (τ i j).re := by
    intro i j
    have := e2 i j
    simp only [hrow, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hsecond] at this
    linarith
  have him : ∀ i j, (τ j i).im = (τ i j).im := by
    intro i j
    have := congrFun (congrFun hBt i) j
    simpa [hBdef] using this
  refine ⟨IsSymm.ext fun i j => Complex.ext (hre i j) (him i j), ?_, hYB⟩
  rw [← Matrix.inv_eq_right_inv hYB]
  exact hY.inv
end _root_.GlobalTheory.SiegelNormalForm
end GlobalTheory.SiegelNormalForm
