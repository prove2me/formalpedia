-- Prove2me | solution 1 for GlobalTheory.RealWeil.quad_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:17.838998+00:00
-- url     : https://prove2.me/submissions/5b6202dc-a7a5-431a-ac1a-e8a25cd3ab4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Theorems.Thm_GlobalTheory_RealWeil_dRho_comm
import Theorems.Thm_GlobalTheory_RealWeil_mul_J_symm
import Theorems.Thm_GlobalTheory_RealWeil_dRho_eq_sum
import Theorems.Thm_GlobalTheory_RealWeil_sympl_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (u : l ⊕ l → ℝ) :
    quad X * dRho u - dRho u * quad X = dRho (X *ᵥ u) := by
  set S := X * Matrix.J l ℝ with hS
  have hsym : ∀ a b, S a b = S b a := fun a b => (congrFun (congrFun (mul_J_symm hX) b) a)
  set s : l ⊕ l → ℝ := fun b => sympl (Pi.single b 1) u with hs
  have hXu : ∀ a, (X *ᵥ u) a = ∑ b, S a b * s b := by
    intro a
    have : X *ᵥ u = S *ᵥ (-(Matrix.J l ℝ *ᵥ u)) := by
      rw [mulVec_neg, mulVec_mulVec, hS, Matrix.mul_assoc, J_squared]
      simp [neg_mulVec]
    rw [this]
    simp only [hs, sympl_single]
    rfl
  set D : l ⊕ l → (Sch l →L[ℂ] Sch l) := fun a => dRho (Pi.single a 1) with hD
  have hc : ∀ a, D a * dRho u = dRho u * D a + (2 * π * I * s a : ℂ) • 1 := fun a => by
    rw [← dRho_comm]
    simp [hD]
  have h2 : ∀ a b, (D a * D b + D b * D a) * dRho u - dRho u * (D a * D b + D b * D a) =
      (4 * π * I : ℂ) • ((s b : ℂ) • D a + (s a : ℂ) • D b) := fun a b => by
    have e : ∀ a b, D a * D b * dRho u = dRho u * (D a * D b) +
        ((2 * π * I * s a : ℂ) • D b + (2 * π * I * s b : ℂ) • D a) := fun a b => by
      rw [mul_assoc, hc b, mul_add, ← mul_assoc, hc a, add_mul, mul_assoc, add_assoc]
      simp
    rw [add_mul, e, e, mul_add]
    module
  have hne : (4 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : quad X * dRho u - dRho u * quad X =
      ∑ a, ∑ b, ((S a b / 2 : ℝ) : ℂ) • ((s b : ℂ) • D a + (s a : ℂ) • D b) := by
    simp only [quad, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      ← Finset.sum_sub_distrib]
    rw [inv_smul_eq_iff₀ hne]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm (4 * π * I : ℂ), ← h2]
  rw [h3, dRho_eq_sum (X *ᵥ u)]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => ((S a b / 2 : ℝ) : ℂ) • (s a : ℂ) • D b), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hXu, ← Finset.sum_add_distrib, ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hsym b a]
  push_cast
  module
end GlobalTheory.RealWeil
