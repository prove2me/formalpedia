-- Prove2me | solution 1 for GlobalTheory.RealWeil.quad_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:37.504162+00:00
-- url     : https://prove2.me/submissions/bd448b14-468d-452e-b153-a18d1a08e2bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Theorems.Thm_GlobalTheory_RealWeil_dRho_comm
import Theorems.Thm_GlobalTheory_RealWeil_mul_J_symm
import Theorems.Thm_GlobalTheory_RealWeil_sympl_single
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inl
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inr

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
theorem _root_.solution {A B C D : Matrix l l ℝ} (hX : fromBlocks A B C D ∈ LieAlgebra.Symplectic.sp l ℝ)
    (f : Sch l) (x : EuclideanSpace ℝ l) :
    quad (fromBlocks A B C D) f x =
      (4 * π * I : ℂ)⁻¹ * ∑ j, ∑ k, (B j k : ℂ) * (∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)}
          (∂_{(EuclideanSpace.single k 1 : EuclideanSpace ℝ l)} f)) x
        - ∑ j, ∑ k, (A j k : ℂ) * x k * (∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)} f) x
        - (A.trace : ℝ) / 2 * f x - π * I * ∑ j, ∑ k, (C j k : ℂ) * x j * x k * f x := by
  have hS : fromBlocks A B C D * Matrix.J l ℝ = fromBlocks B (-A) D (-C) := by
    simp [Matrix.J, fromBlocks_multiply]
  have hsym := mul_J_symm hX
  rw [hS] at hsym
  have hD : ∀ j k, D j k = -A k j := fun j k => congrFun (congrFun hsym (Sum.inl k)) (Sum.inr j)
  have hne : (4 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  set P : l → (Sch l →L[ℂ] Sch l) := fun j => dRho (Pi.single (Sum.inl j) 1) with hP
  set Q : l → (Sch l →L[ℂ] Sch l) := fun j => dRho (Pi.single (Sum.inr j) 1) with hQ
  have hPP : ∀ j k, P k * P j = P j * P k := fun j k => by
    have := dRho_comm (l := l) (Pi.single (Sum.inl k) 1) (Pi.single (Sum.inl j) 1)
    rw [sympl_single] at this
    rw [← sub_eq_zero, this]
    simp [Matrix.J]
  have hPQ : ∀ j k, P j * Q k = Q k * P j + (2 * π * I * (if j = k then 1 else 0) : ℂ) • 1 := fun j k => by
    have := dRho_comm (l := l) (Pi.single (Sum.inl j) 1) (Pi.single (Sum.inr k) 1)
    rw [sympl_single] at this
    rw [← sub_eq_iff_eq_add', this]
    by_cases h : j = k <;> simp [Matrix.J, h, Matrix.one_apply]
  have hQa : ∀ k (g : Sch l), Q k g x = 2 * π * I * x k * g x := fun k g => dRho_single_inr k g x
  have hq : quad (fromBlocks A B C D) = (4 * π * I : ℂ)⁻¹ • ((∑ j, ∑ k, (B j k : ℂ) • (P j * P k)) -
      (∑ j, ∑ k, (2 * A j k : ℂ) • (Q k * P j)) - (2 * π * I * (A.trace : ℝ) : ℂ) • 1 -
      ∑ j, ∑ k, (C j k / 2 : ℂ) • (Q j * Q k + Q k * Q j)) := by
    rw [quad, hS]
    congr 1
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.neg_apply, hD]
    have t : (2 * π * I * (A.trace : ℝ) : ℂ) • (1 : Sch l →L[ℂ] Sch l) =
        ∑ j, ∑ k, (A j k : ℂ) • (2 * π * I * (if j = k then 1 else 0) : ℂ) • (1 : Sch l →L[ℂ] Sch l) := by
      simp only [Matrix.trace, diag_apply, ofReal_sum, Finset.mul_sum, Finset.sum_smul, smul_smul, mul_ite, mul_one,
        mul_zero, ite_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
    rw [t, Finset.sum_comm (f := fun j k => ((-A k j / 2 : ℝ) : ℂ) • _)]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    change ((B j k / 2 : ℝ) : ℂ) • (P j * P k + P k * P j) + ((-A j k / 2 : ℝ) : ℂ) • (Q k * P j + P j * Q k) +
      (((-A j k / 2 : ℝ) : ℂ) • (P j * Q k + Q k * P j) + ((-C j k / 2 : ℝ) : ℂ) • (Q j * Q k + Q k * Q j)) = _
    rw [hPP j k, hPQ j k]
    push_cast
    module
  rw [hq]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
    SchwartzMap.smul_apply, SchwartzMap.sub_apply, SchwartzMap.add_apply, SchwartzMap.sum_apply, smul_eq_mul, hQa]
  simp only [hP, dRho_single_inl, mul_sub, Finset.mul_sum]
  congr 1
  · congr 1
    · congr 1
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      field_simp
      ring
    · field_simp
      ring
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    field_simp
    ring
end GlobalTheory.RealWeil
