-- Prove2me | solution 1 for LeastSquaresTD.Ergodic.eq12_theta_star_finite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:12:48.223987+00:00
-- url     : https://prove2.me/submissions/3aac9f2a-fc70-46dc-b4c8-bcac5b4c9007

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD

set_option autoImplicit false

open MeasureTheory Matrix Filter Topology

namespace LSTDEq12Aux

open LeastSquaresTD.Ergodic

theorem step_bound {X : Type*} [Fintype X] (C : Chain X) (v : X → ℝ) (B : ℝ)
    (h : ∀ y, |v y| ≤ B) (x : X) : |(C.P *ᵥ v) x| ≤ B := by
  have e : (C.P *ᵥ v) x = ∑ y, C.P x y * v y := rfl
  rw [e]
  calc |∑ y, C.P x y * v y| ≤ ∑ y, |C.P x y * v y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, C.P x y * |v y| := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (C.nonneg x y)]
    _ ≤ ∑ y, C.P x y * B := by
        refine Finset.sum_le_sum fun y _ => ?_
        exact mul_le_mul_of_nonneg_left (h y) (C.nonneg x y)
    _ = B := by rw [← Finset.sum_mul, C.row_sum x, one_mul]

theorem pow_bound {X : Type*} [Fintype X] [DecidableEq X] (C : Chain X) (v : X → ℝ) (B : ℝ)
    (h : ∀ y, |v y| ≤ B) (k : ℕ) (x : X) : |((C.P ^ k) *ᵥ v) x| ≤ B := by
  induction k generalizing x with
  | zero => simpa using h x
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact step_bound C _ B ih x

theorem summable_terms {X : Type*} [Fintype X] [DecidableEq X] (C : Chain X) (v : X → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (x : X) :
    Summable (fun k : ℕ => γ ^ k * ((C.P ^ k) *ᵥ v) x) := by
  set B : ℝ := ∑ y, |v y|
  have hB : ∀ y, |v y| ≤ B := fun y =>
    Finset.single_le_sum (f := fun y => |v y|) (fun y _ => abs_nonneg (v y)) (Finset.mem_univ y)
  have hg : Summable (fun k : ℕ => γ ^ k * B) :=
    (summable_geometric_of_lt_one hγ0.le hγ1).mul_right B
  refine Summable.of_norm_bounded hg fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hγ0]
  exact mul_le_mul_of_nonneg_left (pow_bound C v B hB k x) (pow_nonneg hγ0.le k)

theorem bellman {X : Type*} [Fintype X] [DecidableEq X] (C : Chain X) (v : X → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (x : X) :
    (∑' k : ℕ, γ ^ k * ((C.P ^ k) *ᵥ v) x) =
      v x + γ * ∑ y, C.P x y * ∑' k : ℕ, γ ^ k * ((C.P ^ k) *ᵥ v) y := by
  have hs := fun y => summable_terms C v γ hγ0 hγ1 y
  rw [(hs x).tsum_eq_zero_add]
  congr 1
  · simp
  · have e : ∀ k : ℕ, γ ^ (k + 1) * ((C.P ^ (k + 1)) *ᵥ v) x =
        γ * ∑ y, C.P x y * (γ ^ k * ((C.P ^ k) *ᵥ v) y) := by
      intro k
      rw [pow_succ' γ k, pow_succ' C.P k, ← Matrix.mulVec_mulVec]
      have : (C.P *ᵥ ((C.P ^ k) *ᵥ v)) x = ∑ y, C.P x y * ((C.P ^ k) *ᵥ v) y := rfl
      rw [this, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    simp_rw [e]
    rw [tsum_mul_left, Summable.tsum_finsetSum (fun y _ => (hs y).mul_left (C.P x y))]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [tsum_mul_left]

end LSTDEq12Aux

open LeastSquaresTD.Ergodic Matrix in
theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (R : X → X → ℝ) {m : ℕ} (φ : X → Fin m → ℝ) (hφ : LinearIndependent ℝ φ)
    (hm : m = Fintype.card X) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k * ((C.P ^ k) *ᵥ C.rbar R) x)) ∧
      (∀ x, C.value R γ x = φ x ⬝ᵥ θstar) ∧
      C.rbar R = (1 - γ • C.P) *ᵥ (featureMatrix φ *ᵥ θstar) := by
  -- surjectivity of Φ
  have hrank : (featureMatrix φ).rank = Fintype.card X := by
    rw [Matrix.rank_eq_finrank_span_row]
    exact finrank_span_eq_card hφ
  have hsurj : LinearMap.range (featureMatrix φ).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨θ, hθ⟩ : ∃ θ, (featureMatrix φ).mulVecLin θ = C.value R γ := by
    have : C.value R γ ∈ LinearMap.range (featureMatrix φ).mulVecLin := by
      rw [hsurj]; exact Submodule.mem_top
    exact this
  have hθ' : featureMatrix φ *ᵥ θ = C.value R γ := hθ
  refine ⟨θ, fun x => LSTDEq12Aux.summable_terms C _ γ hγ0 hγ1 x, fun x => ?_, ?_⟩
  · rw [← hθ']; rfl
  · rw [hθ', Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    funext x
    have hb := LSTDEq12Aux.bellman C (C.rbar R) γ hγ0 hγ1 x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have : (C.P *ᵥ C.value R γ) x = ∑ y, C.P x y * C.value R γ y := rfl
    rw [this]
    unfold Chain.value
    rw [hb]
    ring
