-- Prove2me | solution 1 for MinVolEllipsoid.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:02:10.700614+00:00
-- url     : https://prove2.me/submissions/c80deb0d-443b-4390-b75d-85f6b4933a85

import Mathlib
import Definitions.Def_MinVolEllipsoid_Zval
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_MinVolEllipsoid_GenCopositive
import Definitions.Def_MinVolEllipsoid_borderedMatrix

set_option autoImplicit false

open Matrix MinVolEllipsoid

namespace MinVolEllipsoid.Eq8Proof

def localStack {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Matrix (Fin n) (Fin n ⊕ Unit) ℝ :=
  Matrix.of fun i j => Sum.elim (fun k => A i k) (fun _ => b i) j

theorem qf_rho {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (ρ : ℝ)
    (v : Fin n ⊕ Unit → ℝ) :
    v ⬝ᵥ ((borderedMatrix 0 0 0 ρ - (localStack A b)ᵀ * localStack A b) *ᵥ v) =
      ρ * v (Sum.inr ()) * v (Sum.inr ()) - (localStack A b *ᵥ v) ⬝ᵥ (localStack A b *ᵥ v) := by
  have h2 : v ⬝ᵥ ((localStack A b)ᵀ *ᵥ (localStack A b *ᵥ v)) =
      (localStack A b *ᵥ v) ⬝ᵥ (localStack A b *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, h2]
  congr 1
  simp [borderedMatrix, dotProduct, mulVec, fromBlocks, Fintype.sum_sum_type]
  ring

theorem stack_lift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    localStack A b *ᵥ lift x = A *ᵥ x + b := by
  ext i
  simp [localStack, lift, mulVec, dotProduct, Fintype.sum_sum_type]

theorem dual_eq_stack {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hAsymm : A.IsSymm)
    (b : Fin n → ℝ) (ρ : ℝ) :
    borderedMatrix (-(A * A)) (-(A *ᵥ b)) (-(b ᵥ* A)) (ρ - b ⬝ᵥ b) =
      borderedMatrix 0 0 0 ρ - (localStack A b)ᵀ * localStack A b := by
  have hAt : ∀ i j, A i j = A j i := fun i j => by
    have := congr_fun (congr_fun hAsymm.eq i) j
    simpa [Matrix.transpose_apply] using this.symm
  have hbA : b ᵥ* A = A *ᵥ b := by
    rw [← Matrix.mulVec_transpose, hAsymm.eq]
  ext i j
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
  · simp only [borderedMatrix, fromBlocks_apply₁₁, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, localStack, of_apply,
      Sum.elim_inl]
    have : ∑ k, A k i * A k j = ∑ k, A i k * A k j :=
      Finset.sum_congr rfl fun k _ => by rw [hAt k i]
    rw [this]
    ring
  · simp only [borderedMatrix, fromBlocks_apply₁₂, replicateCol, Matrix.sub_apply, Pi.neg_apply,
      Pi.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, localStack, of_apply,
      Sum.elim_inl, Sum.elim_inr, mulVec, dotProduct]
    have : ∑ k, A k i * b k = ∑ k, A i k * b k :=
      Finset.sum_congr rfl fun k _ => by rw [hAt k i]
    rw [this]
    ring
  · simp only [borderedMatrix, hbA, fromBlocks_apply₂₁, replicateRow, Matrix.sub_apply,
      Pi.neg_apply, Pi.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, localStack, of_apply,
      Sum.elim_inl, Sum.elim_inr, mulVec, dotProduct]
    have : ∑ k, b k * A k j = ∑ k, A j k * b k :=
      Finset.sum_congr rfl fun k _ => by rw [hAt k j, mul_comm]
    rw [this]
    ring
  · simp only [borderedMatrix, fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.transpose_apply, localStack, of_apply, Sum.elim_inr, dotProduct]

theorem dot_self_nonneg {n : ℕ} (w : Fin n → ℝ) : 0 ≤ w ⬝ᵥ w :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))

end MinVolEllipsoid.Eq8Proof

open MinVolEllipsoid.Eq8Proof in
theorem solution {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) :
    IsLeast {ρ : ℝ | GenCopositive (liftCone P)
        (borderedMatrix (-(A * A)) (-(A *ᵥ b)) (-(b ᵥ* A)) (ρ - b ⬝ᵥ b))}
      (Zval P A b) := by
  have hAsymm : A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.1
  have hcont : Continuous (fun x : Fin n → ℝ => (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b)) := by
    have h1 : Continuous (fun x : Fin n → ℝ => A *ᵥ x + b) :=
      (continuous_const.matrix_mulVec continuous_id).add continuous_const
    show Continuous (fun x => ∑ i, (A *ᵥ x + b) i * (A *ᵥ x + b) i)
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp h1).mul ((continuous_apply i).comp h1))
  have hbdd : BddAbove ((fun x => (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b)) '' P) :=
    (hPc.image hcont).bddAbove
  have hPne : P.Nonempty := hPi.mono interior_subset
  have hsymm : ∀ ρ : ℝ, (borderedMatrix 0 0 0 ρ - (localStack A b)ᵀ * localStack A b).IsSymm := by
    intro ρ
    apply Matrix.IsSymm.sub
    · ext i j
      rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;> simp [borderedMatrix, fromBlocks]
    · unfold Matrix.IsSymm; rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  constructor
  · set ρ₀ := Zval P A b
    change GenCopositive (liftCone P)
      (borderedMatrix (-(A * A)) (-(A *ᵥ b)) (-(b ᵥ* A)) (ρ₀ - b ⬝ᵥ b))
    rw [dual_eq_stack A hAsymm b ρ₀]
    have hpt : ∀ x ∈ P, (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b) ≤ ρ₀ := fun x hx =>
      le_csSup hbdd ⟨x, hx, rfl⟩
    refine ⟨hsymm ρ₀, ?_⟩
    rintro v ⟨m, c, x, hc, hx, rfl⟩
    rw [qf_rho]
    have hinr : (∑ s, c s • lift (x s)) (Sum.inr ()) = ∑ s, c s := by
      simp [Finset.sum_apply, lift]
    have hS : localStack A b *ᵥ (∑ s, c s • lift (x s)) = ∑ s, c s • (A *ᵥ x s + b) := by
      rw [Matrix.mulVec_sum]
      congr 1
      funext s
      rw [Matrix.mulVec_smul, stack_lift]
    rw [hinr, hS]
    set w : Fin m → Fin n → ℝ := fun s => A *ᵥ x s + b
    have hw1 : ∀ s, w s ⬝ᵥ w s ≤ ρ₀ := fun s => hpt (x s) (hx s)
    have hwst : ∀ s t, w s ⬝ᵥ w t ≤ ρ₀ := by
      intro s t
      have h0 := dot_self_nonneg (w s - w t)
      simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm (w t) (w s)] at h0
      linarith [hw1 s, hw1 t]
    have hexp : (∑ s, c s • w s) ⬝ᵥ (∑ t, c t • w t) = ∑ s, ∑ t, c s * c t * (w s ⬝ᵥ w t) := by
      rw [sum_dotProduct]
      apply Finset.sum_congr rfl
      intro s _
      rw [dotProduct_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hexp]
    have hle : ∑ s, ∑ t, c s * c t * (w s ⬝ᵥ w t) ≤ ∑ s, ∑ t, c s * c t * ρ₀ := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (hwst s t) (mul_nonneg (hc s) (hc t))
    have hsq : ∑ s, ∑ t, c s * c t * ρ₀ = ρ₀ * (∑ s, c s) * (∑ s, c s) := by
      have : ∑ s, ∑ t, c s * c t * ρ₀ = (∑ s, ∑ t, c s * c t) * ρ₀ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => (Finset.sum_mul _ _ _).symm
      rw [this, ← Finset.sum_mul_sum]
      ring
    linarith
  · intro ρ hρ
    change GenCopositive (liftCone P)
      (borderedMatrix (-(A * A)) (-(A *ᵥ b)) (-(b ᵥ* A)) (ρ - b ⬝ᵥ b)) at hρ
    rw [dual_eq_stack A hAsymm b ρ] at hρ
    obtain ⟨-, hcop⟩ := hρ
    apply csSup_le (hPne.image _)
    rintro _ ⟨x, hx, rfl⟩
    have hmem : lift x ∈ liftCone P :=
      ⟨1, fun _ => 1, fun _ => x, fun _ => zero_le_one, fun _ => hx, by simp⟩
    have h := hcop (lift x) hmem
    rw [qf_rho, stack_lift] at h
    simp only [lift, Sum.elim_inr] at h
    linarith
