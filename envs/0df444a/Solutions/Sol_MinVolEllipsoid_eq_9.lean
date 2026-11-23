-- Prove2me | solution 1 for MinVolEllipsoid.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:27:11.29814+00:00
-- url     : https://prove2.me/submissions/fc2f2114-4d58-4316-9bdf-f45cf205b934

import Mathlib
import Definitions.Def_MinVolEllipsoid_Zval
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_MinVolEllipsoid_GenCopositive
import Definitions.Def_MinVolEllipsoid_borderedMatrix
import Definitions.Def_MinVolEllipsoid_stackAb

set_option autoImplicit false

open Matrix MinVolEllipsoid

namespace MinVolEllipsoid.Eq9Proof

theorem qf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (v : Fin n ⊕ Unit → ℝ) :
    v ⬝ᵥ ((borderedMatrix 0 0 0 1 - (stackAb A b)ᵀ * stackAb A b) *ᵥ v) =
      v (Sum.inr ()) * v (Sum.inr ()) - (stackAb A b *ᵥ v) ⬝ᵥ (stackAb A b *ᵥ v) := by
  have h2 : v ⬝ᵥ ((stackAb A b)ᵀ *ᵥ (stackAb A b *ᵥ v)) =
      (stackAb A b *ᵥ v) ⬝ᵥ (stackAb A b *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, h2]
  congr 1
  simp [borderedMatrix, dotProduct, mulVec, fromBlocks, Fintype.sum_sum_type]

theorem stack_lift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    stackAb A b *ᵥ lift x = A *ᵥ x + b := by
  ext i
  simp [stackAb, lift, mulVec, dotProduct, Fintype.sum_sum_type]

theorem dot_self_nonneg {n : ℕ} (w : Fin n → ℝ) : 0 ≤ w ⬝ᵥ w :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))

end MinVolEllipsoid.Eq9Proof

open MinVolEllipsoid.Eq9Proof in
theorem solution {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) :
    Zval P A b ≤ 1 ↔
      GenCopositive (liftCone P)
        (borderedMatrix 0 0 0 1 - (stackAb A b)ᵀ * stackAb A b) := by
  have hcont : Continuous (fun x : Fin n → ℝ => (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b)) := by
    have h1 : Continuous (fun x : Fin n → ℝ => A *ᵥ x + b) :=
      (continuous_const.matrix_mulVec continuous_id).add continuous_const
    show Continuous (fun x => ∑ i, (A *ᵥ x + b) i * (A *ᵥ x + b) i)
    exact continuous_finset_sum _ (fun i _ =>
      ((continuous_apply i).comp h1).mul ((continuous_apply i).comp h1))
  have hbdd : BddAbove ((fun x => (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b)) '' P) :=
    (hPc.image hcont).bddAbove
  have hPne : P.Nonempty := hPi.mono interior_subset
  have hsymm : (borderedMatrix 0 0 0 1 - (stackAb A b)ᵀ * stackAb A b).IsSymm := by
    apply Matrix.IsSymm.sub
    · ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [borderedMatrix, fromBlocks]
    · unfold Matrix.IsSymm; rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  constructor
  · intro hZ
    have hpt : ∀ x ∈ P, (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b) ≤ 1 := fun x hx =>
      (le_csSup hbdd ⟨x, hx, rfl⟩).trans hZ
    refine ⟨hsymm, ?_⟩
    rintro v ⟨m, c, x, hc, hx, rfl⟩
    rw [qf]
    have hinr : (∑ s, c s • lift (x s)) (Sum.inr ()) = ∑ s, c s := by
      simp [Finset.sum_apply, lift]
    have hS : stackAb A b *ᵥ (∑ s, c s • lift (x s)) = ∑ s, c s • (A *ᵥ x s + b) := by
      rw [Matrix.mulVec_sum]
      congr 1
      funext s
      rw [Matrix.mulVec_smul, stack_lift]
    rw [hinr, hS]
    set w : Fin m → Fin n → ℝ := fun s => A *ᵥ x s + b with hw
    have hw1 : ∀ s, w s ⬝ᵥ w s ≤ 1 := fun s => hpt (x s) (hx s)
    have hwst : ∀ s t, w s ⬝ᵥ w t ≤ 1 := by
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
    have hle : ∑ s, ∑ t, c s * c t * (w s ⬝ᵥ w t) ≤ ∑ s, ∑ t, c s * c t := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      have := mul_nonneg (hc s) (hc t)
      nlinarith [hwst s t]
    have hsq : ∑ s, ∑ t, c s * c t = (∑ s, c s) * (∑ s, c s) := by
      rw [Finset.sum_mul_sum]
    linarith
  · rintro ⟨-, hcop⟩
    apply csSup_le (hPne.image _)
    rintro _ ⟨x, hx, rfl⟩
    have hmem : lift x ∈ liftCone P :=
      ⟨1, fun _ => 1, fun _ => x, fun _ => zero_le_one, fun _ => hx, by simp⟩
    have := hcop (lift x) hmem
    rw [qf, stack_lift] at this
    simp only [lift, Sum.elim_inr] at this
    linarith
