-- Prove2me | solution 1 for MinVolEllipsoid.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:58:33.038589+00:00
-- url     : https://prove2.me/submissions/dcbddcb0-2d08-47c0-b3b4-4794325f94cf

import Mathlib
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_MinVolEllipsoid_GenCopositive
import Definitions.Def_MinVolEllipsoid_borderedMatrix
import Definitions.Def_MinVolEllipsoid_ineq3Right
import Definitions.Def_ConvexOptimization_ellipsoidBody

set_option autoImplicit false

open Matrix MinVolEllipsoid

namespace MinVolEllipsoid.Thm1Proof

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

theorem bordered_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hAsymm : A.IsSymm) (b : Fin n → ℝ) :
    -(borderedMatrix (A * A) (A *ᵥ b) (A *ᵥ b) (b ⬝ᵥ b - 1)) =
      borderedMatrix 0 0 0 1 - (stackAb A b)ᵀ * stackAb A b := by
  have hAt : ∀ i j, A i j = A j i := fun i j => by
    have := congr_fun (congr_fun hAsymm.eq i) j
    exact (by simpa [Matrix.transpose_apply] using this : A j i = A i j).symm
  ext i j
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
  · simp only [Matrix.neg_apply, Matrix.sub_apply, borderedMatrix, fromBlocks_apply₁₁,
      Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, stackAb, of_apply,
      Sum.elim_inl]
    have : ∑ k, A k i * A k j = ∑ k, A i k * A k j :=
      Finset.sum_congr rfl fun k _ => by rw [hAt k i]
    rw [this]
    ring
  · simp only [Matrix.neg_apply, Matrix.sub_apply, borderedMatrix, fromBlocks_apply₁₂,
      replicateCol, Pi.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, stackAb,
      of_apply, Sum.elim_inl, Sum.elim_inr, mulVec, dotProduct]
    have : ∑ k, A k i * b k = ∑ k, A i k * b k :=
      Finset.sum_congr rfl fun k _ => by rw [hAt k i]
    rw [this]
    ring
  · simp only [Matrix.neg_apply, Matrix.sub_apply, borderedMatrix, fromBlocks_apply₂₁,
      replicateRow, Pi.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, stackAb,
      of_apply, Sum.elim_inl, Sum.elim_inr, mulVec, dotProduct]
    have : ∑ k, b k * A k j = ∑ k, A j k * b k :=
      Finset.sum_congr rfl fun k _ => by rw [hAt k j, mul_comm]
    rw [this]
    ring
  · simp only [Matrix.neg_apply, Matrix.sub_apply, borderedMatrix, fromBlocks_apply₂₂,
      Matrix.mul_apply, Matrix.transpose_apply, stackAb, of_apply, Sum.elim_inr, dotProduct]
    ring

theorem gram_ineq3Right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hAsymm : A.IsSymm)
    (b : Fin n → ℝ) :
    (ineq3Right A b (A * A) (A *ᵥ b) (b ⬝ᵥ b)).PosSemidef := by
  have hAt : ∀ i j, A i j = A j i := fun i j => by
    have := congr_fun (congr_fun hAsymm.eq i) j
    exact (by simpa [Matrix.transpose_apply] using this : A j i = A i j).symm
  let M : Matrix (Fin n) ((Fin n ⊕ Unit) ⊕ Fin n) ℝ :=
    Matrix.of fun k idx => Sum.elim (fun ij => stackAb A b k ij)
      (fun j => (1 : Matrix (Fin n) (Fin n) ℝ) k j) idx
  have heq : ineq3Right A b (A * A) (A *ᵥ b) (b ⬝ᵥ b) = Mᴴ * M := by
    ext r c
    rcases r with (i | ⟨⟩) | i <;> rcases c with (j | ⟨⟩) | j
    · simp only [ineq3Right, borderedMatrix, fromBlocks_apply₁₁, M, Matrix.mul_apply,
        Matrix.conjTranspose_apply, star_trivial, of_apply, Sum.elim_inl, stackAb]
      exact Finset.sum_congr rfl fun k _ => by rw [hAt k i]
    · simp only [ineq3Right, borderedMatrix, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        replicateCol, M, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, of_apply,
        Sum.elim_inl, Sum.elim_inr, stackAb, mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ => by rw [hAt k i]
    · simp only [ineq3Right, fromBlocks_apply₁₂, M, Matrix.mul_apply,
        Matrix.conjTranspose_apply, star_trivial, of_apply, Sum.elim_inl, Sum.elim_inr,
        stackAb, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      exact hAt i j
    · simp only [ineq3Right, borderedMatrix, fromBlocks_apply₁₁, fromBlocks_apply₂₁,
        replicateRow, M, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, of_apply,
        Sum.elim_inl, Sum.elim_inr, stackAb, mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ => by rw [hAt j k, mul_comm]
    · simp only [ineq3Right, borderedMatrix, fromBlocks_apply₁₁, fromBlocks_apply₂₂,
        M, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, of_apply,
        Sum.elim_inl, Sum.elim_inr, stackAb, dotProduct]
    · simp only [ineq3Right, fromBlocks_apply₁₂, M, Matrix.mul_apply,
        Matrix.conjTranspose_apply, star_trivial, of_apply, Sum.elim_inl, Sum.elim_inr,
        stackAb, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
    · simp only [ineq3Right, fromBlocks_apply₂₁, M, Matrix.mul_apply,
        Matrix.conjTranspose_apply, star_trivial, of_apply, Sum.elim_inl, Sum.elim_inr,
        stackAb, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
    · simp only [ineq3Right, fromBlocks_apply₂₁, M, Matrix.mul_apply,
        Matrix.conjTranspose_apply, star_trivial, of_apply, Sum.elim_inl, Sum.elim_inr,
        stackAb, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
    · simp only [ineq3Right, fromBlocks_apply₂₂, M, Matrix.mul_apply,
        Matrix.conjTranspose_apply, star_trivial, of_apply, Sum.elim_inr,
        Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self M

end MinVolEllipsoid.Thm1Proof

open MinVolEllipsoid.Thm1Proof in
theorem solution {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) :
    P ⊆ ConvexOptimization.ellipsoidBody A b ↔
      ∃ (F : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (h : ℝ), F.IsSymm ∧
        GenCopositive (liftCone P) (-(borderedMatrix F g g (h - 1))) ∧
        (ineq3Right A b F g h).PosSemidef := by
  have hAsymm : A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.1
  constructor
  · intro hsub
    refine ⟨A * A, A *ᵥ b, b ⬝ᵥ b, ?_, ?_, gram_ineq3Right A hAsymm b⟩
    · unfold Matrix.IsSymm
      rw [Matrix.transpose_mul, hAsymm.eq]
    · rw [bordered_eq A hAsymm b]
      have hsymm : (borderedMatrix 0 0 0 1 - (stackAb A b)ᵀ * stackAb A b).IsSymm := by
        rw [← bordered_eq A hAsymm b]
        ext i j
        rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
        · simp only [Matrix.transpose_apply, Matrix.neg_apply, borderedMatrix, fromBlocks_apply₁₁]
          have hAA : (A * A)ᵀ = A * A := by rw [Matrix.transpose_mul, hAsymm.eq]
          exact congr_arg Neg.neg (congr_fun (congr_fun hAA i) j)
        · simp [borderedMatrix]
        · simp [borderedMatrix]
        · simp [borderedMatrix]
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
      set w : Fin m → Fin n → ℝ := fun s => A *ᵥ x s + b
      have hw1 : ∀ s, w s ⬝ᵥ w s ≤ 1 := fun s => hsub (hx s)
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
  · rintro ⟨F, g, h, -, ⟨-, hcop⟩, hpsd⟩ x hx
    change (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b) ≤ 1
    set u : Fin n ⊕ Unit → ℝ := lift x
    set z : Fin n → ℝ := stackAb A b *ᵥ u
    have hz : z = A *ᵥ x + b := stack_lift A b x
    have hu_mem : u ∈ liftCone P :=
      ⟨1, fun _ => 1, fun _ => x, fun _ => zero_le_one, fun _ => hx, by simp [u]⟩
    have hc1 := hcop u hu_mem
    have hbord_sub : -(borderedMatrix F g g (h - 1)) =
        borderedMatrix 0 0 0 1 - borderedMatrix F g g h := by
      ext i j
      rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;> simp [borderedMatrix] <;> ring
    have hc1' : 0 ≤ 1 - u ⬝ᵥ (borderedMatrix F g g h *ᵥ u) := by
      rw [hbord_sub, Matrix.sub_mulVec, dotProduct_sub] at hc1
      have hu1 : u ⬝ᵥ (borderedMatrix 0 0 0 1 *ᵥ u) = 1 := by
        simp [u, lift, borderedMatrix, dotProduct, mulVec, fromBlocks, Fintype.sum_sum_type]
      linarith
    let w : (Fin n ⊕ Unit) ⊕ Fin n → ℝ := Sum.elim u (-z)
    have hpsd_w : 0 ≤ w ⬝ᵥ (ineq3Right A b F g h *ᵥ w) := by
      have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 w
      simpa using this
    have hur : (Matrix.of fun i j => Sum.elim (fun k => A k j) (fun _ : Unit => b j) i) =
        (stackAb A b)ᵀ := by
      ext i j
      rcases i with k | ⟨⟩
      · simp only [of_apply, Sum.elim_inl, Matrix.transpose_apply, stackAb]
        have := congr_fun (congr_fun hAsymm.eq j) k
        simpa [Matrix.transpose_apply] using this
      · simp only [of_apply, Sum.elim_inr, Matrix.transpose_apply, stackAb]
    have hpsd_exp : w ⬝ᵥ (ineq3Right A b F g h *ᵥ w) =
        u ⬝ᵥ (borderedMatrix F g g h *ᵥ u) - z ⬝ᵥ z := by
      unfold ineq3Right
      rw [hur]
      have hw_mul : fromBlocks (borderedMatrix F g g h) (stackAb A b)ᵀ (stackAb A b) 1 *ᵥ w =
          Sum.elim (borderedMatrix F g g h *ᵥ u + (stackAb A b)ᵀ *ᵥ (-z))
            (stackAb A b *ᵥ u + (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ (-z)) := by
        simp [w, fromBlocks_mulVec]
      rw [hw_mul]
      have hsum_dot : ∀ (p₁ p₂ : Fin n ⊕ Unit → ℝ) (q₁ q₂ : Fin n → ℝ),
          Sum.elim p₁ q₁ ⬝ᵥ Sum.elim p₂ q₂ = p₁ ⬝ᵥ p₂ + q₁ ⬝ᵥ q₂ := by
        intro p₁ p₂ q₁ q₂
        simp [dotProduct, Fintype.sum_sum_type]
      rw [hsum_dot, Matrix.one_mulVec, Matrix.mulVec_neg, dotProduct_add, dotProduct_neg]
      have hut : u ⬝ᵥ ((stackAb A b)ᵀ *ᵥ z) = z ⬝ᵥ z := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      have hzu : stackAb A b *ᵥ u = z := rfl
      rw [hut, hzu]
      simp only [dotProduct_add, neg_dotProduct, dotProduct_neg]
      ring
    rw [hpsd_exp, hz] at hpsd_w
    linarith
