-- Prove2me | solution 1 for MaGoldfarbFPC.Convergence.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:49:30.442245+00:00
-- url     : https://prove2.me/submissions/ab84642d-eb57-447c-94ab-d177451314b9

import Definitions.Def_MaGoldfarbFPC_Convergence_Basic
open scoped BigOperators
open CaiCandesShen.Convergence MaGoldfarbFPC.Convergence

private abbrev Space (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)
private def vec {m n : ℕ} (X : Mat m n) : Space m n :=
  WithLp.toLp 2 (fun ij => X ij.1 ij.2)
private def unvec {m n : ℕ} (x : Space m n) : Mat m n := fun i j => x (i,j)

private lemma vec_unvec {m n : ℕ} (x : Space m n) : vec (unvec x) = x := by
  ext ij
  rfl

private lemma vec_inner {m n : ℕ} (X Y : Mat m n) :
    inner ℝ (vec X) (vec Y) = frobInner X Y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, vec, frobInner,
    Fintype.sum_prod_type, mul_comm]

private lemma vec_norm {m n : ℕ} (X : Mat m n) : ‖vec X‖ = frobNorm X := by
  rw [norm_eq_sqrt_real_inner, vec_inner]
  rfl

private lemma vec_sub {m n : ℕ} (X Y : Mat m n) : vec (X - Y) = vec X - vec Y := by
  ext ij
  rfl

private lemma vec_smul {m n : ℕ} (r : ℝ) (X : Mat m n) : vec (r • X) = r • vec X := by
  ext ij
  rfl

private def lin {m n p : ℕ} (Aop : Fin p → Mat m n) :
    Space m n →ₗ[ℝ] EuclideanSpace ℝ (Fin p) where
  toFun x := WithLp.toLp 2 (applyA Aop (unvec x))
  map_add' x y := by
    ext i
    simp [applyA, frobInner, unvec, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    ext i
    simp [applyA, frobInner, unvec, Finset.mul_sum, mul_left_comm]

private noncomputable def op {m n p : ℕ} (Aop : Fin p → Mat m n) :
    Space m n →L[ℝ] EuclideanSpace ℝ (Fin p) := (lin Aop).toContinuousLinearMap

private lemma op_vec {m n p : ℕ} (Aop : Fin p → Mat m n) (X : Mat m n) :
    op Aop (vec X) = WithLp.toLp 2 (applyA Aop X) := by
  rfl

private lemma op_norm {m n p : ℕ} (Aop : Fin p → Mat m n) :
    ‖op Aop‖ = opNormA Aop := by
  rw [← (op Aop).sSup_sphere_eq_norm]
  unfold opNormA
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨unvec x, ?_, ?_⟩
    · change frobNorm (unvec x) = 1
      rw [← vec_norm, vec_unvec]
      simpa using hx
    · change Real.sqrt (∑ i, applyA Aop (unvec x) i ^ 2) = ‖op Aop x‖
      simp [op, lin, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  · rintro ⟨X, hX, rfl⟩
    refine ⟨vec X, ?_, ?_⟩
    · simpa [vec_norm] using hX
    · change ‖op Aop (vec X)‖ = Real.sqrt (∑ i, applyA Aop X i ^ 2)
      rw [op_vec, EuclideanSpace.norm_eq]
      simp

private lemma op_adjoint {m n p : ℕ} (Aop : Fin p → Mat m n)
    (y : EuclideanSpace ℝ (Fin p)) :
    (op Aop).adjoint y = vec (adjA Aop y) := by
  apply ext_inner_right ℝ
  intro x
  rw [(op Aop).adjoint_inner_left]
  rw [← vec_unvec x, vec_inner, op_vec]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ k, applyA Aop (unvec x) k * y k) = frobInner (adjA Aop y) (unvec x)
  have hadj : ∀ i j, adjA Aop y i j = ∑ k, y k * Aop k i j := by
    intro i j
    simp [adjA, Matrix.sum_apply]
  simp only [frobInner]
  simp_rw [hadj]
  simp only [applyA, frobInner]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma abstract_step {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (τ : ℝ) (ht : 0 < τ) (hbound : τ * ‖A‖ ^ 2 < 2) (x : E) :
    ‖x - τ • A.adjoint (A x)‖ ≤ ‖x‖ ∧
      (x - τ • A.adjoint (A x) = x ↔ ‖x - τ • A.adjoint (A x)‖ = ‖x‖) := by
  let z := A.adjoint (A x)
  have hz : ‖z‖ ≤ ‖A‖ * ‖A x‖ := by
    simpa [z] using A.adjoint.le_opNorm (A x)
  have hi : inner ℝ x z = ‖A x‖ ^ 2 := by
    rw [A.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have he : ‖x - τ • z‖ ^ 2 = ‖x‖ ^ 2 - 2 * τ * ‖A x‖ ^ 2 + τ ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, hi, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    ring
  have hz2 : ‖z‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖A x‖ ^ 2 := by
    nlinarith [norm_nonneg z, norm_nonneg A, norm_nonneg (A x)]
  have hdec : ‖x - τ • z‖ ^ 2 ≤ ‖x‖ ^ 2 - τ * (2 - τ * ‖A‖ ^ 2) * ‖A x‖ ^ 2 := by
    nlinarith [sq_nonneg τ]
  have hc : 0 < τ * (2 - τ * ‖A‖ ^ 2) := mul_pos ht (by linarith)
  constructor
  · nlinarith [sq_nonneg ‖A x‖, norm_nonneg x, norm_nonneg (x - τ • z)]
  · constructor
    · intro hh
      rw [hh]
    · intro hh
      change ‖x - τ • z‖ = ‖x‖ at hh
      have ha : A x = 0 := by
        apply norm_eq_zero.mp
        rw [hh] at hdec
        have hp : τ * (2 - τ * ‖A‖ ^ 2) * ‖A x‖ ^ 2 ≤ 0 := by
          linarith only [hdec]
        have hs : ‖A x‖ ^ 2 ≤ 0 := by
          by_contra hs
          have hpos := mul_pos hc (lt_of_not_ge hs)
          linarith only [hp, hpos]
        nlinarith only [hs, norm_nonneg (A x)]
      simp [z, ha]

theorem solution {m n p : ℕ} (Aop : Fin p → Mat m n) (b : Fin p → ℝ) (τ : ℝ)
    (hτ : StepRange τ Aop) (X X' : Mat m n) :
    frobNorm (h τ Aop b X - h τ Aop b X') ≤ frobNorm (X - X') ∧
      (h τ Aop b X - h τ Aop b X' = X - X' ↔
        frobNorm (h τ Aop b X - h τ Aop b X') = frobNorm (X - X')) := by
  have hh : vec (h τ Aop b X - h τ Aop b X') =
      vec (X - X') - τ • (op Aop).adjoint (op Aop (vec (X - X'))) := by
    rw [op_vec, op_adjoint]
    simp only [h, g, vec_sub, vec_smul]
    have hg : adjA Aop (applyA Aop X - b) - adjA Aop (applyA Aop X' - b) =
        adjA Aop (applyA Aop (X - X')) := by
      ext i j
      simp [adjA, applyA, frobInner, Matrix.sum_apply, Finset.sum_sub_distrib,
        mul_sub, sub_mul]
    have hgv := congrArg vec hg
    rw [vec_sub] at hgv
    rw [← hgv, smul_sub]
    abel
  have ht := abstract_step (op Aop) τ hτ.1 (by simpa [op_norm] using hτ.2) (vec (X - X'))
  have hn := vec_norm (h τ Aop b X - h τ Aop b X')
  rw [hh] at hn
  constructor
  · simpa [hn, vec_norm] using ht.1
  · constructor
    · intro he
      rw [he]
    · intro he
      have he' : ‖vec (X - X') - τ • (op Aop).adjoint (op Aop (vec (X - X')))‖ =
          ‖vec (X - X')‖ := by simpa [hn, vec_norm] using he
      have hv := ht.2.mpr he'
      rw [← hh] at hv
      apply Matrix.ext
      intro i j
      exact congrArg (fun v : Space m n => v (i,j)) hv

#print axioms solution
