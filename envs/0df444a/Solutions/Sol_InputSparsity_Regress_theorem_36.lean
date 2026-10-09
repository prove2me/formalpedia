-- Prove2me | solution 1 for InputSparsity.Regress.theorem_36
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T16:38:34.654975+00:00
-- url     : https://prove2.me/submissions/d66a76e2-6a65-4172-89e5-67ac73cad23d

import Mathlib
import Definitions.Def_InputSparsity_Regress_Basic

set_option autoImplicit false
open Matrix InputSparsity.Embed InputSparsity.Regress
namespace SketchedRegressionQuadratic
def pair {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, C i j * D i j
lemma pair_self {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) : pair C C = frobSq C := by
  simp only [pair,frobSq,pow_two]
lemma pair_comm {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) : pair C D = pair D C := by
  simp only [pair,mul_comm]
lemma frobSq_add_smul {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) :
    frobSq (C + t • D) = frobSq C + 2 * t * pair C D + t^2 * frobSq D := by
  unfold frobSq pair
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  calc
    _ = ∑ i, ∑ j, (C i j ^ 2 + (2*t)*(C i j*D i j) + t^2*D i j^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum]
lemma linear_coefficient_zero (a b : ℝ) (h : ∀ t : ℝ, 0 ≤ a*(t*t) + 2*b*t + 0) : b = 0 := by
  have hd := discrim_le_zero h
  simp only [discrim,mul_zero,sub_zero] at hd
  nlinarith [sq_nonneg b]
lemma minimizer_pair_zero {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (hX : IsLSMinimizer C D Xstar) (Z : Matrix (Fin d) (Fin m) ℝ) :
    pair (C * Xstar - D) (C * Z) = 0 := by
  apply linear_coefficient_zero (frobSq (C*Z))
  intro t
  have hh := hX (Xstar + t • Z)
  have he : C * (Xstar + t • Z) - D = (C*Xstar-D) + t • (C*Z) := by
    rw [Matrix.mul_add,Matrix.mul_smul]
    module
  rw [he,frobSq_add_smul] at hh
  nlinarith
lemma pair_mul_left {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (Z : Matrix (Fin d) (Fin m) ℝ) (R : Matrix (Fin n) (Fin m) ℝ) :
    pair (C*Z) R = pair Z (Cᵀ*R) := by
  unfold pair
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun (i : Fin n) (j : Fin m) => ∑ k, C i k * Z k j * R i j),
    Finset.sum_comm (f := fun (k : Fin d) (j : Fin m) => ∑ i, Z k j * (C i k * R i j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  ring
lemma frobSq_zero_iff {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) : frobSq C = 0 ↔ C = 0 := by
  constructor
  · intro h
    ext i j
    have hi : (∑ j, C i j ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _)).mp h i (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg (C i j))).mp hi j (Finset.mem_univ _)
    simpa only [Matrix.zero_apply] using (sq_eq_zero_iff.mp hij)
  · rintro rfl
    simp [frobSq]
lemma normal_equations {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (hX : IsLSMinimizer C D Xstar) : Cᵀ*(C*Xstar-D) = 0 := by
  apply (frobSq_zero_iff _).mp
  have hh := minimizer_pair_zero C D Xstar hX (Cᵀ*(C*Xstar-D))
  rw [pair_comm,pair_mul_left,pair_self] at hh
  exact hh
lemma frobSq_nonneg {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) : 0 ≤ frobSq C := by
  exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _
lemma residual_column_orthogonal {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (hX : IsLSMinimizer C D Xstar) (x : Fin d → ℝ) :
    (C *ᵥ x) ᵥ* (C*Xstar-D) = 0 := by
  rw [Matrix.vecMul_mulVec,normal_equations C D Xstar hX,Matrix.vecMul_zero]
lemma error_decomposition {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (hX : IsLSMinimizer C D Xstar) (X : Matrix (Fin d) (Fin m) ℝ) :
    frobSq (C*X-D) = frobSq (C*(X-Xstar)) + frobSq (C*Xstar-D) := by
  have he : C*X-D = (C*Xstar-D) + (1 : ℝ) • (C*(X-Xstar)) := by
    rw [Matrix.mul_sub,one_smul]
    module
  rw [he,frobSq_add_smul,minimizer_pair_zero C D Xstar hX (X-Xstar)]
  ring
lemma normal_equations_minimizer {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (h : Cᵀ*(C*Xstar-D) = 0) : IsLSMinimizer C D Xstar := by
  intro X
  have hz : pair (C*Xstar-D) (C*(X-Xstar)) = 0 := by
    rw [pair_comm,pair_mul_left,h]
    simp [pair]
  have he : C*X-D = (C*Xstar-D) + (1 : ℝ) • (C*(X-Xstar)) := by
    rw [Matrix.mul_sub,one_smul]
    module
  rw [he,frobSq_add_smul,hz]
  nlinarith [frobSq_nonneg (C*(X-Xstar))]
lemma penrose_normal_equations {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (G : Matrix (Fin d) (Fin n) ℝ)
    (hG : IsMoorePenrose C G) : Cᵀ*(C*(G*D)-D) = 0 := by
  have hc : Cᵀ*(C*G) = Cᵀ := by
    have ht := congrArg Matrix.transpose hG.1
    rw [Matrix.transpose_mul,hG.2.2.1] at ht
    exact ht
  rw [Matrix.mul_sub,← Matrix.mul_assoc C G D,← Matrix.mul_assoc,hc,sub_self]
lemma penrose_minimizer {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (G : Matrix (Fin d) (Fin n) ℝ)
    (hG : IsMoorePenrose C G) : IsLSMinimizer C D (G*D) :=
  normal_equations_minimizer C D (G*D) (penrose_normal_equations C D G hG)
end SketchedRegressionQuadratic
#print axioms SketchedRegressionQuadratic.pair_self
#print axioms SketchedRegressionQuadratic.pair_comm
#print axioms SketchedRegressionQuadratic.frobSq_add_smul
#print axioms SketchedRegressionQuadratic.linear_coefficient_zero
#print axioms SketchedRegressionQuadratic.minimizer_pair_zero
#print axioms SketchedRegressionQuadratic.pair_mul_left
#print axioms SketchedRegressionQuadratic.frobSq_zero_iff
#print axioms SketchedRegressionQuadratic.normal_equations
#print axioms SketchedRegressionQuadratic.frobSq_nonneg
#print axioms SketchedRegressionQuadratic.residual_column_orthogonal
#print axioms SketchedRegressionQuadratic.error_decomposition
#print axioms SketchedRegressionQuadratic.normal_equations_minimizer
#print axioms SketchedRegressionQuadratic.penrose_normal_equations
#print axioms SketchedRegressionQuadratic.penrose_minimizer

set_option autoImplicit false
open Matrix InputSparsity.Embed InputSparsity.Regress SketchedRegressionQuadratic
namespace SketchedRegressionColumns
lemma factor_of_range_le {n d k : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ)
    (h : LinearMap.range (Matrix.mulVecLin A) ≤ LinearMap.range (Matrix.mulVecLin U)) :
    ∃ V : Matrix (Fin k) (Fin d) ℝ, U*V = A := by
  classical
  have hc : ∀ j : Fin d, ∃ v : Fin k → ℝ, U *ᵥ v = fun i => A i j := by
    intro j
    have hj : (fun i => A i j) ∈ LinearMap.range (Matrix.mulVecLin A) := by
      refine ⟨Pi.single j 1,?_⟩
      ext i
      change (A *ᵥ Pi.single j 1) i = A i j
      simp only [Matrix.mulVec_single_one,Matrix.col_apply]
    obtain ⟨v,hv⟩ := h hj
    exact ⟨v,hv⟩
  choose v hv using hc
  refine ⟨fun i j => v j i,?_⟩
  ext i j
  exact congrFun (hv j) i
lemma basis_factorization {n d k : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (hU : IsOrthonormalBasisOf U A) :
    (∃ V : Matrix (Fin k) (Fin d) ℝ, U*V = A) ∧
    (∃ W : Matrix (Fin d) (Fin k) ℝ, A*W = U) := by
  exact ⟨factor_of_range_le A U (le_of_eq hU.2.symm),factor_of_range_le U A (le_of_eq hU.2)⟩
lemma basis_dimension_le_rank {n d k : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (hU : IsOrthonormalBasisOf U A) : k ≤ A.rank := by
  obtain ⟨W,hW⟩ := (basis_factorization A U hU).2
  have h₁ := Matrix.rank_mul_le_right Uᵀ U
  have h₂ := Matrix.rank_mul_le_left A W
  rw [hU.1,Matrix.rank_one] at h₁
  rw [hW] at h₂
  simpa using h₁.trans h₂
lemma orthonormal_frobSq_mul {n k m : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (hU : HasOrthonormalCols U) (Z : Matrix (Fin k) (Fin m) ℝ) : frobSq (U*Z) = frobSq Z := by
  rw [← pair_self,pair_mul_left,← Matrix.mul_assoc,hU,Matrix.one_mul,pair_self]
lemma orthonormal_frobSq {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (hU : HasOrthonormalCols U) : frobSq U = k := by
  have hc : ∀ j : Fin k, ∑ i : Fin n, U i j ^ 2 = 1 := by
    intro j
    have hh := congrFun (congrFun hU j) j
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,pow_two] using hh
  unfold frobSq
  rw [Finset.sum_comm]
  simp only [hc,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
lemma basis_residual_orthogonal {n d k m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Ystar : Matrix (Fin d) (Fin m) ℝ) (hU : IsOrthonormalBasisOf U A)
    (hY : IsLSMinimizer A B Ystar) : Uᵀ*(B-A*Ystar) = 0 := by
  obtain ⟨W,hW⟩ := (basis_factorization A U hU).2
  rw [← hW,Matrix.transpose_mul,Matrix.mul_assoc]
  have hh : Aᵀ*(B-A*Ystar) = 0 := by
    rw [← neg_sub (A*Ystar) B,Matrix.mul_neg,normal_equations A B Ystar hY,neg_zero]
  rw [hh,Matrix.mul_zero]
lemma pair_sq_le {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) :
    pair C D ^ 2 ≤ frobSq C * frobSq D := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.product Finset.univ) (fun p : Fin n × Fin m => C p.1 p.2)
    (fun p : Fin n × Fin m => D p.1 p.2)
  have hs (f : Fin n × Fin m → ℝ) :
      (∑ p ∈ Finset.univ.product Finset.univ, f p) = ∑ i, ∑ j, f (i,j) :=
    Finset.sum_product _ _ _
  rw [hs,hs,hs] at hh
  exact hh
lemma frobSq_columns {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) :
    frobSq C = ∑ j, sqNorm (fun i => C i j) := by
  exact Finset.sum_comm
lemma embedding_frobSq {t n d m : ℕ} (S : Matrix (Fin t) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (η : ℝ) (hemb : IsSubspaceEmbedding S A η)
    (Z : Matrix (Fin d) (Fin m) ℝ) :
    |frobSq (S*(A*Z))-frobSq (A*Z)| ≤ η*frobSq (A*Z) := by
  rw [frobSq_columns,frobSq_columns,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |sqNorm (fun i => (S*(A*Z)) i j)-sqNorm (fun i => (A*Z) i j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, η*sqNorm (fun i => (A*Z) i j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hemb (fun i => Z i j)
    _ = _ := by rw [← Finset.mul_sum]
lemma frobSq_sub_comm {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) :
    frobSq (C-D) = frobSq (D-C) := by
  unfold frobSq
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.sub_apply]
  ring
end SketchedRegressionColumns
#print axioms SketchedRegressionColumns.factor_of_range_le
#print axioms SketchedRegressionColumns.basis_factorization
#print axioms SketchedRegressionColumns.basis_dimension_le_rank
#print axioms SketchedRegressionColumns.orthonormal_frobSq_mul
#print axioms SketchedRegressionColumns.orthonormal_frobSq
#print axioms SketchedRegressionColumns.basis_residual_orthogonal
#print axioms SketchedRegressionColumns.pair_sq_le
#print axioms SketchedRegressionColumns.frobSq_columns
#print axioms SketchedRegressionColumns.embedding_frobSq
#print axioms SketchedRegressionColumns.frobSq_sub_comm

set_option autoImplicit false
open Matrix InputSparsity.Embed InputSparsity.Regress
open SketchedRegressionQuadratic SketchedRegressionColumns
namespace SketchedRegressionError
lemma pair_sub_left {n m : ℕ} (C D R : Matrix (Fin n) (Fin m) ℝ) :
    pair (C-D) R = pair C R - pair D R := by
  simp only [pair,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
lemma sketched_normal_equations {n d m t : ℕ} (S : Matrix (Fin t) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Y : Matrix (Fin d) (Fin m) ℝ) (hY : IsSketchedMinimizer S A B Y) :
    (S*A)ᵀ*((S*A)*Y-S*B) = 0 := by
  apply normal_equations (S*A) (S*B) Y
  intro X
  simpa only [Matrix.mul_assoc,← Matrix.mul_sub] using hY X
lemma sketched_cross_identity {n d m t : ℕ} (S : Matrix (Fin t) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Ystar Ytil : Matrix (Fin d) (Fin m) ℝ) (hY : IsSketchedMinimizer S A B Ytil) :
    frobSq (S*(A*(Ytil-Ystar))) = pair (S*(A*(Ytil-Ystar))) (S*(B-A*Ystar)) := by
  have hm : IsLSMinimizer (S*A) (S*B) Ytil := by
    intro X
    simpa only [Matrix.mul_assoc,← Matrix.mul_sub] using hY X
  have hh := minimizer_pair_zero (S*A) (S*B) Ytil hm (Ytil-Ystar)
  have he : (S*A)*Ytil-S*B = S*(A*(Ytil-Ystar))-S*(B-A*Ystar) := by
    simp only [Matrix.mul_sub,Matrix.mul_assoc]
    module
  rw [he,Matrix.mul_assoc,pair_sub_left,pair_self,pair_comm] at hh
  linarith
lemma amm_residual_bound {n k m t : ℕ} (r : ℕ) (U : Matrix (Fin n) (Fin k) ℝ)
    (S : Matrix (Fin t) (Fin n) ℝ) (R : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ)
    (hr : 1 ≤ r) (hk : k ≤ r) (hU : HasOrthonormalCols U) (hε : 0 < ε)
    (horth : Uᵀ*R = 0) (hamm : AMMEvent S U R (Real.sqrt (ε/r))) :
    frobSq (Uᵀ*Sᵀ*S*R) ≤ ε*frobSq R := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hkr : (k : ℝ) ≤ r := by exact_mod_cast hk
  have her : 0 ≤ ε/(r : ℝ) := div_nonneg hε.le hrp.le
  unfold AMMEvent at hamm
  rw [horth,sub_zero,Real.sq_sqrt her,orthonormal_frobSq U hU] at hamm
  calc
    _ ≤ (ε/(r : ℝ))*(k : ℝ)*frobSq R := hamm
    _ ≤ (ε/(r : ℝ))*(r : ℝ)*frobSq R :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkr her) (frobSq_nonneg R)
    _ = _ := by rw [div_mul_cancel₀ _ hrp.ne']
lemma error_squared_bound {n d m t k : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin d) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (S : Matrix (Fin t) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (ε η : ℝ) (Ystar Ytil : Matrix (Fin d) (Fin m) ℝ)
    (hr : 1 ≤ r) (hrank : A.rank ≤ r) (hε : 0 < ε) (hη : η ≤ 1/2)
    (hU : IsOrthonormalBasisOf U A) (hemb : IsSubspaceEmbedding S A η)
    (hYstar : IsLSMinimizer A B Ystar)
    (hamm : AMMEvent S U (B-A*Ystar) (Real.sqrt (ε/r)))
    (hYtil : IsSketchedMinimizer S A B Ytil) :
    frobSq (A*(Ytil-Ystar)) ≤ 4*ε*frobSq (B-A*Ystar) := by
  obtain ⟨V,hV⟩ := (basis_factorization A U hU).1
  let Z := V*(Ytil-Ystar)
  let Δ := A*(Ytil-Ystar)
  let R := B-A*Ystar
  let M := Uᵀ*Sᵀ*S*R
  have he : Δ = U*Z := by dsimp [Δ,Z]; rw [← hV,Matrix.mul_assoc]
  have hz : frobSq Z = frobSq Δ := by rw [he,orthonormal_frobSq_mul U hU.1]
  have hm : frobSq M ≤ ε*frobSq R := amm_residual_bound r U S R ε hr
    ((basis_dimension_le_rank A U hU).trans hrank) hU.1 hε
    (basis_residual_orthogonal A U B Ystar hU hYstar) hamm
  have hp : pair (S*Δ) (S*R) = pair Z M := by
    rw [he,← Matrix.mul_assoc,pair_mul_left]
    simp only [M,Matrix.transpose_mul,Matrix.mul_assoc]
  have hc : frobSq (S*Δ) = pair Z M :=
    (sketched_cross_identity S A B Ystar Ytil hYtil).trans hp
  have hsq : frobSq (S*Δ)^2 ≤ frobSq Δ*(ε*frobSq R) := by
    rw [hc]
    exact (pair_sq_le Z M).trans (by rw [hz]; exact mul_le_mul_of_nonneg_left hm (frobSq_nonneg Δ))
  have hlow : frobSq Δ/2 ≤ frobSq (S*Δ) := by
    have hh := (abs_le.mp (embedding_frobSq S A η hemb (Ytil-Ystar))).1
    nlinarith [frobSq_nonneg Δ]
  have hlowSq : (frobSq Δ/2)^2 ≤ frobSq (S*Δ)^2 :=
    (sq_le_sq₀ (div_nonneg (frobSq_nonneg Δ) (by norm_num)) (frobSq_nonneg (S*Δ))).mpr hlow
  by_cases hzero : frobSq Δ = 0
  · change frobSq Δ ≤ 4*ε*frobSq R
    rw [hzero]
    exact mul_nonneg (by positivity) (frobSq_nonneg R)
  · have hpos : 0 < frobSq Δ := lt_of_le_of_ne (frobSq_nonneg Δ) (Ne.symm hzero)
    have hprod : frobSq Δ*frobSq Δ ≤ frobSq Δ*(4*ε*frobSq R) := by
      nlinarith only [hlowSq,hsq]
    exact le_of_mul_le_mul_left hprod hpos
end SketchedRegressionError
#print axioms SketchedRegressionError.pair_sub_left
#print axioms SketchedRegressionError.sketched_normal_equations
#print axioms SketchedRegressionError.sketched_cross_identity
#print axioms SketchedRegressionError.amm_residual_bound
#print axioms SketchedRegressionError.error_squared_bound

set_option autoImplicit false
open Matrix InputSparsity.Regress
theorem solution {n d d' t k : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin d) ℝ)
    (B : Matrix (Fin n) (Fin d') ℝ) (S : Matrix (Fin t) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (ε η : ℝ) (Ystar Ytil : Matrix (Fin d) (Fin d') ℝ)
    (hr : 1 ≤ r) (hrank : A.rank ≤ r)
    (hε : 0 < ε) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hU : IsOrthonormalBasisOf U A)
    (hemb : IsSubspaceEmbedding S A η)
    (hYstar : IsLSMinimizer A B Ystar)
    (hamm : AMMEvent S U (B - A * Ystar) (Real.sqrt (ε / r)))
    (hYtil : IsSketchedMinimizer S A B Ytil) :
    InputSparsity.Embed.frobSq (A * Ytil - B) ≤ (1 + 4 * ε) * InputSparsity.Embed.frobSq (A * Ystar - B) := by
  have hb := SketchedRegressionError.error_squared_bound r A B S U ε η Ystar Ytil
    hr hrank hε hη hU hemb hYstar hamm hYtil
  rw [SketchedRegressionColumns.frobSq_sub_comm B (A*Ystar)] at hb
  rw [SketchedRegressionQuadratic.error_decomposition A B Ystar hYstar Ytil]
  nlinarith only [hb]

#print axioms solution
namespace InputSparsity.Regress
open Matrix

example {n d d' t k : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin d) ℝ)
    (B : Matrix (Fin n) (Fin d') ℝ) (S : Matrix (Fin t) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (ε η : ℝ) (Ystar Ytil : Matrix (Fin d) (Fin d') ℝ)
    (hr : 1 ≤ r) (hrank : A.rank ≤ r)
    (hε : 0 < ε) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hU : IsOrthonormalBasisOf U A)
    (hemb : IsSubspaceEmbedding S A η)
    (hYstar : IsLSMinimizer A B Ystar)
    (hamm : AMMEvent S U (B - A * Ystar) (Real.sqrt (ε / r)))
    (hYtil : IsSketchedMinimizer S A B Ytil) :
    InputSparsity.Embed.frobSq (A * Ytil - B) ≤ (1 + 4 * ε) * InputSparsity.Embed.frobSq (A * Ystar - B) := by
  exact solution r A B S U ε η Ystar Ytil hr hrank hε hη₀ hη hU hemb hYstar hamm hYtil

end InputSparsity.Regress

#print axioms solution
