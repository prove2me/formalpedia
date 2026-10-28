-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.rational_algorithm_success
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:39:33.551803+00:00
-- url     : https://prove2.me/submissions/6d63ddae-8b1f-456c-95b5-f1da3a31b416

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_OAIQ2Mt000
import Theorems.Thm_OAI_CommonBasesFPRAS_actual_history_success

section
-- module Solutions.OAIQ2_Mat.MatroidCounting_CommonBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem onePositive_of_nonpositive_kernel (B : LinearMap.BilinForm ℝ V)
    (hsymm : B.IsSymm) (L : V →ₗ[ℝ] ℝ)
    (hker : ∀ v, L v = 0 → B v v ≤ 0) : OnePositive B := by
  intro e he v hve
  by_contra hv
  have hvpos : 0 < B v v := lt_of_not_ge hv
  have hLe : L e ≠ 0 := by
    intro h
    exact (not_le_of_gt he) (hker e h)
  have hev : B e v = 0 := by rw [hsymm.eq e v, hve]
  have hz : L ((L e) • v - (L v) • e) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have hq := hker ((L e) • v - (L v) • e) hz
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hve, hev, mul_zero, sub_zero] at hq
  have hLe2 : 0 < (L e)^2 := sq_pos_of_ne_zero hLe
  have hn : 0 ≤ (L v)^2 * B e e := mul_nonneg (sq_nonneg _) (le_of_lt he)
  have hp : 0 < (L e)^2 * B v v := mul_pos hLe2 hvpos
  nlinarith

section Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem spectral_kernel_nonpositive (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (w : E)
    (hlocal : ∀ v, ⟪v, T v⟫ ≤ ⟪T v, T v⟫)
    (hcon : ∀ v, ⟪v, T v⟫ ≤ ⟪v, v⟫)
    (heq : ∀ v, ⟪v, T v⟫ = ⟪v, v⟫ → ∃ a : ℝ, v = a • w)
    (v : E) (hv : ⟪w,v⟫ = 0) : ⟪v, T v⟫ ≤ 0 := by
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have heigen : ∀ i, T (b i) = ev i • b i := hT.apply_eigenvectorBasis rfl
  have hunit : ∀ i, ⟪b i, b i⟫ = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    norm_num
  have hpos : ∀ i, 0 < ev i → b.repr v i = 0 := by
    intro i hi
    have hl := hlocal (b i)
    have hc := hcon (b i)
    rw [heigen i] at hl hc
    simp only [inner_smul_left, inner_smul_right, hunit, conj_trivial, mul_one] at hl hc
    have he : ev i = 1 := by nlinarith
    have he' : ⟪b i, T (b i)⟫ = ⟪b i, b i⟫ := by rw [heigen i, he, one_smul]
    obtain ⟨a, ha⟩ := heq (b i) he'
    rw [b.repr_apply_apply, ha, inner_smul_left, hv]
    simp
  rw [← b.repr.inner_map_map v (T v)]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_nonpos
  intro i _
  have ht : b.repr (T v) i = ev i * b.repr v i :=
    hT.eigenvectorBasis_apply_self_apply rfl v i
  rw [ht]
  by_cases h : 0 < ev i
  · simp [hpos i h]
  · have hn : ev i ≤ 0 := le_of_not_gt h
    nlinarith [sq_nonneg (b.repr v i)]

end Spectral
section PositiveMatrix
variable {ι : Type*} [Fintype ι] [sectionInstance7 : DecidableEq ι]

theorem matrix_bilin_symm (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = A j i) :
    A.toBilin'.IsSymm := by
  constructor
  intro x y
  simp only [Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i]
  ring

omit sectionInstance7 in
lemma dirichlet_identity [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = A j i)
    (r : ι → ℝ) :
    (∑ i, ∑ j, A i j * (r i-r j)^2) =
      2*(∑ i, (∑ j, A i j)*(r i)^2) - 2*(∑ i, ∑ j, r i*A i j*r j) := by
  have hfirst : (∑ i, ∑ j, A i j*(r i)^2) = ∑ i, (∑ j, A i j)*(r i)^2 := by
    simp only [Finset.sum_mul]
  have hsecond : (∑ i, ∑ j, A i j*(r j)^2) = ∑ i, (∑ j, A i j)*(r i)^2 := by
    rw [Finset.sum_comm]
    simp_rw [hA]
    exact hfirst
  calc
    _ = ∑ i, ∑ j, (A i j*(r i)^2 + A i j*(r j)^2 - 2*(r i*A i j*r j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hfirst, hsecond]
      ring

lemma eigen_dirichlet (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = A j i)
    (w v : ι → ℝ) (hw : ∀ i, 0 < w i) (he : A *ᵥ w = w) :
    (∑ i, ∑ j, A i j*w i*w j*(v i/w i-v j/w j)^2) =
      2 * ((∑ i, (v i)^2) - A.toBilin' v v) := by
  have hs : ∀ i j, A i j*w i*w j = A j i*w j*w i := by
    intro i j; rw [hA i j]; ring
  rw [dirichlet_identity (fun i j => A i j*w i*w j) hs (fun i => v i/w i)]
  have hrows : ∀ i, (∑ j, A i j*w i*w j)*(v i/w i)^2 = (v i)^2 := by
    intro i
    have he' : (∑ j, A i j*w j) = w i := congr_fun he i
    have hsum : (∑ j, A i j*w i*w j) = w i*(∑ j, A i j*w j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum, he']
    field_simp [ne_of_gt (hw i)]
  have hquad : (∑ i, ∑ j, (v i/w i)*(A i j*w i*w j)*(v j/w j)) = A.toBilin' v v := by
    rw [Matrix.toBilin'_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp [ne_of_gt (hw i), ne_of_gt (hw j)]
  simp_rw [hrows]
  rw [hquad]
  ring

lemma positive_eigen_contraction (A : Matrix ι ι ℝ)
    (hA : ∀ i j, A i j = A j i) (hpos : ∀ i j, 0 ≤ A i j)
    (w v : ι → ℝ) (hw : ∀ i, 0 < w i) (he : A *ᵥ w = w) :
    A.toBilin' v v ≤ ∑ i, (v i)^2 := by
  have hd := eigen_dirichlet A hA w v hw he
  have hn : 0 ≤ ∑ i, ∑ j, A i j*w i*w j*(v i/w i-v j/w j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (hpos i j) (hw i).le) (hw j).le) (sq_nonneg _)
  linarith

lemma positive_eigen_equality [Nonempty ι] (A : Matrix ι ι ℝ)
    (hA : ∀ i j, A i j = A j i) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hpos : ∀ i j, i ≠ j → 0 < A i j)
    (w v : ι → ℝ) (hw : ∀ i, 0 < w i) (he : A *ᵥ w = w)
    (heq : A.toBilin' v v = ∑ i, (v i)^2) : ∃ a : ℝ, v = a • w := by
  classical
  let k : ι := Classical.choice ‹Nonempty ι›
  have hd := eigen_dirichlet A hA w v hw he
  rw [heq, sub_self, mul_zero] at hd
  have hn : ∀ i j, 0 ≤ A i j*w i*w j*(v i/w i-v j/w j)^2 := by
    intro i j
    exact mul_nonneg (mul_nonneg (mul_nonneg (hnonneg i j) (hw i).le) (hw j).le) (sq_nonneg _)
  have h0 : ∀ i j, A i j*w i*w j*(v i/w i-v j/w j)^2 = 0 := by
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => Finset.sum_nonneg fun j _ => hn i j)).mp hd
    intro i j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp
      (hrow i (Finset.mem_univ i)) j (Finset.mem_univ j)
  refine ⟨v k/w k, ?_⟩
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hik : i = k
  · subst i
    field_simp [ne_of_gt (hw k)]
  · have hm : A i k*w i*w k ≠ 0 := ne_of_gt (mul_pos (mul_pos (hpos i k hik) (hw i)) (hw k))
    have hz : (v i/w i-v k/w k)^2 = 0 := (mul_eq_zero.mp (h0 i k)).resolve_left hm
    have hh : v i/w i = v k/w k := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    exact (div_eq_iff (ne_of_gt (hw i))).mp hh

lemma euclidean_inner_matrix (A : Matrix ι ι ℝ) (v w : EuclideanSpace ℝ ι) :
    ⟪v, A.toEuclideanLin w⟫ = A.toBilin' (WithLp.ofLp v) (WithLp.ofLp w) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.toBilin'_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit sectionInstance7 in
lemma euclidean_normsq [DecidableEq ι] (v : EuclideanSpace ℝ ι) :
    ⟪v,v⟫ = ∑ i, (WithLp.ofLp v i)^2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, pow_two]

theorem matrix_signature_of_squared [Nonempty ι] (A : Matrix ι ι ℝ)
    (hA : ∀ i j, A i j = A j i) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hpos : ∀ i j, i ≠ j → 0 < A i j)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (he : A *ᵥ w = w)
    (hlocal : ∀ v, A.toBilin' v v ≤ ∑ i, ((A *ᵥ v) i)^2) :
    OnePositive A.toBilin' := by
  have hsym : A.toEuclideanLin.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ext i j
    simpa using hA j i
  refine onePositive_of_nonpositive_kernel _ (matrix_bilin_symm A hA)
    (weightedSumLinear w) ?_
  intro v hv
  change (∑ i, w i * v i) = 0 at hv
  have hn := spectral_kernel_nonpositive A.toEuclideanLin hsym (WithLp.toLp 2 w)
    (fun v => ?_) (fun v => ?_) (fun v hv => ?_) (WithLp.toLp 2 v) ?_
  · simpa only [euclidean_inner_matrix, WithLp.ofLp_toLp] using hn
  · rw [euclidean_inner_matrix, euclidean_normsq]
    exact hlocal _
  · rw [euclidean_inner_matrix, euclidean_normsq]
    exact positive_eigen_contraction A hA hnonneg w _ hw he
  · rw [euclidean_inner_matrix, euclidean_normsq] at hv
    obtain ⟨a, ha⟩ := positive_eigen_equality A hA hnonneg hpos w _ hw he hv
    refine ⟨a, ?_⟩
    exact WithLp.ofLp_injective 2 ha
  · simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using hv

lemma diagonalScale_bilin (A : Matrix ι ι ℝ) (s u v : ι → ℝ) :
    (diagonalScale A s).toBilin' u v =
      A.toBilin' (fun i => s i*u i) (fun i => s i*v i) := by
  simp only [Matrix.toBilin'_apply, diagonalScale]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit sectionInstance7 in
lemma diagonalScale_mulVec [DecidableEq ι] (A : Matrix ι ι ℝ) (s v : ι → ℝ) (i : ι) :
    (diagonalScale A s *ᵥ v) i = s i * (A *ᵥ (fun j => s j*v j)) i := by
  simp only [Matrix.mulVec, dotProduct, diagonalScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma onePositive_unscale (A : Matrix ι ι ℝ) (s : ι → ℝ) (hs : ∀ i, s i ≠ 0)
    (h : OnePositive (diagonalScale A s).toBilin') : OnePositive A.toBilin' := by
  have hf : ∀ v : ι → ℝ, (fun i => s i * (v i / s i)) = v := by
    intro v; ext i; field_simp [hs i]
  intro e he v hv
  have hep : 0 < (diagonalScale A s).toBilin' (fun i => e i/s i) (fun i => e i/s i) := by
    simpa [diagonalScale_bilin, hf] using he
  have hvp : (diagonalScale A s).toBilin' (fun i => v i/s i) (fun i => e i/s i) = 0 := by
    simpa [diagonalScale_bilin, hf] using hv
  simpa [diagonalScale_bilin, hf] using h _ hep _ hvp

theorem signature_of_local_bound [Nonempty ι] (A : Matrix ι ι ℝ)
    (hA : ∀ i j, A i j = A j i) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hpos : ∀ i j, i ≠ j → 0 < A i j)
    (x s : ι → ℝ) (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i)
    (hsx : ∀ i, (s i)^2*(A*ᵥx) i = x i)
    (hlocal : ∀ v, A.toBilin' v v ≤ ∑ i, (s i)^2*((A *ᵥ v) i)^2) :
    OnePositive A.toBilin' := by
  let B := diagonalScale A s
  have hB : ∀ i j, B i j = B j i := by
    intro i j; dsimp [B, diagonalScale]; rw [hA i j]; ring
  have hBn : ∀ i j, 0 ≤ B i j := by
    intro i j; exact mul_nonneg (mul_nonneg (hs i).le (hnonneg i j)) (hs j).le
  have hBp : ∀ i j, i ≠ j → 0 < B i j := by
    intro i j hij; exact mul_pos (mul_pos (hs i) (hpos i j hij)) (hs j)
  let w : ι → ℝ := fun i => x i/s i
  have hw : ∀ i, 0 < w i := fun i => div_pos (hx i) (hs i)
  have hsw : (fun j => s j * w j) = x := by
    ext j; dsimp [w]; field_simp [ne_of_gt (hs j)]
  have he : B *ᵥ w = w := by
    ext i
    rw [diagonalScale_mulVec, hsw]
    dsimp [w]
    apply (eq_div_iff (ne_of_gt (hs i))).mpr
    nlinarith [hsx i]
  have hl : ∀ v, B.toBilin' v v ≤ ∑ i, ((B *ᵥ v) i)^2 := by
    intro v
    change (diagonalScale A s).toBilin' v v ≤ _
    dsimp only [B]
    rw [diagonalScale_bilin]
    simp_rw [diagonalScale_mulVec, mul_pow]
    exact hlocal _
  exact onePositive_unscale A s (fun i => ne_of_gt (hs i))
    (matrix_signature_of_squared B hB hBn hBp w hw he hl)

lemma onePositive_quadratic_bound {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : OnePositive B) (hS : B.IsSymm)
    (e v : V) (he : 0 < B e e) : B v v ≤ (B v e)^2 / B e e := by
  have hz : B ((B e e) • v - (B v e) • e) e = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hn := hB e he ((B e e) • v - (B v e) • e) hz
  have hev : B e v = B v e := hS.eq e v
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hev] at hn
  apply (le_div_iff₀ he).mpr
  have hf : B e e * (B v v * B e e - (B v e)^2) ≤ 0 := by nlinarith [hn]
  have hle : B v v * B e e - (B v e)^2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hf he
  linarith

omit sectionInstance7 in
lemma cubicContraction_symm [DecidableEq ι] (C : ι → Matrix ι ι ℝ)
    (hC : ∀ i j k, C i j k = C i k j) (x : ι → ℝ) :
    ∀ j k, cubicContraction C x j k = cubicContraction C x k j := by
  intro j k
  simp only [cubicContraction, hC]

lemma cubicContraction_bilin (C : ι → Matrix ι ι ℝ) (x v : ι → ℝ) :
    (cubicContraction C x).toBilin' v v = ∑ i, x i*(C i).toBilin' v v := by
  calc
    _ = ∑ j, ∑ k, ∑ i, v j * x i * C i j k * v k := by
      simp only [Matrix.toBilin'_apply, cubicContraction, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ j, ∑ i, ∑ k, v j * x i * C i j k * v k :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, v j * x i * C i j k * v k := Finset.sum_comm
    _ = _ := by
      simp only [Matrix.toBilin'_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma cubicContraction_row (C : ι → Matrix ι ι ℝ)
    (hC : ∀ i j k, C i j k = C j i k) (x v : ι → ℝ) (i : ι) :
    (C i).toBilin' x v = (cubicContraction C x *ᵥ v) i := by
  simp only [Matrix.toBilin'_apply, Matrix.mulVec, dotProduct, cubicContraction,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hC i k j]

theorem cubic_local_estimate (C : ι → Matrix ι ι ℝ)
    (hCs : ∀ i j k, C i j k = C i k j)
    (hCt : ∀ i j k, C i j k = C j i k)
    (hC : ∀ i, OnePositive (C i).toBilin')
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hCx : ∀ i, 0 < (C i).toBilin' x x) (v : ι → ℝ) :
    (cubicContraction C x).toBilin' v v ≤
      ∑ i, x i * ((cubicContraction C x *ᵥv) i)^2 / (cubicContraction C x *ᵥx) i := by
  rw [cubicContraction_bilin]
  apply Finset.sum_le_sum
  intro i _
  have hS := matrix_bilin_symm (C i) (hCs i)
  have hl := mul_le_mul_of_nonneg_left
    (onePositive_quadratic_bound (C i).toBilin' (hC i) hS x v (hCx i)) (hx i)
  rw [hS.eq v x, cubicContraction_row C hCt x v i,
    cubicContraction_row C hCt x x i, ← mul_div_assoc] at hl
  exact hl

theorem cubic_signature [Nonempty ι] (C : ι → Matrix ι ι ℝ)
    (hCs : ∀ i j k, C i j k = C i k j)
    (hCt : ∀ i j k, C i j k = C j i k)
    (hC : ∀ i, OnePositive (C i).toBilin')
    (x : ι → ℝ) (hx : ∀ i, 0 < x i)
    (hCx : ∀ i, 0 < (C i).toBilin' x x)
    (hCn : ∀ j k, 0 ≤ cubicContraction C x j k)
    (hCp : ∀ j k, j ≠ k → 0 < cubicContraction C x j k) :
    OnePositive (cubicContraction C x).toBilin' := by
  let A := cubicContraction C x
  have hy : ∀ i, 0 < (A*ᵥx) i := by
    intro i
    rw [← cubicContraction_row C hCt x x i]
    exact hCx i
  let s : ι → ℝ := fun i => Real.sqrt (x i/(A*ᵥx) i)
  have hs : ∀ i, 0 < s i := fun i => Real.sqrt_pos.2 (div_pos (hx i) (hy i))
  have hs2 : ∀ i, (s i)^2 = x i/(A*ᵥx) i := fun i =>
    Real.sq_sqrt (le_of_lt (div_pos (hx i) (hy i)))
  apply signature_of_local_bound A (cubicContraction_symm C hCs x) hCn hCp x s hx hs
  · intro i
    rw [hs2]
    field_simp [ne_of_gt (hy i)]
  intro v
  have hl := cubic_local_estimate C hCs hCt hC x (fun i => (hx i).le) hCx v
  refine hl.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [hs2]
  ring

end PositiveMatrix

section RawSignature
open scoped BigOperators Classical
variable {ι : Type*} [sectionInstance8 : Fintype ι] [sectionInstance9 : DecidableEq ι]

omit sectionInstance8 sectionInstance9 in
lemma eRk_insert_of_mem_closure' [Fintype ι] [DecidableEq ι] (M : Matroid ι) (i : ι) (X : Set ι)
    (hi : i ∈ M.closure X) : M.eRk (insert i X) = M.eRk X := by
  rw [← M.eRk_insert_closure_eq, Set.insert_eq_of_mem hi, M.eRk_closure_eq]

lemma pair_rank_of_loop (M : Matroid ι) (i j : ι) (hi : M.IsLoop i) :
    M.eRk {i,j} = M.eRk {j} :=
  eRk_insert_of_mem_closure' M i {j} (hi.mem_closure _)

lemma pair_rank_parallel (M : Matroid ι) (i j : ι) (hi : M.IsNonloop i) (hj : M.IsNonloop j)
    (hc : M.closure {i} = M.closure {j}) : M.eRk {i,j} = 1 := by
  rw [eRk_insert_of_mem_closure' M i {j}, hj.eRk_eq]
  rw [← hc]
  exact M.mem_closure_self i hi.mem_ground

omit sectionInstance8 sectionInstance9 in
lemma pair_rank_nonparallel [Fintype ι] [DecidableEq ι] (M : Matroid ι) (i j : ι) (hi : M.IsNonloop i)
    (hj : M.IsNonloop j) (hc : M.closure {i} ≠ M.closure {j}) :
    M.eRk {i,j} = 2 := by
  have hn : i ∉ M.closure {j} := fun h => hc (hi.closure_eq_of_mem_closure h)
  rw [M.eRk_insert_eq_add_one ⟨hi.mem_ground, hn⟩, hj.eRk_eq]
  norm_num

omit sectionInstance9 in
lemma parallel_gram [DecidableEq ι] (M : Matroid ι) (i j : ι) :
    (∑ C : Set ι, parallelIndicator M C i * parallelIndicator M C j) =
    if M.IsNonloop i ∧ M.IsNonloop j ∧ M.closure {i} = M.closure {j}
      then 1 else 0 := by
  classical
  by_cases hi : M.IsNonloop i <;> by_cases hj : M.IsNonloop j
  · simp [parallelIndicator, hi, hj, Finset.sum_ite_eq', eq_comm]
  · simp [parallelIndicator, hi, hj]
  · simp [parallelIndicator, hi, hj]
  · simp [parallelIndicator, hi, hj]

lemma rawHessian_decomposition (M : Matroid ι) (hE : M.E = Set.univ)
    (q : ℝ) (i j : ι) :
    rawHessian M q i j = rawPositive M q i * rawPositive M q j -
      (if i = j then rawPositive M q i else 0) -
      (q⁻¹^2-q⁻¹) * ∑ C : Set ι, parallelIndicator M C i * parallelIndicator M C j := by
  classical
  have hground : ∀ i, i ∈ M.E := by simp [hE]
  rw [parallel_gram]
  by_cases hij : i = j
  · subst j
    by_cases hi : M.IsNonloop i <;> simp [rawHessian, rawPositive, hi] ; ring
  · have hij' : j ≠ i := Ne.symm hij
    simp only [rawHessian, ite_eq_right hij]
    by_cases hi : M.IsNonloop i <;> by_cases hj : M.IsNonloop j
    · by_cases hc : M.closure {i} = M.closure {j}
      · rw [rankWeight, pair_rank_parallel M i j hi hj hc]
        simp [rawPositive, hi, hj, hc]
        ring
      · rw [rankWeight, pair_rank_nonparallel M i j hi hj hc]
        simp [rawPositive, hi, hj, hc]
        ring
    · have hloop : M.IsLoop j := (M.not_isNonloop_iff (hground j)).mp hj
      rw [rankWeight, Set.pair_comm i j, pair_rank_of_loop M j i hloop, hi.eRk_eq]
      simp [rawPositive, hi, hj]
    · have hloop : M.IsLoop i := (M.not_isNonloop_iff (hground i)).mp hi
      rw [rankWeight, pair_rank_of_loop M i j hloop, hj.eRk_eq]
      simp [rawPositive, hi, hj]
    · have hli : M.IsLoop i := (M.not_isNonloop_iff (hground i)).mp hi
      have hlj : M.IsLoop j := (M.not_isNonloop_iff (hground j)).mp hj
      rw [rankWeight, pair_rank_of_loop M i j hli, hlj.eRk_eq]
      simp [rawPositive, hi, hj]

omit sectionInstance9 in
lemma sum_rankone [DecidableEq ι] (a v : ι → ℝ) :
    (∑ i, ∑ j, v i * (a i * a j) * v j) = (∑ i, a i * v i)^2 := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sum_diagonal (a v : ι → ℝ) :
    (∑ i, ∑ j, v i * (if i = j then a i else 0) * v j) =
      ∑ i, a i * (v i)^2 := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma sum_gram {κ : Type*} [Fintype κ] (p : κ → ι → ℝ) (v : ι → ℝ) :
    (∑ i, ∑ j, v i * (∑ c, p c i * p c j) * v j) =
      ∑ c, (∑ i, p c i * v i)^2 := by
  calc
    _ = ∑ i, ∑ j, ∑ c, v i * (p c i * p c j) * v j := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ c, ∑ j, v i * (p c i * p c j) * v j :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ j, v i * (p c i * p c j) * v j := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => sum_rankone (p c) v

lemma rawHessian_eval (M : Matroid ι) (hE : M.E = Set.univ) (q : ℝ) (v : ι → ℝ) :
    (rawHessian M q).toBilin' v v =
      (∑ i, rawPositive M q i * v i)^2 -
      (∑ i, rawPositive M q i * (v i)^2) -
      (q⁻¹^2-q⁻¹) * ∑ C : Set ι, (∑ i, parallelIndicator M C i * v i)^2 := by
  simp only [Matrix.toBilin'_apply, rawHessian_decomposition M hE]
  generalize hc : q⁻¹^2-q⁻¹ = c
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [sum_rankone, sum_diagonal]
  congr 1
  rw [← sum_gram]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  ring

theorem raw_matroid_signature (M : Matroid ι) (hE : M.E = Set.univ)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) : OnePositive (rawHessian M q).toBilin' := by
  refine onePositive_of_nonpositive_kernel _ ?_ (weightedSumLinear (rawPositive M q)) ?_
  · apply matrix_bilin_symm
    intro i j
    by_cases hij : i = j
    · subst j; rfl
    · simp [rawHessian, hij, Ne.symm hij, Set.pair_comm i j]
  intro v hv
  change (∑ i, rawPositive M q i * v i) = 0 at hv
  rw [rawHessian_eval M hE q v, hv, zero_pow (by decide), zero_sub]
  have hp : ∀ i, 0 ≤ rawPositive M q i := by
    intro i
    simp only [rawPositive]
    split_ifs <;> positivity
  have hd : 0 ≤ ∑ i, rawPositive M q i * (v i)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)
  have hi : 1 ≤ q⁻¹ := (one_le_inv₀ hq).mpr hq1
  have hc : 0 ≤ q⁻¹^2-q⁻¹ := by nlinarith
  have hg : 0 ≤ (q⁻¹^2-q⁻¹) * ∑ C : Set ι, (∑ i, parallelIndicator M C i * v i)^2 :=
    mul_nonneg hc (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  linarith

end RawSignature
section MatroidFaces
open scoped Matroid BigOperators Classical
variable {ι : Type*} [sectionInstance10 : Fintype ι] [sectionInstance11 : DecidableEq ι]

omit sectionInstance10 sectionInstance11 in
lemma contract_eRk_add [Fintype ι] [DecidableEq ι] (M : Matroid ι) (A X : Set ι)
    (hA : A ⊆ M.E) (hX : X ⊆ (M ／ A).E) :
    (M ／ A).eRk X + M.eRk A = M.eRk (X ∪ A) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis A hA
  obtain ⟨J, hJ⟩ := (M ／ A).exists_isBasis X hX
  have hJ' : (M ／ I).IsBasis J X := by
    rw [hI.contract_eq_contract_delete] at hJ
    exact (Matroid.delete_isBasis_iff.mp hJ).1
  have hU := hI.indep.union_isBasis_union_of_contract_isBasis hJ'
  have hd : Disjoint J I := (hI.indep.contract_indep_iff.mp hJ'.indep).1
  calc
    _ = J.encard + I.encard := by rw [hJ.eRk_eq_encard, hI.eRk_eq_encard]
    _ = (J ∪ I).encard := (Set.encard_union_eq hd).symm
    _ = M.eRk (X ∪ I) := hU.encard_eq_eRk
    _ = M.eRk (X ∪ A) := by
      simpa [Set.union_comm] using hI.eRk_eq_eRk_union X

omit sectionInstance10 sectionInstance11 in
lemma faceMatroid_ground [Fintype ι] [DecidableEq ι] (M : Matroid ι) (hE : M.E = Set.univ) (A : Set ι) :
    (faceMatroid M A).E = Set.univ := by
  ext i
  simp [faceMatroid, hE, i.property]

lemma faceMatroid_rank (M : Matroid ι) (hE : M.E = Set.univ)
    (A : Set ι) (i j : {i // i ∉ A}) :
    (faceMatroid M A).eRk {i,j} + M.eRk A = M.eRk (A ∪ {i.val,j.val}) := by
  have hA : A ⊆ M.E := by simp [hE]
  have hX : ({i.val,j.val} : Set ι) ⊆ (M ／ A).E := by
    simp only [Matroid.contract_ground, hE]
    intro k hk
    rcases hk with rfl | rfl
    · exact ⟨Set.mem_univ _, i.property⟩
    · exact ⟨Set.mem_univ _, j.property⟩
  simpa [faceMatroid, Matroid.eRk_comap, Set.image_pair, Set.union_comm] using
    contract_eRk_add M A {i.val,j.val} hA hX

lemma faceHessian_rankWeight (M : Matroid ι) (hE : M.E = Set.univ)
    (q : ℝ) (A : Set ι) :
    faceHessian (rankWeight M q) A = rankWeight M q A • rawHessian (faceMatroid M A) q := by
  ext i j
  by_cases hij : i = j
  · simp [faceHessian, rawHessian, hij]
  simp only [faceHessian, rawHessian, ite_eq_right hij, Matrix.smul_apply, smul_eq_mul,
    rankWeight]
  have hr := faceMatroid_rank M hE A i j
  rw [← hr, ENat.toNat_add (by simp) (by simp), pow_add, mul_comm]

lemma onePositive_pos_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : OnePositive B) (c : ℝ) (hc : 0 < c) :
    OnePositive (c • B) := by
  intro e he v hv
  simp only [LinearMap.smul_apply, smul_eq_mul] at he hv ⊢
  have he' : 0 < B e e := pos_of_mul_pos_right he hc.le
  have hv' : B v e = 0 := (mul_eq_zero.mp hv).resolve_left (ne_of_gt hc)
  exact mul_nonpos_of_nonneg_of_nonpos hc.le (hB e he' v hv')

theorem rankWeight_face_signature (M : Matroid ι) (hE : M.E = Set.univ)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (A : Set ι) :
    OnePositive (faceHessian (rankWeight M q) A).toBilin' := by
  rw [faceHessian_rankWeight M hE q A, map_smul]
  exact onePositive_pos_smul _
    (raw_matroid_signature (faceMatroid M A) (faceMatroid_ground M hE A) q hq hq1)
    _ (by dsimp [rankWeight]; positivity)

end MatroidFaces

section DerivativeClosure
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance12 : Fintype ι] [sectionInstance13 : DecidableEq ι]

omit sectionInstance13 in
lemma ncard_insert_eq [DecidableEq ι] (A : Set ι) (i : ι) (hi : i ∉ A) :
    (insert i A).ncard = A.ncard + 1 := Set.ncard_insert_of_notMem hi

omit sectionInstance13 in
lemma exists_outside_of_ncard_lt [DecidableEq ι] (A : Set ι) (h : A.ncard < Fintype.card ι) :
    ∃ i, i ∉ A := by
  by_contra hn
  have hA : A = Set.univ := by ext i; simp only [Set.mem_univ, iff_true]; exact of_not_not (not_exists.mp hn i)
  simp [hA] at h

omit sectionInstance13 in
lemma FullPositive.nonneg [DecidableEq ι] {f : Set ι → ℝ} {k : ℕ} (h : FullPositive f k)
    (A : Set ι) : 0 ≤ f A := by
  by_cases ha : A.ncard + k ≤ Fintype.card ι
  · exact (h.1 A ha).le
  · rw [h.2 A (lt_of_not_ge ha)]

lemma FullPositive.deriv {f : Set ι → ℝ} {k : ℕ} (h : FullPositive f k)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) : FullPositive (coeffDeriv a f) (k+1) := by
  constructor
  · intro A hA
    obtain ⟨i, hi⟩ := exists_outside_of_ncard_lt A (by omega)
    apply Finset.sum_pos'
    · intro j _
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (ha j).le (h.nonneg _)
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [ite_eq_right hi]
      apply mul_pos (ha i)
      apply h.1
      rw [ncard_insert_eq A i hi]
      omega
  · intro A hA
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · rfl
    · rw [h.2 (insert i A) (by rw [ncard_insert_eq A i hi]; omega), mul_zero]

lemma padMatrix_bilin (p : ι → Prop) [DecidablePred p]
    (B : Matrix {i // p i} {i // p i} ℝ) (v w : ι → ℝ) :
    (padMatrix p B).toBilin' v w = B.toBilin' (fun i => v i.val) (fun i => w i.val) := by
  simp only [Matrix.toBilin'_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype p
    (fun i => ∑ j, v i * padMatrix p B i j * w j)]
  have hn : (∑ i : {i // ¬p i}, ∑ j, v i.val * padMatrix p B i.val j * w j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    simp [padMatrix, i.property]
  rw [hn, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fintype.sum_subtype_add_sum_subtype p
    (fun j => v i.val * padMatrix p B i.val j * w j)]
  have hn' : (∑ j : {j // ¬p j}, v i.val * padMatrix p B i.val j.val * w j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [padMatrix, i.property, j.property]
  rw [hn', add_zero]
  apply Finset.sum_congr rfl
  intro j _
  simp [padMatrix, i.property, j.property]

lemma onePositive_padMatrix (p : ι → Prop) [DecidablePred p]
    (B : Matrix {i // p i} {i // p i} ℝ) (hB : OnePositive B.toBilin') :
    OnePositive (padMatrix p B).toBilin' := by
  intro e he v hv
  rw [padMatrix_bilin] at he hv ⊢
  exact hB _ he _ hv

lemma matrix_reindex_bilin {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (B : Matrix κ κ ℝ) (v w : ι → ℝ) :
    (B.submatrix e e).toBilin' v w =
      B.toBilin' (fun j => v (e.symm j)) (fun j => w (e.symm j)) := by
  simp only [Matrix.toBilin'_apply, Matrix.submatrix_apply]
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  simp

lemma onePositive_reindex {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (B : Matrix κ κ ℝ) (hB : OnePositive B.toBilin') :
    OnePositive (B.submatrix e e).toBilin' := by
  intro x hx v hv
  rw [matrix_reindex_bilin] at hx hv ⊢
  exact hB _ hx _ hv

omit sectionInstance12 in
lemma faceCubic_symm [Fintype ι] (f : Set ι → ℝ) (A : Set ι) (i j k : {i // i ∉ A}) :
    faceCubic f A i j k = faceCubic f A i k j := by
  unfold faceCubic
  have hc : (i = j ∨ i = k ∨ j = k) ↔ (i = k ∨ i = j ∨ k = j) := by aesop
  simp only [← hc]
  have hs : ({j.val,k.val} : Set ι) = {k.val,j.val} := Set.pair_comm _ _
  rw [hs]

omit sectionInstance12 in
lemma faceCubic_transpose [Fintype ι] (f : Set ι → ℝ) (A : Set ι) (i j k : {i // i ∉ A}) :
    faceCubic f A i j k = faceCubic f A j i k := by
  unfold faceCubic
  have hc : (i = j ∨ i = k ∨ j = k) ↔ (j = i ∨ j = k ∨ i = k) := by aesop
  simp only [← hc]
  have hs : insert i.val (A ∪ {j.val,k.val}) = insert j.val (A ∪ {i.val,k.val}) := by
    ext x; simp; tauto
  rw [hs]

omit sectionInstance12 in
lemma faceCubic_pad [Fintype ι] (f : Set ι → ℝ) (A : Set ι) (i : {i // i ∉ A}) :
    faceCubic f A i = padMatrix (fun j => j ≠ i)
      ((faceHessian f (insert i.val A)).submatrix (faceEraseEquiv A i) (faceEraseEquiv A i)) := by
  ext j k
  simp only [faceCubic, padMatrix]
  by_cases hji : j = i
  · subst j; simp
  by_cases hki : k = i
  · subst k; simp
  rw [dite_eq_left hji, dite_eq_left hki]
  simp only [Matrix.submatrix_apply, faceHessian]
  by_cases hjk : j = k
  · subst k; simp
  have hi : i ≠ j := Ne.symm hji
  have hk : i ≠ k := Ne.symm hki
  have hne : faceEraseEquiv A i ⟨j,hji⟩ ≠ faceEraseEquiv A i ⟨k,hki⟩ := by
    intro h
    exact hjk (congrArg Subtype.val ((faceEraseEquiv A i).injective h))
  simp only [hi, hk, hjk, false_or, ite_false, hne]
  congr 1
  ext x
  simp [faceEraseEquiv]
  tauto

lemma faceCubic_onePositive (f : Set ι → ℝ)
    (hf : ∀ A, OnePositive (faceHessian f A).toBilin')
    (A : Set ι) (i : {i // i ∉ A}) : OnePositive (faceCubic f A i).toBilin' := by
  classical
  rw [faceCubic_pad]
  apply onePositive_padMatrix
  apply onePositive_reindex
  convert hf (insert i.val A) using 1
  congr 2 <;> exact Subsingleton.elim _ _

omit sectionInstance13 in
lemma ncard_union_pair [DecidableEq ι] (A : Set ι) (i j : {i // i ∉ A}) (hij : i ≠ j) :
    (A ∪ {i.val,j.val}).ncard = A.ncard + 2 := by
  have he : A ∪ {i.val,j.val} = insert i.val (insert j.val A) := by ext x; simp
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  rw [he, Set.ncard_insert_of_notMem (by simpa using And.intro hne i.property),
    Set.ncard_insert_of_notMem j.property]

lemma ncard_insert_union_pair (A : Set ι) (i j k : {i // i ∉ A})
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (insert i.val (A ∪ {j.val,k.val})).ncard = A.ncard + 3 := by
  have hi : i.val ∉ A ∪ {j.val,k.val} := by
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨i.property, fun h => hij (Subtype.ext h), fun h => hik (Subtype.ext h)⟩
  rw [Set.ncard_insert_of_notMem hi, ncard_union_pair A j k hjk]

lemma faceCubic_contraction (f : Set ι → ℝ) (a : ι → ℝ) (A : Set ι)
    (j k : {i // i ∉ A}) :
    faceHessian (coeffDeriv a f) A j k =
      ∑ i : {i // i ∉ A}, a i.val * faceCubic f A i j k := by
  classical
  by_cases hjk : j = k
  · subst k; simp [faceHessian, faceCubic]
  change (if j = k then 0 else coeffDeriv a f (A ∪ {j.val,k.val})) = _
  rw [ite_eq_right hjk]
  unfold coeffDeriv
  let g : ι → ℝ := fun i => @ite ℝ (i ∈ A ∪ {j.val,k.val})
    (Classical.propDecidable _) 0 (a i * f (insert i (A ∪ {j.val,k.val})))
  change (∑ i, g i) = _
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∉ A) g]
  have hz : (∑ i : {i // ¬i ∉ A}, g i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    dsimp [g]
    rw [ite_eq_left (Set.mem_union_left _ (not_not.mp i.property))]
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [g]
  by_cases hij : i = j
  · subst j; simp [faceCubic]
  by_cases hik : i = k
  · subst k; simp [faceCubic]
  have hni : i.val ∉ A ∪ {j.val,k.val} := by
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨i.property, fun h => hij (Subtype.ext h), fun h => hik (Subtype.ext h)⟩
  simp only [ite_eq_right hni, faceCubic, hij, hik, hjk, false_or, ite_false]

omit sectionInstance12 in
lemma faceCubic_nonneg [Fintype ι] (f : Set ι → ℝ) (hf : ∀ A, 0 ≤ f A) (A : Set ι)
    (i j k : {i // i ∉ A}) : 0 ≤ faceCubic f A i j k := by
  unfold faceCubic
  split_ifs
  · exact le_rfl
  · exact hf _

lemma FullPositive.faceCubic_pos {f : Set ι → ℝ} {m : ℕ} (hf : FullPositive f m)
    (A : Set ι) (hA : A.ncard + m + 3 ≤ Fintype.card ι)
    (i j k : {i // i ∉ A}) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    0 < faceCubic f A i j k := by
  simp only [faceCubic, hij, hik, hjk, false_or, ite_false]
  apply hf.1
  rw [ncard_insert_union_pair A i j k hij hik hjk]
  omega

lemma FullPositive.faceCubic_zero {f : Set ι → ℝ} {m : ℕ} (hf : FullPositive f m)
    (A : Set ι) (hA : Fintype.card ι < A.ncard + m + 3)
    (i j k : {i // i ∉ A}) : faceCubic f A i j k = 0 := by
  unfold faceCubic
  split_ifs with hc
  · rfl
  · obtain ⟨hij,hik,hjk⟩ : i ≠ j ∧ i ≠ k ∧ j ≠ k := by tauto
    apply hf.2
    rw [ncard_insert_union_pair A i j k hij hik hjk]
    omega

theorem derivative_face_signature {f : Set ι → ℝ} {m : ℕ}
    (hf : FullPositive f m) (hfs : ∀ A, OnePositive (faceHessian f A).toBilin')
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (A : Set ι) :
    OnePositive (faceHessian (coeffDeriv a f) A).toBilin' := by
  classical
  have heq : faceHessian (coeffDeriv a f) A =
      cubicContraction (faceCubic f A) (fun i => a i.val) := by
    ext j k
    exact faceCubic_contraction f a A j k
  rw [heq]
  by_cases hA : A.ncard + m + 3 ≤ Fintype.card ι
  · obtain ⟨i, hi⟩ := exists_outside_of_ncard_lt A (by omega)
    let : Nonempty {i // i ∉ A} := ⟨⟨i,hi⟩⟩
    have hn : ∀ j k, 0 ≤ cubicContraction (faceCubic f A) (fun i => a i.val) j k := by
      intro j k
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (ha _).le (faceCubic_nonneg f hf.nonneg A i j k)
    have hp : ∀ j k, j ≠ k →
        0 < cubicContraction (faceCubic f A) (fun i => a i.val) j k := by
      intro j k hjk
      obtain ⟨l,hl⟩ := exists_outside_of_ncard_lt (A ∪ {j.val,k.val})
        (by rw [ncard_union_pair A j k hjk]; omega)
      have hlA : l ∉ A := fun h => hl (Or.inl h)
      let l' : {i // i ∉ A} := ⟨l,hlA⟩
      have hlj : l' ≠ j := by intro h; exact hl (Or.inr (Or.inl (congrArg Subtype.val h)))
      have hlk : l' ≠ k := by intro h; exact hl (Or.inr (Or.inr (congrArg Subtype.val h)))
      apply Finset.sum_pos'
      · intro i _
        exact mul_nonneg (ha _).le (faceCubic_nonneg f hf.nonneg A i j k)
      · exact ⟨l', Finset.mem_univ _, mul_pos (ha l) (hf.faceCubic_pos A hA l' j k hlj hlk hjk)⟩
    apply cubic_signature (faceCubic f A) (faceCubic_symm f A) (faceCubic_transpose f A)
      (faceCubic_onePositive f hfs A) (fun i => a i.val) (fun i => ha i.val) _ hn hp
    intro j
    rw [cubicContraction_row _ (faceCubic_transpose f A)]
    change 0 < ∑ k, cubicContraction (faceCubic f A) (fun i => a i.val) j k * a k.val
    obtain ⟨k,hk⟩ := exists_outside_of_ncard_lt (insert j.val A)
      (by rw [ncard_insert_eq A j.val j.property]; omega)
    have hkA : k ∉ A := fun h => hk (Or.inr h)
    let k' : {i // i ∉ A} := ⟨k,hkA⟩
    have hjk : j ≠ k' := by intro h; exact hk (Or.inl (congrArg Subtype.val h).symm)
    apply Finset.sum_pos'
    · intro k _; exact mul_nonneg (hn j k) (ha _).le
    · exact ⟨k', Finset.mem_univ _, mul_pos (hp j k' hjk) (ha k)⟩
  · have hz : cubicContraction (faceCubic f A) (fun i => a i.val) = 0 := by
      ext j k
      simp [cubicContraction, hf.faceCubic_zero A (lt_of_not_ge hA)]
    rw [hz]
    intro e he
    simp

omit sectionInstance13 in
lemma rankWeight_fullPositive [DecidableEq ι] (M : Matroid ι) (q : ℝ) (hq : 0 < q) :
    FullPositive (rankWeight M q) 0 := by
  constructor
  · intro A _; unfold rankWeight; positivity
  · intro A hA
    have hbound : A.ncard ≤ Fintype.card ι := by simpa using Set.ncard_le_card A
    omega

theorem rankWeight_positive_directions (M : Matroid ι) (hE : M.E = Set.univ)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (ds : List (ι → ℝ))
    (hds : ∀ a ∈ ds, ∀ i, 0 < a i) :
    FullPositive (coeffDerivs ds (rankWeight M q)) ds.length ∧
      ∀ A, OnePositive (faceHessian (coeffDerivs ds (rankWeight M q)) A).toBilin' := by
  induction ds with
  | nil =>
    exact ⟨rankWeight_fullPositive M q hq, rankWeight_face_signature M hE q hq hq1⟩
  | cons a ds ih =>
    have ha := hds a (List.mem_cons_self ..)
    obtain ⟨hpos,hsig⟩ := ih (fun b hb => hds b (List.mem_cons_of_mem _ hb))
    exact ⟨hpos.deriv a ha, derivative_face_signature hpos hsig a ha⟩

lemma matrix_bilin_tendsto {κ : Type*} {l : Filter κ}
    (F : κ → Matrix ι ι ℝ) (B : Matrix ι ι ℝ)
    (hF : ∀ i j, Filter.Tendsto (fun t => F t i j) l (nhds (B i j)))
    (v w : ι → ℝ) :
    Filter.Tendsto (fun t => (F t).toBilin' v w) l (nhds (B.toBilin' v w)) := by
  simp only [Matrix.toBilin'_apply]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_const_nhds.mul (hF i j)).mul tendsto_const_nhds)

lemma onePositive_of_tendsto {κ : Type*} {l : Filter κ} [l.NeBot]
    (F : κ → Matrix ι ι ℝ) (B : Matrix ι ι ℝ)
    (hF : ∀ i j, Filter.Tendsto (fun t => F t i j) l (nhds (B i j)))
    (hS : ∀ t i j, F t i j = F t j i)
    (hP : ∀ᶠ t in l, OnePositive (F t).toBilin') : OnePositive B.toBilin' := by
  intro e he v hv
  have hee := matrix_bilin_tendsto F B hF e e
  have hvv := matrix_bilin_tendsto F B hF v v
  have hve := matrix_bilin_tendsto F B hF v e
  have hp : ∀ᶠ t in l, (F t).toBilin' v v * (F t).toBilin' e e ≤
      ((F t).toBilin' v e)^2 := by
    filter_upwards [hP, hee.eventually (eventually_gt_nhds he)] with t ht hte
    exact (le_div_iff₀ hte).mp
      (onePositive_quadratic_bound _ ht (matrix_bilin_symm _ (hS t)) e v hte)
  have hh := le_of_tendsto_of_tendsto (hvv.mul hee) (hve.pow 2) hp
  rw [hv, zero_pow (by decide : 2 ≠ 0)] at hh
  exact nonpos_of_mul_nonpos_right (by simpa [mul_comm] using hh) he

omit sectionInstance12 in
lemma faceHessian_symm [Fintype ι] (f : Set ι → ℝ) (A : Set ι) :
    ∀ i j, faceHessian f A i j = faceHessian f A j i := by
  intro i j
  simp only [faceHessian]
  by_cases hij : i = j
  · subst j; rfl
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), Set.pair_comm]

omit sectionInstance13 in
lemma continuous_coeffDerivs_perturb [DecidableEq ι] (ds : List (ι → ℝ)) (f : Set ι → ℝ) (A : Set ι) :
    Continuous (fun t : ℝ => coeffDerivs (ds.map (fun a i => a i + t)) f A) := by
  induction ds generalizing A with
  | nil => exact continuous_const
  | cons a ds ih =>
    simp only [List.map_cons, coeffDerivs, coeffDeriv]
    apply continuous_finsetSum
    intro i _
    by_cases hi : i ∈ A
    · simp only [ite_eq_left hi]; exact continuous_const
    · simp only [ite_eq_right hi]
      exact (continuous_const.add continuous_id).mul (ih _)

theorem rankWeight_nonnegative_directions (M : Matroid ι) (hE : M.E = Set.univ)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (ds : List (ι → ℝ))
    (hds : ∀ a ∈ ds, ∀ i, 0 ≤ a i) (A : Set ι) :
    OnePositive (faceHessian (coeffDerivs ds (rankWeight M q)) A).toBilin' := by
  classical
  let F : ℝ → Matrix {i // i ∉ A} {i // i ∉ A} ℝ := fun t =>
    faceHessian (coeffDerivs (ds.map (fun a i => a i + t)) (rankWeight M q)) A
  have hzero : F 0 = faceHessian (coeffDerivs ds (rankWeight M q)) A := by
    simp [F]
  rw [← hzero]
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have : l.NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
  apply onePositive_of_tendsto (l := l) F (F 0)
  · intro i j
    have hc : Continuous (fun t => F t i j) := by
      dsimp [F, faceHessian]
      by_cases hij : i = j
      · simp only [ite_eq_left hij]; exact continuous_const
      · simp only [ite_eq_right hij]
        exact continuous_coeffDerivs_perturb ds (rankWeight M q) _
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact fun t => faceHessian_symm _ A
  · have hpos : ∀ᶠ t in l, 0 < t := self_mem_nhdsWithin
    filter_upwards [hpos] with t ht
    apply (rankWeight_positive_directions M hE q hq hq1 _ _).2 A
    intro b hb i
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    exact add_pos_of_nonneg_of_pos (hds a ha i) ht

lemma onePositive_matrix_substitution {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (hB : OnePositive B.toBilin') (L : Matrix ι κ ℝ) :
    OnePositive (L.transpose * B * L).toBilin' := by
  rw [← Matrix.toBilin'_comp]
  intro e he v hv
  exact hB (L.toLin' e) he (L.toLin' v) hv

omit sectionInstance12 sectionInstance13 in
lemma onePositive_smul [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm ℝ (ι → ℝ))
    (hB : OnePositive B) (c : ℝ) (hc : 0 < c) : OnePositive (c • B) := by
  intro e he v hv
  change 0 < c * B e e at he
  change c * B v e = 0 at hv
  change c * B v v ≤ 0
  have he' : 0 < B e e := (mul_pos_iff_of_pos_left hc).mp he
  have hv' : B v e = 0 := (mul_eq_zero.mp hv).resolve_left (ne_of_gt hc)
  exact mul_nonpos_of_nonneg_of_nonpos hc.le (hB e he' v hv')

lemma onePositive_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (hB : OnePositive B.toBilin') (e : κ → ι) :
    OnePositive (B.submatrix e e).toBilin' := by
  classical
  let L : Matrix ι κ ℝ := fun i j => if i = e j then 1 else 0
  have heq : L.transpose * B * L = B.submatrix e e := by
    ext i j
    change (∑ k, (∑ l, (if l = e i then (1 : ℝ) else 0) * B l k) *
      (if k = e j then (1 : ℝ) else 0)) = B (e i) (e j)
    simp
  rw [← heq]
  exact onePositive_matrix_substitution B hB L

end DerivativeClosure

theorem quadratic_split_bound (B : LinearMap.BilinForm ℝ V)
    (hB : OnePositive B) (hsymm : B.IsSymm)
    (e h d : V) (u X : ℝ) (hu : 0 < u)
    (hee : 0 < B e e) (hhe : B h e = 0) (hde : B d e = 0)
    (hhd : B h d = -2 * X) (hdd : B d d = -2 * u) :
    2 * X ^ 2 / u ≤ -B h h := by
  have hor : B (h - (X / u) • d) e = 0 := by
    simp [map_sub, map_smul, hhe, hde]
  have hn := hB e hee (h - (X / u) • d) hor
  have hdh : B d h = -2 * X := by rw [hsymm.eq d h, hhd]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hhd, hdh, hdd] at hn
  have hu0 : u ≠ 0 := ne_of_gt hu
  field_simp at hn ⊢
  nlinarith

section MatrixSplit

open scoped BigOperators
variable {ι : Type*} [Fintype ι] [sectionInstance15 : DecidableEq ι]

theorem splitMatrix_symm (V : Matrix ι ι ℝ) (sa sb : ι → ℝ) (u : ℝ)
    (hV : ∀ i j, V i j = V j i) : (splitMatrix V sa sb u).toBilin'.IsSymm := by
  apply matrix_bilin_symm
  intro i j
  cases i with
  | inl i => cases j with
    | inl j => exact hV i j
    | inr b => cases b <;> rfl
  | inr a => cases a <;> cases j with
    | inl j => rfl
    | inr b => cases b <;> rfl

theorem split_bound (V : Matrix ι ι ℝ) (sa sb h : ι → ℝ) (u : ℝ)
    (hu : 0 < u) (hV : ∀ i j, V i j = V j i)
    (hA : OnePositive (splitMatrix V sa sb u).toBilin')
    (hbal : ∑ i, (sa i + sb i) * h i = 0) :
    2 * (∑ i, h i * sa i)^2 / u ≤ - V.toBilin' h h := by
  have bal : (∑ i, h i * sb i) = -(∑ i, h i * sa i) := by
    simp_rw [add_mul, Finset.sum_add_distrib] at hbal
    have hs : ∀ f : ι → ℝ, (∑ i, f i * h i) = ∑ i, h i * f i := by
      intro f
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs sa, hs sb] at hbal
    linarith
  have hh : (splitMatrix V sa sb u).toBilin' (oldVector h) (oldVector h) =
      V.toBilin' h h := by
    simp [Matrix.toBilin'_apply, Fintype.sum_sum_type, 
      splitMatrix, oldVector]
  rw [← hh]
  apply quadratic_split_bound (splitMatrix V sa sb u).toBilin' hA
    (splitMatrix_symm V sa sb u hV) splitPositive (oldVector h) splitDifference
    u (∑ i, h i * sa i) hu
  · simpa [Matrix.toBilin'_apply, Fintype.sum_sum_type, Fintype.sum_bool,
      splitMatrix, splitPositive] using (show 0 < u + u by linarith)
  · simp [Matrix.toBilin'_apply, Fintype.sum_sum_type, 
      splitMatrix, splitPositive, oldVector, Finset.sum_add_distrib, bal]
  · simp [Matrix.toBilin'_apply, Fintype.sum_sum_type, 
      splitMatrix, splitPositive, splitDifference]
  · simp [Matrix.toBilin'_apply, Fintype.sum_sum_type, 
      splitMatrix, splitDifference, oldVector, Finset.sum_add_distrib,
      bal]
    ring
  · simp [Matrix.toBilin'_apply, Fintype.sum_sum_type, 
      splitMatrix, splitDifference]
    ring

theorem future_conservation (Va Vb : Matrix ι ι ℝ) (c h : ι → ℝ) (a : ℝ) :
    (futureChild Va c).toBilin' (extendVector h a) (extendVector h a) +
      (futureChild Vb c).toBilin' (extendVector h (-a)) (extendVector h (-a)) =
      (Va + Vb).toBilin' h h := by
  simp only [Matrix.toBilin'_apply, Fintype.sum_option, futureChild, extendVector,
    mul_zero, zero_mul, Matrix.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib, mul_neg, neg_mul, Finset.sum_neg_distrib]
  ring

omit sectionInstance15 in
theorem child_balance [DecidableEq ι] (s h : ι → ℝ) (u : ℝ) (hu : u ≠ 0) :
    ∑ i : Option ι, extendVector s u i *
      extendVector h (-(∑ j, h j * s j) / u) i = 0 := by
  simp only [Fintype.sum_option, extendVector]
  have hcomm : (∑ j, s j * h j) = ∑ j, h j * s j := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm]
  field_simp
  ring

omit sectionInstance15 in
theorem leaf_clique_bound [DecidableEq ι] (s W h H : ι → ℝ) (hub : ι)
    (hs : ∀ i, 0 < s i) (hW : ∀ i, 0 < W i)
    (hbal : ∑ i, s i * h i = 0) :
    2 * (∑ i, s i * h i * H i) ≤
      (∑ i, s i * (h i)^2 / W i) +
      ∑ i, W i * s i * (H i - H hub)^2 := by
  have hterm : ∀ i, 2*(s i*h i*(H i-H hub)) ≤
      s i*(h i)^2/W i + W i*s i*(H i-H hub)^2 := by
    intro i
    have hsq := mul_nonneg (div_nonneg (le_of_lt (hs i)) (le_of_lt (hW i)))
      (sq_nonneg (h i-W i*(H i-H hub)))
    have heq : s i*(h i)^2/W i + W i*s i*(H i-H hub)^2 -
        2*(s i*h i*(H i-H hub)) =
        (s i/W i)*(h i-W i*(H i-H hub))^2 := by
      field_simp [ne_of_gt (hW i)]
      ; ring
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  have hz : (∑ i, s i * h i * H hub) = 0 := by
    rw [← Finset.sum_mul, hbal, zero_mul]
  simpa only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hz, mul_zero, sub_zero] using hsum

end MatrixSplit

section RecursiveTransport
open scoped BigOperators Classical Matrix
variable {Γ : Type*} [sectionInstance16 : Fintype Γ] [sectionInstance17 : DecidableEq Γ]

omit sectionInstance16 sectionInstance17 in
lemma range_appendPoint [Fintype Γ] [DecidableEq Γ] {ι : Type*} (e : ι → Γ) (a : Γ) :
    Set.range (appendPoint e a) = insert a (Set.range e) := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i,rfl⟩
  · rintro (rfl | ⟨i,rfl⟩)
    · exact ⟨none,rfl⟩
    · exact ⟨some i,rfl⟩

omit sectionInstance16 sectionInstance17 in
lemma appendPoint_injective [Fintype Γ] [DecidableEq Γ] {ι : Type*} (e : ι → Γ) (a : Γ)
    (he : Function.Injective e) (ha : a ∉ Set.range e) :
    Function.Injective (appendPoint e a) := by
  intro i j h
  cases i <;> cases j
  · rfl
  · exact False.elim (ha ⟨_,h.symm⟩)
  · exact False.elim (ha ⟨_,h⟩)
  · exact congrArg some (he h)

lemma slotsFresh_child {ι : Type*} (e : ι → Γ) (A : Set Γ) (p : Γ × Γ)
    (ps : List (Γ × Γ)) (h : SlotsFresh (p::ps) (A ∪ Set.range e)) :
    SlotsFresh ps (insert p.2 A ∪ Set.range (appendPoint e p.1)) ∧
      SlotsFresh ps (insert p.1 A ∪ Set.range (appendPoint e p.2)) := by
  obtain ⟨_,_,_,ht⟩ := h
  rw [range_appendPoint, range_appendPoint]
  constructor
  · convert ht using 1 ; ext x ; simp ; tauto
  · convert ht using 1 ; ext x ; simp ; tauto

omit sectionInstance16 sectionInstance17 in
lemma appendPoint_fresh [Fintype Γ] [DecidableEq Γ] {ι : Type*} (e : ι → Γ) (A : Set Γ) (a b : Γ)
    (he : ∀ i, e i ∉ A) (hab : a ≠ b) (ha : a ∉ A)
    (hb : b ∉ Set.range e) : ∀ i, appendPoint e a i ∉ insert b A := by
  intro i
  cases i with
  | none => exact fun h => h.elim hab ha
  | some i =>
    intro h
    rcases h with h | h
    · exact hb ⟨i,h⟩
    · exact he i h

omit sectionInstance16 sectionInstance17 in
lemma pairMatrix_symm [Fintype Γ] [DecidableEq Γ] {ι : Type*} [DecidableEq ι]
    (f : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) :
    ∀ i j, pairMatrix f A e i j = pairMatrix f A e j i := by
  intro i j
  by_cases hij : i = j
  · subst j; rfl
  · simp only [pairMatrix, hij, Ne.symm hij, ite_false, Set.insert_comm]

lemma rankWeight_hasSlotSignature (M : Matroid Γ) (hE : M.E = Set.univ)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) : HasSlotSignature (rankWeight M q) := by
  intro ps A
  apply rankWeight_nonnegative_directions M hE q hq hq1
  intro a ha i
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
  exact slotDirection_nonneg _ i

lemma pairMatrix_signature {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Set Γ → ℝ) (hSig : HasSlotSignature f)
    (ps : List (Γ × Γ)) (A : Set Γ) (e : ι → Γ)
    (he : Function.Injective e) (heA : ∀ i, e i ∉ A) :
    OnePositive (pairMatrix (slotTotal ps f) A e).toBilin' := by
  let e' : ι → {i // i ∉ A} := fun i => ⟨e i,heA i⟩
  have hEq : pairMatrix (slotTotal ps f) A e =
      (faceHessian (slotTotal ps f) A).submatrix e' e' := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [pairMatrix,faceHessian]
    · have hne : e' i ≠ e' j := fun h => hij (he (congrArg Subtype.val h))
      simp only [pairMatrix, hij, ite_false, Matrix.submatrix_apply, faceHessian, hne]
      congr 1
      ext x
      simp [e']
  rw [hEq]
  exact onePositive_submatrix _ (hSig ps A) e'

section Clique
variable {ι : Type*} [Fintype ι] [sectionInstance19 : DecidableEq ι]

lemma star_le_half_clique (E : ι → ι → ℝ)
    (hE : ∀ i j, 0 ≤ E i j) (hS : ∀ i j, E i j = E j i)
    (hD : ∀ i, E i i = 0) (hub : ι) :
    (∑ i, E i hub) ≤ (∑ i, ∑ j, E i j) / 2 := by
  have hrest : (∑ i ∈ Finset.univ.erase hub, E i hub) ≤
      ∑ i ∈ Finset.univ.erase hub, ∑ j, E i j := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => hE i j) (Finset.mem_univ hub)
  rw [Finset.sum_erase (f := fun i => E i hub) _ (hD hub)] at hrest
  have ht := Finset.sum_erase_add Finset.univ (fun i => ∑ j, E i j)
    (Finset.mem_univ hub)
  have hrow : (∑ j, E hub j) = ∑ j, E j hub := by simp_rw [hS hub]
  rw [hrow] at ht
  linarith

lemma clique_linear_bound [Nonempty ι] (s W h H : ι → ℝ)
    (hs : ∀ i, 0 < s i) (hW : ∀ i, 0 < W i)
    (hbal : ∑ i, s i*h i = 0) :
    2*(∑ i, s i*h i*H i) ≤ (∑ i, s i*(h i)^2/W i) + cliqueEnergy s W H := by
  obtain ⟨hub,_,hhub⟩ := Finset.exists_max_image Finset.univ (fun i => W i*s i)
    Finset.univ_nonempty
  have hl := leaf_clique_bound s W h H hub hs hW hbal
  have he := star_le_half_clique (fun i j => min (W i*s i) (W j*s j)*(H i-H j)^2)
    (fun i j => mul_nonneg (le_min (mul_pos (hW i) (hs i)).le
      (mul_pos (hW j) (hs j)).le) (sq_nonneg _))
    (by intro i j; rw [min_comm]; ring) (by intro i; simp) hub
  simp_rw [min_eq_left (hhub _ (Finset.mem_univ _))] at he
  unfold cliqueEnergy
  linarith

end Clique

variable {ι : Type*} [sectionInstance20 : Fintype ι] [sectionInstance21 : DecidableEq ι]

omit sectionInstance16 sectionInstance17 sectionInstance20 sectionInstance21 in
lemma splitEmbedding_injective [Fintype Γ] [DecidableEq Γ] [Fintype ι] [DecidableEq ι] (e : ι → Γ) (a b : Γ)
    (he : Function.Injective e) (hab : a ≠ b)
    (ha : a ∉ Set.range e) (hb : b ∉ Set.range e) :
    Function.Injective (splitEmbedding e a b) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (he hij)
    | inr x =>
      cases x with
      | false => exact False.elim (ha ⟨i,hij⟩)
      | true => exact False.elim (hb ⟨i,hij⟩)
  | inr x =>
    cases j with
    | inl j =>
      cases x with
      | false => exact False.elim (ha ⟨j,hij.symm⟩)
      | true => exact False.elim (hb ⟨j,hij.symm⟩)
    | inr y =>
      cases x <;> cases y
      · rfl
      · exact False.elim (hab hij)
      · exact False.elim (hab hij.symm)
      · rfl

omit sectionInstance16 sectionInstance17 sectionInstance20 in
lemma pairMatrix_split [Fintype Γ] [DecidableEq Γ] [Fintype ι] (f : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (a b : Γ) :
    pairMatrix f A (splitEmbedding e a b) =
      splitMatrix (pairMatrix f A e)
        (fun i => f (insert (e i) (insert b A)))
        (fun i => f (insert (e i) (insert a A)))
        (f (insert a (insert b A))) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [pairMatrix, splitMatrix, splitEmbedding]
    | inr x => cases x <;> simp [pairMatrix, splitMatrix, splitEmbedding]
  | inr x =>
    cases j with
    | inl j => cases x <;> simp [pairMatrix, splitMatrix, splitEmbedding, Set.insert_comm]
    | inr y => cases x <;> cases y <;>
      simp [pairMatrix, splitMatrix, splitEmbedding, Set.insert_comm]

lemma slot_split_signature (f : Set Γ → ℝ) (hSig : HasSlotSignature f)
    (ps : List (Γ × Γ)) (A : Set Γ) (e : ι → Γ) (a b : Γ)
    (he : Function.Injective e) (heA : ∀ i, e i ∉ A) (hab : a ≠ b)
    (ha : a ∉ A ∪ Set.range e) (hb : b ∉ A ∪ Set.range e) :
    OnePositive (splitMatrix (pairMatrix (slotTotal ps f) A e)
      (fun i => slotTotal ps f (insert (e i) (insert b A)))
      (fun i => slotTotal ps f (insert (e i) (insert a A)))
      (slotTotal ps f (insert a (insert b A)))).toBilin' := by
  rw [← pairMatrix_split]
  apply pairMatrix_signature f hSig ps A _
    (splitEmbedding_injective e a b he hab (fun h => ha (Or.inr h)) (fun h => hb (Or.inr h)))
  intro i
  cases i with
  | inl i => exact heA i
  | inr x =>
    cases x with
    | false => exact fun h => ha (Or.inl h)
    | true => exact fun h => hb (Or.inl h)

omit sectionInstance16 sectionInstance17 sectionInstance20 in
lemma pairMatrix_append [Fintype Γ] [DecidableEq Γ] [Fintype ι] (f : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (a b : Γ) :
    pairMatrix f (insert b A) (appendPoint e a) =
      futureChild (pairMatrix f (insert b A) e)
        (fun i => f (insert (e i) (insert a (insert b A)))) := by
  ext i j
  cases i <;> cases j <;> simp [pairMatrix, appendPoint, futureChild, Set.insert_comm]

omit sectionInstance20 sectionInstance21 in
lemma slotTotal_parent [Fintype ι] [DecidableEq ι] (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (A : Set Γ)
    (e : ι → Γ) (p : Γ × Γ)
    (hp : p.1 ≠ p.2) (ha : p.1 ∉ A ∪ Set.range e) (hb : p.2 ∉ A ∪ Set.range e) :
    ∀ i, slotTotal (p::ps) f (insert (e i) A) =
      slotTotal ps f (insert (e i) (insert p.2 A)) +
      slotTotal ps f (insert (e i) (insert p.1 A)) := by
  intro i
  rw [slotTotal_cons p ps f _ hp]
  · rw [Set.insert_comm p.1, Set.insert_comm p.2, add_comm]
  · intro h
    exact h.elim (fun h => ha (Or.inr ⟨i,h.symm⟩)) (fun h => ha (Or.inl h))
  · intro h
    exact h.elim (fun h => hb (Or.inr ⟨i,h.symm⟩)) (fun h => hb (Or.inl h))

omit sectionInstance20 in
lemma pairMatrix_parent [Fintype ι] (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (A : Set Γ)
    (e : ι → Γ) (p : Γ × Γ)
    (hp : p.1 ≠ p.2) (ha : p.1 ∉ A ∪ Set.range e) (hb : p.2 ∉ A ∪ Set.range e) :
    pairMatrix (slotTotal (p::ps) f) A e =
      pairMatrix (slotTotal ps f) (insert p.2 A) e +
      pairMatrix (slotTotal ps f) (insert p.1 A) e := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [pairMatrix]
  simp only [pairMatrix, hij, ite_false, Matrix.add_apply]
  rw [slotTotal_cons p ps f _ hp]
  · rw [Set.insert_comm p.1 (e i), Set.insert_comm p.1 (e j),
      Set.insert_comm p.2 (e i), Set.insert_comm p.2 (e j), add_comm]
  · intro h
    rcases h with h | h | h
    · exact ha (Or.inr ⟨i,h.symm⟩)
    · exact ha (Or.inr ⟨j,h.symm⟩)
    · exact ha (Or.inl h)
  · intro h
    rcases h with h | h | h
    · exact hb (Or.inr ⟨i,h.symm⟩)
    · exact hb (Or.inr ⟨j,h.symm⟩)
    · exact hb (Or.inl h)

lemma slot_future_conservation (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (A : Set Γ)
    (e : ι → Γ) (p : Γ × Γ) (h : ι → ℝ) (c : ℝ)
    (hp : p.1 ≠ p.2) (ha : p.1 ∉ A ∪ Set.range e) (hb : p.2 ∉ A ∪ Set.range e) :
    (pairMatrix (slotTotal ps f) (insert p.2 A) (appendPoint e p.1)).toBilin'
      (extendVector h c) (extendVector h c) +
    (pairMatrix (slotTotal ps f) (insert p.1 A) (appendPoint e p.2)).toBilin'
      (extendVector h (-c)) (extendVector h (-c)) =
    (pairMatrix (slotTotal (p::ps) f) A e).toBilin' h h := by
  rw [pairMatrix_append, pairMatrix_append, pairMatrix_parent ps f A e p hp ha hb]
  have heq : (fun i => slotTotal ps f (insert (e i) (insert p.2 (insert p.1 A)))) =
      (fun i => slotTotal ps f (insert (e i) (insert p.1 (insert p.2 A)))) := by
    simp only [Set.insert_comm p.2 p.1]
  rw [heq]
  exact future_conservation _ _ _ h c

omit sectionInstance16 sectionInstance17 in
lemma transportEnergy_nil [Fintype Γ] [DecidableEq Γ] {ι : Type*} [Fintype ι]
    (f H : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ) :
    transportEnergy [] f H A e W =
      cliqueEnergy (fun i => f (insert (e i) A)) (fun i => W (e i))
      (fun i => H (insert (e i) A)) := by rw [transportEnergy]

omit sectionInstance16 sectionInstance17 in
lemma transportEnergy_cons [Fintype Γ] [DecidableEq Γ] {ι : Type*} [Fintype ι]
    (p : Γ × Γ) (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ) :
    transportEnergy (p::ps) f H A e W =
      transportEnergy ps f H (insert p.2 A) (appendPoint e p.1) W +
      transportEnergy ps f H (insert p.1 A) (appendPoint e p.2) W := by rw [transportEnergy]

lemma transportDemand_split (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (p : Γ × Γ) (h : ι → ℝ) (c : ℝ)
    (hp : p.1 ≠ p.2) (ha : p.1 ∉ A ∪ Set.range e) (hb : p.2 ∉ A ∪ Set.range e) :
    transportDemand ps f H (insert p.2 A) (appendPoint e p.1) (extendVector h c) +
    transportDemand ps f H (insert p.1 A) (appendPoint e p.2) (extendVector h (-c)) =
    transportDemand (p::ps) f H A e h := by
  unfold transportDemand
  simp only [Fintype.sum_option, extendVector, appendPoint]
  rw [Set.insert_comm p.2 p.1]
  simp_rw [slotTotal_parent ps (fun S => f S*H S) A e p hp ha hb]
  simp only [mul_add, Finset.sum_add_distrib, neg_mul]
  ring

lemma transportCorrection_split (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (p : Γ × Γ) (h : ι → ℝ) (c : ℝ) (W : Γ → ℝ)
    (hp : p.1 ≠ p.2) (ha : p.1 ∉ A ∪ Set.range e) (hb : p.2 ∉ A ∪ Set.range e) :
    transportCorrection (p::ps) f A e h W =
      (pairMatrix (slotTotal ps f) A e).toBilin' h h / W p.1 +
      (transportCorrection ps f (insert p.2 A) (appendPoint e p.1) (extendVector h c) W +
       transportCorrection ps f (insert p.1 A) (appendPoint e p.2) (extendVector h (-c)) W) := by
  simp only [transportCorrection, slotPunctures, List.map_cons, List.map_map, List.sum_cons]
  rw [← List.sum_map_add]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  dsimp
  rw [← add_div, slot_future_conservation x.2 f A e p h c hp ha hb]

lemma transportPotential_split (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (p : Γ × Γ) (h : ι → ℝ) (X u : ℝ) (W : Γ → ℝ)
    (hp : p.1 ≠ p.2) (ha : p.1 ∉ A ∪ Set.range e) (hb : p.2 ∉ A ∪ Set.range e)
    (hu : u = slotTotal ps f (insert p.1 (insert p.2 A))) (hu0 : u ≠ 0)
    (hw : W p.1 = W p.2) (hw0 : W p.1 ≠ 0) :
    transportPotential ps f (insert p.2 A) (appendPoint e p.1) (extendVector h (-X/u)) W +
    transportPotential ps f (insert p.1 A) (appendPoint e p.2) (extendVector h (X/u)) W =
      transportPotential (p::ps) f A e h W + 2*X^2/(u*W p.1) := by
  unfold transportPotential
  simp only [Fintype.sum_option, extendVector, appendPoint]
  rw [Set.insert_comm p.2 p.1, ← hu, ← hw]
  simp_rw [slotTotal_parent ps f A e p hp ha hb]
  simp only [add_mul, add_div, Finset.sum_add_distrib]
  field_simp
  ring

theorem transport_linear_bound (ps : List (Γ × Γ)) :
    ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
      (f H : Set Γ → ℝ) (A : Set Γ) (e : κ → Γ) (h : κ → ℝ) (W : Γ → ℝ),
      (∀ S, 0 < f S) → HasSlotSignature f → Function.Injective e →
      (∀ i, e i ∉ A) → SlotsFresh ps (A ∪ Set.range e) →
      (∀ i, 0 < W i) → (∀ p ∈ ps, W p.1 = W p.2) →
      (∑ i, slotTotal ps f (insert (e i) A)*h i = 0) →
      2*transportDemand ps f H A e h ≤
        transportPotential ps f A e h W - transportCorrection ps f A e h W +
          transportEnergy ps f H A e W := by
  induction ps with
  | nil =>
    intro κ _ _ _ f H A e h W hf _ _ _ _ hW _ hbal
    have hb : ∑ i, f (insert (e i) A)*h i = 0 := hbal
    have hl := clique_linear_bound (fun i => f (insert (e i) A)) (fun i => W (e i)) h
      (fun i => H (insert (e i) A)) (fun i => hf _) (fun i => hW _) hb
    simpa [transportDemand, transportPotential, transportCorrection, slotPunctures,
      slotTotal, coeffDerivs, transportEnergy_nil, mul_comm, mul_left_comm, mul_assoc] using hl
  | cons p ps ih =>
    intro κ _ _ _ f H A e h W hf hSig he heA hFresh hW hw hbal
    obtain ⟨hab,ha,hb,ht⟩ := hFresh
    have hFresh' : SlotsFresh (p::ps) (A ∪ Set.range e) := ⟨hab,ha,hb,ht⟩
    obtain ⟨hfa,hfb⟩ := slotsFresh_child e A p ps hFresh'
    let sa : κ → ℝ := fun i => slotTotal ps f (insert (e i) (insert p.2 A))
    let sb : κ → ℝ := fun i => slotTotal ps f (insert (e i) (insert p.1 A))
    let u : ℝ := slotTotal ps f (insert p.1 (insert p.2 A))
    let X : ℝ := ∑ i, h i*sa i
    let c : ℝ := -X/u
    have hu : 0 < u := slotTotal_pos ps f hf _
      (ht.mono (Set.insert_subset_insert (Set.insert_subset_insert Set.subset_union_left)))
    have hb0 : (∑ i, (sa i+sb i)*h i) = 0 := by
      simpa only [slotTotal_parent ps f A e p hab ha hb] using hbal
    have hXb : (∑ i, h i*sb i) = -X := by
      simp only [add_mul, Finset.sum_add_distrib] at hb0
      have ha' : (∑ i, sa i*h i) = X := by dsimp [X]; apply Finset.sum_congr rfl; intro i _; ring
      have hb' : (∑ i, sb i*h i) = ∑ i, h i*sb i := by apply Finset.sum_congr rfl; intro i _; ring
      rw [ha',hb'] at hb0
      linarith
    have hcB : -c = -(∑ i, h i*sb i)/u := by rw [hXb]; dsimp [c]; ring
    have hba : ∑ i, slotTotal ps f (insert (appendPoint e p.1 i) (insert p.2 A)) *
        extendVector h c i = 0 := by
      have hc := child_balance sa h u (ne_of_gt hu)
      simp only [Fintype.sum_option, extendVector] at hc
      simpa only [Fintype.sum_option, extendVector, appendPoint, sa, u, c, X] using hc
    have hbb : ∑ i, slotTotal ps f (insert (appendPoint e p.2 i) (insert p.1 A)) *
        extendVector h (-c) i = 0 := by
      rw [hcB]
      have hc := child_balance sb h u (ne_of_gt hu)
      simp only [Fintype.sum_option, extendVector] at hc
      simpa only [Fintype.sum_option, extendVector, appendPoint, u, sb, Set.insert_comm p.2 p.1] using hc
    have hwa := hw p (List.mem_cons_self ..)
    have hwt : ∀ p ∈ ps, W p.1 = W p.2 := fun q hq => hw q (List.mem_cons_of_mem _ hq)
    have hla := ih f H (insert p.2 A) (appendPoint e p.1) (extendVector h c) W
      hf hSig (appendPoint_injective e p.1 he (fun h => ha (Or.inr h)))
      (appendPoint_fresh e A p.1 p.2 heA hab (fun h => ha (Or.inl h))
        (fun h => hb (Or.inr h))) hfa hW hwt hba
    have hlb := ih f H (insert p.1 A) (appendPoint e p.2) (extendVector h (-c)) W
      hf hSig (appendPoint_injective e p.2 he (fun h => hb (Or.inr h)))
      (appendPoint_fresh e A p.2 p.1 heA hab.symm (fun h => hb (Or.inl h))
        (fun h => ha (Or.inr h))) hfb hW hwt hbb
    have hsplit := split_bound (pairMatrix (slotTotal ps f) A e) sa sb h u hu
      (pairMatrix_symm _ A e) (slot_split_signature f hSig ps A e p.1 p.2 he heA hab ha hb) hb0
    have hcost : 2*X^2/(u*W p.1) ≤
        -(pairMatrix (slotTotal ps f) A e).toBilin' h h / W p.1 := by
      simpa only [X, div_div] using div_le_div_of_nonneg_right hsplit (hW p.1).le
    have hpot := transportPotential_split ps f A e p h X u W hab ha hb rfl
      (ne_of_gt hu) hwa (ne_of_gt (hW p.1))
    have hcN : X/u = -c := by dsimp [c]; ring
    rw [hcN] at hpot
    change transportPotential ps f (insert p.2 A) (appendPoint e p.1) (extendVector h c) W +
      transportPotential ps f (insert p.1 A) (appendPoint e p.2) (extendVector h (-c)) W = _ at hpot
    rw [← transportDemand_split ps f H A e p h c hab ha hb,
      transportEnergy_cons, transportCorrection_split ps f A e p h c W hab ha hb]
    rw [neg_div] at hcost
    linarith

end RecursiveTransport

section TransportRoot
open scoped BigOperators Classical Matrix
variable {Γ ι : Type*} [sectionInstance22 : Fintype Γ] [sectionInstance23 : DecidableEq Γ]
  [Fintype ι] [sectionInstance25 : DecidableEq ι]

omit sectionInstance25 in
lemma transportDemand_smul [DecidableEq ι] (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) (c : ℝ) :
    transportDemand ps f H A e (c • h) = c * transportDemand ps f H A e h := by
  simp [transportDemand, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

omit sectionInstance25 in
lemma transportPotential_smul [DecidableEq ι] (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) (W : Γ → ℝ) (c : ℝ) :
    transportPotential ps f A e (c • h) W = c^2 * transportPotential ps f A e h W := by
  unfold transportPotential
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma transportCorrection_smul (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) (W : Γ → ℝ) (c : ℝ) :
    transportCorrection ps f A e (c • h) W = c^2 * transportCorrection ps f A e h W := by
  unfold transportCorrection
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

lemma squared_le_of_linear_scalings (D C E : ℝ) (hC : 0 < C)
    (h : ∀ t : ℝ, 2*t*D ≤ t^2*C + E) : D^2 ≤ C*E := by
  have ht := h (D/C)
  have ht' := (mul_le_mul_of_nonneg_right ht hC.le)
  field_simp at ht'
  nlinarith

theorem transport_squared_bound [Nonempty ι] (ps : List (Γ × Γ))
    (f H : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) (W : Γ → ℝ)
    (hf : ∀ S, 0 < f S) (hSig : HasSlotSignature f) (he : Function.Injective e)
    (heA : ∀ i, e i ∉ A) (hps : SlotsFresh ps (A ∪ Set.range e))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2)
    (hbal : ∑ i, slotTotal ps f (insert (e i) A)*h i = 0)
    (hC : 0 < transportPotential ps f A e h W - transportCorrection ps f A e h W) :
    (transportDemand ps f H A e h)^2 ≤
      (transportPotential ps f A e h W - transportCorrection ps f A e h W) *
        transportEnergy ps f H A e W := by
  apply squared_le_of_linear_scalings _ _ _ hC
  intro t
  have hbal' : ∑ i, slotTotal ps f (insert (e i) A)*(t • h) i = 0 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm _ t, ← Finset.mul_sum, hbal, mul_zero]
  have ht := transport_linear_bound ps f H A e (t • h) W hf hSig he heA hps hW hw hbal'
  rw [transportDemand_smul,transportPotential_smul,transportCorrection_smul] at ht
  nlinarith

lemma slotTotal_nonneg (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (hf : ∀ S, 0 ≤ f S) (A : Set Γ) : 0 ≤ slotTotal ps f A := by
  induction ps generalizing A with
  | nil => exact hf A
  | cons p ps ih =>
    change 0 ≤ coeffDeriv (pairDirection p) (slotTotal ps f) A
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (slotDirection_nonneg _ i) (ih _)

omit sectionInstance22 sectionInstance23 in
lemma rootEmbedding_injective [Fintype Γ] [DecidableEq Γ] (p d : Γ) (hpd : p ≠ d) :
    Function.Injective (rootEmbedding p d) := by
  intro i j h
  cases i <;> cases j <;> simp_all [rootEmbedding]

lemma rootPotential (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ)
    (hsp : slotTotal ps f (insert p A) ≠ 0) (hsd : slotTotal ps f (insert d A) ≠ 0) :
    transportPotential ps f A (rootEmbedding p d)
      (rootDemand (slotTotal ps f (insert p A)) (slotTotal ps f (insert d A))) W =
    1/(slotTotal ps f (insert p A)*W p) + 1/(slotTotal ps f (insert d A)*W d) := by
  simp only [transportPotential, Fintype.sum_bool, rootEmbedding, rootDemand,
    Bool.false_eq_true, ite_false, ite_true]
  field_simp
  ; ring

lemma rootCorrection (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) (sp sd : ℝ) :
    transportCorrection ps f A (rootEmbedding p d) (rootDemand sp sd) W =
      -(2/(sp*sd)*((slotPunctures ps).map
        (fun x => slotTotal x.2 f (insert p (insert d A))/W x.1.1)).sum) := by
  unfold transportCorrection
  rw [← neg_mul, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  simp only [Matrix.toBilin'_apply, Fintype.sum_bool, pairMatrix, rootEmbedding,
    rootDemand, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
    Set.insert_comm d p]
  ring

lemma rootCoefficient_pos (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (hf : ∀ S, 0 < f S) (A : Set Γ) (p d : Γ) (W : Γ → ℝ)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d))) (hW : ∀ i, 0 < W i) :
    0 < rootCoefficient ps f A p d W := by
  have hfp : SlotsFresh ps (insert p A) := hps.mono (by
    intro x hx
    rcases hx with rfl | hx
    · exact Or.inr ⟨false,rfl⟩
    · exact Or.inl hx)
  have hfd : SlotsFresh ps (insert d A) := hps.mono (by
    intro x hx
    rcases hx with rfl | hx
    · exact Or.inr ⟨true,rfl⟩
    · exact Or.inl hx)
  have hp := slotTotal_pos ps f hf _ hfp
  have hd := slotTotal_pos ps f hf _ hfd
  unfold rootCoefficient
  apply add_pos_of_pos_of_nonneg
  · exact add_pos (one_div_pos.mpr (mul_pos hp (hW p)))
      (one_div_pos.mpr (mul_pos hd (hW d)))
  · apply mul_nonneg (div_nonneg (by norm_num) (mul_pos hp hd).le)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact div_nonneg (slotTotal_nonneg _ f (fun S => (hf S).le) _) (hW _).le

theorem transport_root_bound (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ)
    (hf : ∀ S, 0 < f S) (hSig : HasSlotSignature f)
    (hpd : p ≠ d) (hpA : p ∉ A) (hdA : d ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2) :
    (slotTotal ps (fun S => f S*H S) (insert p A) / slotTotal ps f (insert p A) -
      slotTotal ps (fun S => f S*H S) (insert d A) / slotTotal ps f (insert d A))^2 ≤
    rootCoefficient ps f A p d W * transportEnergy ps f H A (rootEmbedding p d) W := by
  have heA : ∀ i, rootEmbedding p d i ∉ A := by
    intro i; cases i <;> assumption
  have hfresh : ∀ i, SlotsFresh ps (insert (rootEmbedding p d i) A) := by
    intro i
    apply hps.mono
    intro x hx
    rcases hx with rfl | hx
    · exact Or.inr ⟨i,rfl⟩
    · exact Or.inl hx
  have hsp := slotTotal_pos ps f hf _ (hfresh false)
  have hsd := slotTotal_pos ps f hf _ (hfresh true)
  change 0 < slotTotal ps f (insert p A) at hsp
  change 0 < slotTotal ps f (insert d A) at hsd
  let h := rootDemand (slotTotal ps f (insert p A)) (slotTotal ps f (insert d A))
  have hbal : ∑ i, slotTotal ps f (insert (rootEmbedding p d i) A)*h i = 0 := by
    simp [h,rootDemand,rootEmbedding, ne_of_gt hsp, ne_of_gt hsd]
  have hcoef : transportPotential ps f A (rootEmbedding p d) h W -
      transportCorrection ps f A (rootEmbedding p d) h W = rootCoefficient ps f A p d W := by
    dsimp [h]
    rw [rootPotential ps f A p d W (ne_of_gt hsp) (ne_of_gt hsd), rootCorrection]
    simp only [rootCoefficient, sub_neg_eq_add]
  have ht := transport_squared_bound ps f H A (rootEmbedding p d) h W hf hSig
    (rootEmbedding_injective p d hpd) heA hps hW hw hbal
    (by rw [hcoef]; exact rootCoefficient_pos ps f hf A p d W hps hW)
  rw [hcoef] at ht
  simpa [transportDemand,h,rootDemand,rootEmbedding,Fintype.sum_bool,div_eq_mul_inv,
    mul_comm,sub_eq_add_neg,add_comm] using ht

end TransportRoot

section TransportGraph
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance26 : Fintype Γ] [sectionInstance27 : DecidableEq Γ]

omit sectionInstance26 sectionInstance27 in
lemma transportEdges_fixed [Fintype Γ] [DecidableEq Γ] (ps : List (Γ × Γ)) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Set Γ) (e : ι → Γ)
      (ST : Set Γ × Set Γ), ST ∈ transportEdges ps A e →
      A ⊆ ST.1 ∩ ST.2 := by
  induction ps with
  | nil =>
    intro ι _ _ A e ST h
    rw [transportEdges] at h
    obtain ⟨ij,_,rfl⟩ := Finset.mem_image.mp h
    exact Set.subset_inter (Set.subset_insert _ _) (Set.subset_insert _ _)
  | cons p ps ih =>
    intro ι _ _ A e ST h
    rw [transportEdges] at h
    rcases Finset.mem_union.mp h with h | h
    · exact (Set.subset_insert p.2 A).trans (ih _ _ _ h)
    · exact (Set.subset_insert p.1 A).trans (ih _ _ _ h)

lemma transportEdges_not_holes (ps : List (Γ × Γ)) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Set Γ) (e : ι → Γ),
      Function.Injective e → (∀ i, e i ∉ A) → SlotsFresh ps (A ∪ Set.range e) →
      ∀ ST ∈ transportEdges ps A e, ∀ i, e i ∉ ST.1 ∩ ST.2 := by
  induction ps with
  | nil =>
    intro ι _ _ A e he heA _ ST h i
    rw [transportEdges] at h
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp h
    have hij' := (Finset.mem_filter.mp hij).2
    intro ⟨hi,hj⟩
    have hi' : e i = e ij.1 := hi.resolve_right (heA i)
    have hj' : e i = e ij.2 := hj.resolve_right (heA i)
    exact hij' ((he hi').symm.trans (he hj'))
  | cons p ps ih =>
    intro ι _ _ A e he heA hps ST h i
    obtain ⟨hab,ha,hb,ht⟩ := hps
    have hps' : SlotsFresh (p::ps) (A ∪ Set.range e) := ⟨hab,ha,hb,ht⟩
    obtain ⟨hfa,hfb⟩ := slotsFresh_child e A p ps hps'
    rw [transportEdges] at h
    rcases Finset.mem_union.mp h with h | h
    · exact ih (insert p.2 A) (appendPoint e p.1)
        (appendPoint_injective e p.1 he (fun h => ha (Or.inr h)))
        (appendPoint_fresh e A p.1 p.2 heA hab (fun h => ha (Or.inl h))
          (fun h => hb (Or.inr h))) hfa ST h (some i)
    · exact ih (insert p.1 A) (appendPoint e p.2)
        (appendPoint_injective e p.2 he (fun h => hb (Or.inr h)))
        (appendPoint_fresh e A p.2 p.1 heA hab.symm (fun h => hb (Or.inl h))
          (fun h => ha (Or.inr h))) hfb ST h (some i)

lemma transportEdges_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ps : List (Γ × Γ)) (A : Set Γ) (e : ι → Γ) (p : Γ × Γ)
    (he : Function.Injective e) (heA : ∀ i, e i ∉ A)
    (hps : SlotsFresh (p::ps) (A ∪ Set.range e)) :
    Disjoint (transportEdges ps (insert p.2 A) (appendPoint e p.1))
      (transportEdges ps (insert p.1 A) (appendPoint e p.2)) := by
  apply Finset.disjoint_left.mpr
  intro ST ha hb
  have hfix := transportEdges_fixed ps (insert p.2 A) (appendPoint e p.1) ST ha
  obtain ⟨hab,hpa,hpb,ht⟩ := hps
  have hps' : SlotsFresh (p::ps) (A ∪ Set.range e) := ⟨hab,hpa,hpb,ht⟩
  have hn := transportEdges_not_holes ps (insert p.1 A) (appendPoint e p.2)
    (appendPoint_injective e p.2 he (fun h => hpb (Or.inr h)))
    (appendPoint_fresh e A p.2 p.1 heA hab.symm (fun h => hpb (Or.inl h))
      (fun h => hpa (Or.inr h))) (slotsFresh_child e A p ps hps').2 ST hb none
  exact hn (hfix (Set.mem_insert _ _))

omit sectionInstance26 sectionInstance27 in
lemma missingMultiplier_child_left [Fintype Γ] [DecidableEq Γ] {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (p : Γ × Γ) (e : ι → Γ) (W : Γ → ℝ)
    (S : Set Γ) (hb : p.2 ∈ S) :
    missingMultiplier (p::ps) e W S = missingMultiplier ps (appendPoint e p.1) W S := by
  simp only [missingMultiplier, List.map_cons, List.sum_cons, Fintype.sum_option, appendPoint]
  simp only [hb, and_true]
  ac_rfl

omit sectionInstance26 sectionInstance27 in
lemma missingMultiplier_child_right [Fintype Γ] [DecidableEq Γ] {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (p : Γ × Γ) (e : ι → Γ) (W : Γ → ℝ)
    (S : Set Γ) (ha : p.1 ∈ S) (hw : W p.1 = W p.2) :
    missingMultiplier (p::ps) e W S = missingMultiplier ps (appendPoint e p.2) W S := by
  simp only [missingMultiplier, List.map_cons, List.sum_cons, Fintype.sum_option, appendPoint]
  simp only [ha, true_and, hw]
  ac_rfl

omit sectionInstance26 in
lemma missingMultiplier_leaf [Fintype Γ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ) (he : Function.Injective e)
    (heA : ∀ i, e i ∉ A) (i : ι) :
    missingMultiplier [] e W (insert (e i) A) = W (e i) := by
  simp [missingMultiplier, Set.mem_insert_iff, he.eq_iff, heA]

omit sectionInstance26 sectionInstance27 in
lemma insert_embedding_injective [Fintype Γ] [DecidableEq Γ] {ι : Type*} (A : Set Γ) (e : ι → Γ)
    (he : Function.Injective e) (heA : ∀ i, e i ∉ A) :
    Function.Injective (fun i => insert (e i) A) := by
  intro i j hij
  apply he
  have hi : e i ∈ insert (e j) A := (Set.ext_iff.mp hij (e i)).mp (Set.mem_insert _ _)
  exact hi.resolve_right (heA i)

lemma offdiag_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → ℝ) (hE : ∀ i, E i i = 0) :
    ∑ ij ∈ Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2), E ij.1 ij.2 =
      ∑ i, ∑ j, E i j := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j; simp [hE]
  · simp [hij]

lemma transportEnergy_leaf_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f H : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ)
    (he : Function.Injective e) (heA : ∀ i, e i ∉ A) :
    transportEnergy [] f H A e W =
      (∑ ST ∈ transportEdges [] A e, slotEdgeEnergy [] e W f H ST)/2 := by
  have hi := insert_embedding_injective A e he heA
  have hp : Function.Injective (fun ij : ι × ι => (insert (e ij.1) A, insert (e ij.2) A)) := by
    intro ij kl h
    exact Prod.ext (hi (congrArg Prod.fst h)) (hi (congrArg Prod.snd h))
  rw [transportEnergy_nil, transportEdges, Finset.sum_image (fun _ _ _ _ h => hp h)]
  simp only [slotEdgeEnergy, missingMultiplier_leaf A e W he heA]
  rw [offdiag_sum (fun i j => min (W (e i)*f (insert (e i) A))
    (W (e j)*f (insert (e j) A)) * (H (insert (e i) A)-H (insert (e j) A))^2)
    (fun i => by simp)]
  rfl

lemma transportEnergy_eq_sum (ps : List (Γ × Γ)) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (f H : Set Γ → ℝ)
      (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ),
    Function.Injective e → (∀ i, e i ∉ A) → SlotsFresh ps (A ∪ Set.range e) →
    (∀ p ∈ ps, W p.1 = W p.2) →
    transportEnergy ps f H A e W =
      (∑ ST ∈ transportEdges ps A e, slotEdgeEnergy ps e W f H ST)/2 := by
  induction ps with
  | nil =>
    intro ι _ _ f H A e W he heA _ _
    exact transportEnergy_leaf_eq_sum f H A e W he heA
  | cons p ps ih =>
    intro ι _ _ f H A e W he heA hps hw
    obtain ⟨hab,ha,hb,ht⟩ := hps
    have hps' : SlotsFresh (p::ps) (A ∪ Set.range e) := ⟨hab,ha,hb,ht⟩
    obtain ⟨hfa,hfb⟩ := slotsFresh_child e A p ps hps'
    have hwt : ∀ p ∈ ps, W p.1 = W p.2 := fun q hq => hw q (List.mem_cons_of_mem _ hq)
    rw [transportEnergy_cons,
      ih f H (insert p.2 A) (appendPoint e p.1) W
        (appendPoint_injective e p.1 he (fun h => ha (Or.inr h)))
        (appendPoint_fresh e A p.1 p.2 heA hab (fun h => ha (Or.inl h))
          (fun h => hb (Or.inr h))) hfa hwt,
      ih f H (insert p.1 A) (appendPoint e p.2) W
        (appendPoint_injective e p.2 he (fun h => hb (Or.inr h)))
        (appendPoint_fresh e A p.2 p.1 heA hab.symm (fun h => hb (Or.inl h))
          (fun h => ha (Or.inr h))) hfb hwt,
      transportEdges, Finset.sum_union (transportEdges_disjoint ps A e p he heA hps'), ← add_div]
    congr 1
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro ST hST
      have hfix := transportEdges_fixed ps (insert p.2 A) (appendPoint e p.1) ST hST
      have hm := hfix (Set.mem_insert _ _)
      simp only [slotEdgeEnergy, missingMultiplier_child_left ps p e W ST.1 hm.1,
        missingMultiplier_child_left ps p e W ST.2 hm.2]
    · apply Finset.sum_congr rfl
      intro ST hST
      have hfix := transportEdges_fixed ps (insert p.1 A) (appendPoint e p.2) ST hST
      have hm := hfix (Set.mem_insert _ _)
      simp only [slotEdgeEnergy, missingMultiplier_child_right ps p e W ST.1 hm.1
          (hw p (List.mem_cons_self ..)),
        missingMultiplier_child_right ps p e W ST.2 hm.2 (hw p (List.mem_cons_self ..))]

omit sectionInstance26 sectionInstance27 in
lemma transportEdges_states [Fintype Γ] [DecidableEq Γ] (ps : List (Γ × Γ)) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Set Γ) (e : ι → Γ)
      (ST : Set Γ × Set Γ), ST ∈ transportEdges ps A e →
      ST.1 ∈ slotVertices ps A e ∧ ST.2 ∈ slotVertices ps A e := by
  induction ps with
  | nil =>
    intro ι _ _ A e ST h
    rw [transportEdges] at h
    obtain ⟨ij,_,rfl⟩ := Finset.mem_image.mp h
    rw [slotVertices]
    exact ⟨Finset.mem_image.mpr ⟨ij.1,Finset.mem_univ _,rfl⟩,
      Finset.mem_image.mpr ⟨ij.2,Finset.mem_univ _,rfl⟩⟩
  | cons p ps ih =>
    intro ι _ _ A e ST h
    rw [transportEdges] at h
    rw [slotVertices]
    rcases Finset.mem_union.mp h with h | h
    · have hh := ih _ _ _ h
      exact ⟨Finset.mem_union_left _ hh.1,Finset.mem_union_left _ hh.2⟩
    · have hh := ih _ _ _ h
      exact ⟨Finset.mem_union_right _ hh.1,Finset.mem_union_right _ hh.2⟩

lemma transportEdges_adjacent (ps : List (Γ × Γ)) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Set Γ) (e : ι → Γ),
    Function.Injective e → (∀ i, e i ∉ A) → SlotsFresh ps (A ∪ Set.range e) →
    ∀ ST ∈ transportEdges ps A e, ExchangeAdjacent ST.1 ST.2 := by
  induction ps with
  | nil =>
    intro ι _ _ A e he heA _ ST h
    rw [transportEdges] at h
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp h
    exact ⟨A,e ij.1,e ij.2,fun h => (Finset.mem_filter.mp hij).2 (he h),
      heA _,heA _,rfl,rfl⟩
  | cons p ps ih =>
    intro ι _ _ A e he heA hps ST h
    obtain ⟨hab,ha,hb,ht⟩ := hps
    have hps' : SlotsFresh (p::ps) (A ∪ Set.range e) := ⟨hab,ha,hb,ht⟩
    obtain ⟨hfa,hfb⟩ := slotsFresh_child e A p ps hps'
    rw [transportEdges] at h
    rcases Finset.mem_union.mp h with h | h
    · exact ih (insert p.2 A) (appendPoint e p.1)
        (appendPoint_injective e p.1 he (fun h => ha (Or.inr h)))
        (appendPoint_fresh e A p.1 p.2 heA hab (fun h => ha (Or.inl h))
          (fun h => hb (Or.inr h))) hfa ST h
    · exact ih (insert p.1 A) (appendPoint e p.2)
        (appendPoint_injective e p.2 he (fun h => hb (Or.inr h)))
        (appendPoint_fresh e A p.2 p.1 heA hab.symm (fun h => hb (Or.inl h))
          (fun h => ha (Or.inr h))) hfb ST h

omit sectionInstance26 sectionInstance27 in
lemma missingMultiplier_nonneg [Fintype Γ] [DecidableEq Γ] {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (e : ι → Γ) (W : Γ → ℝ) (hW : ∀ i, 0 ≤ W i) (S : Set Γ) :
    0 ≤ missingMultiplier ps e W S := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp_all)
  · apply List.sum_nonneg
    intro x hx
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    split_ifs <;> simp_all

lemma transportEnergy_le_graphEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ps : List (Γ × Γ)) (f H : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ)
    (he : Function.Injective e) (heA : ∀ i, e i ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range e)) (hw : ∀ p ∈ ps, W p.1 = W p.2)
    (hf : ∀ S, 0 ≤ f S) (hW : ∀ i, 0 ≤ W i) :
    transportEnergy ps f H A e W ≤ slotGraphEnergy ps f H A e W := by
  rw [transportEnergy_eq_sum ps f H A e W he heA hps hw]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ST hST
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr (transportEdges_states ps A e ST hST),
      transportEdges_adjacent ps A e he heA hps ST hST⟩
  · intro ST _ _
    apply mul_nonneg _ (sq_nonneg _)
    exact le_min (mul_nonneg (missingMultiplier_nonneg ps e W hW ST.1) (hf _))
      (mul_nonneg (missingMultiplier_nonneg ps e W hW ST.2) (hf _))

theorem transport_graph_bound (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ)
    (hf : ∀ S, 0 < f S) (hSig : HasSlotSignature f)
    (hpd : p ≠ d) (hpA : p ∉ A) (hdA : d ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2) :
    (slotTotal ps (fun S => f S*H S) (insert p A) / slotTotal ps f (insert p A) -
      slotTotal ps (fun S => f S*H S) (insert d A) / slotTotal ps f (insert d A))^2 ≤
    rootCoefficient ps f A p d W * slotGraphEnergy ps f H A (rootEmbedding p d) W := by
  apply (transport_root_bound ps f H A p d W hf hSig hpd hpA hdA hps hW hw).trans
  apply mul_le_mul_of_nonneg_left _ (rootCoefficient_pos ps f hf A p d W hps hW).le
  apply transportEnergy_le_graphEnergy ps f H A (rootEmbedding p d) W
    (rootEmbedding_injective p d hpd) _ hps hw (fun S => (hf S).le) (fun i => (hW i).le)
  intro i
  cases i <;> assumption

end TransportGraph

section CoefficientInequalities
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance28 : Fintype ι] [sectionInstance29 : DecidableEq ι]

omit sectionInstance29 in
lemma coeffDeriv_eq_sum_outside [DecidableEq ι] (a : ι → ℝ) (f : Set ι → ℝ) (A : Set ι) :
    coeffDeriv a f A = ∑ i : {i // i ∉ A}, a i.val * f (insert i.val A) := by
  classical
  unfold coeffDeriv
  let g : ι → ℝ := fun i => if i ∈ A then 0 else a i * f (insert i A)
  change (∑ i, g i) = _
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∉ A) g]
  have hz : (∑ i : {i // ¬i ∉ A}, g i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [g, ite_eq_left (not_not.mp i.property)]
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [g, ite_eq_right i.property]

lemma faceHessian_bilin_derivatives (f : Set ι → ℝ) (a b : ι → ℝ) (A : Set ι) :
    (faceHessian f A).toBilin' (fun i => a i.val) (fun i => b i.val) =
      coeffDeriv a (coeffDeriv b f) A := by
  classical
  rw [coeffDeriv_eq_sum_outside]
  simp only [Matrix.toBilin'_apply, faceHessian]
  apply Finset.sum_congr rfl
  intro i _
  unfold coeffDeriv
  let g : ι → ℝ := fun j => @ite ℝ (j ∈ insert i.val A)
      (Classical.propDecidable _) 0 (b j * f (insert j (insert i.val A)))
  change _ = a i.val * ∑ j, g j
  have heq : (∑ j, g j) = ∑ j : {j // j ∉ A}, g j.val := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∉ A) g]
    have hz : (∑ j : {j // ¬j ∉ A}, g j.val) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [g, ite_eq_left (Set.mem_insert_of_mem _ (not_not.mp j.property))]
    rw [hz,add_zero]
  rw [heq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [g]
  by_cases hij : i = j
  · subst j; simp []
  · have hji : j.val ∉ insert i.val A := by
      simp only [Set.mem_insert_iff, not_or]
      exact ⟨fun h => hij (Subtype.ext h.symm),j.property⟩
    rw [ite_eq_right hji]
    simp only [hij, ite_false]
    have hset : A ∪ {i.val,j.val} = insert j.val (insert i.val A) := by
      ext x; simp; tauto
    rw [hset]
    ring

lemma onePositive_pair_bound {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : OnePositive B) (hS : B.IsSymm)
    (u v : V) (hu : 0 < B u u) : B u u * B v v ≤ (B u v)^2 := by
  have h := (le_div_iff₀ hu).mp (onePositive_quadratic_bound B hB hS u v hu)
  rw [hS.eq v u] at h
  nlinarith

lemma onePositive_triple_bound {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : OnePositive B) (hS : B.IsSymm)
    (u e v : V) (he : 0 < B e e) (hue : 0 < B u e) (hve : 0 < B v e)
    (hu : 0 ≤ B u u) (hv : 0 ≤ B v v) :
    B u v * B e e ≤ 2 * B u e * B v e := by
  have h := (le_div_iff₀ he).mp
    (onePositive_quadratic_bound B hB hS e ((B v e) • u + (B u e) • v) he)
  have hvu : B v u = B u v := hS.eq v u
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hvu] at h
  have hn₁ := mul_nonneg (mul_nonneg (sq_nonneg (B v e)) hu) he.le
  have hn₂ := mul_nonneg (mul_nonneg (sq_nonneg (B u e)) hv) he.le
  have hh : (2 * B u e * B v e) * (B u v * B e e) ≤
      (2 * B u e * B v e) * (2 * B u e * B v e) := by nlinarith [h,hn₁,hn₂]
  exact (mul_le_mul_iff_right₀ (mul_pos (mul_pos (by norm_num) hue) hve)).mp hh

lemma coeffDeriv_comm (a b : ι → ℝ) (f : Set ι → ℝ) (A : Set ι) :
    coeffDeriv a (coeffDeriv b f) A = coeffDeriv b (coeffDeriv a f) A := by
  rw [← faceHessian_bilin_derivatives, ← faceHessian_bilin_derivatives]
  exact (matrix_bilin_symm _ (faceHessian_symm f A)).eq _ _

lemma coeffDeriv_pair_twice (p : ι × ι) (f : Set ι → ℝ) (A : Set ι)
    (hp : p.1 ≠ p.2) (ha : p.1 ∉ A) (hb : p.2 ∉ A) :
    coeffDeriv (pairDirection p) (coeffDeriv (pairDirection p) f) A =
      2 * f (insert p.1 (insert p.2 A)) := by
  unfold pairDirection
  rw [coeffDeriv_pair p.1 p.2 hp _ A ha hb]
  simp only [coeffDeriv_slot]
  simp [hp, hp.symm, ha, hb, Set.insert_comm, two_mul]

lemma faceHessian_nonnegative_vectors (f : Set ι → ℝ) (hf : ∀ S, 0 ≤ f S)
    (A : Set ι) (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    0 ≤ (faceHessian f A).toBilin' (fun i => a i.val) (fun i => b i.val) := by
  simp only [Matrix.toBilin'_apply]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg _ (hb _)
  apply mul_nonneg (ha _)
  unfold faceHessian
  split_ifs
  · exact le_rfl
  · exact hf _

theorem coefficient_pair (ps : List (ι × ι)) (f : Set ι → ℝ)
    (hf : ∀ S, 0 < f S) (hsig : HasSlotSignature f)
    (A : Set ι) (p r : ι × ι)
    (hpr : SlotsFresh (p::r::ps) A) :
    4 * slotTotal ps f (insert p.1 (insert p.2 A)) *
      slotTotal ps f (insert r.1 (insert r.2 A)) ≤
      (slotTotal (p::r::ps) f A)^2 := by
  obtain ⟨hp,hpa,hpb,hr,hra,hrb,hps⟩ := hpr
  have hra' : r.1 ∉ A := fun h => hra (Or.inr (Or.inr h))
  have hrb' : r.2 ∉ A := fun h => hrb (Or.inr (Or.inr h))
  let B := (faceHessian (slotTotal ps f) A).toBilin'
  let u : {i // i ∉ A} → ℝ := fun i => pairDirection p i.val
  let v : {i // i ∉ A} → ℝ := fun i => pairDirection r i.val
  have huu : B u u = 2 * slotTotal ps f (insert p.1 (insert p.2 A)) := by
    rw [faceHessian_bilin_derivatives]
    exact coeffDeriv_pair_twice p _ A hp hpa hpb
  have hvv : B v v = 2 * slotTotal ps f (insert r.1 (insert r.2 A)) := by
    rw [faceHessian_bilin_derivatives]
    exact coeffDeriv_pair_twice r _ A hr hra' hrb'
  have huv : B u v = slotTotal (p::r::ps) f A := by
    exact faceHessian_bilin_derivatives _ _ _ _
  have hpos : 0 < B u u := by
    rw [huu]
    apply mul_pos (by norm_num)
    apply slotTotal_pos ps f hf _ (hps.mono _)
    intro x hx
    simp only [Set.mem_insert_iff] at hx ⊢
    tauto
  have h := onePositive_pair_bound B (hsig ps A)
    (matrix_bilin_symm _ (faceHessian_symm _ _)) u v hpos
  rw [huu,hvv,huv] at h
  nlinarith

lemma SlotsFresh.tail {ps : List (ι × ι)} {p : ι × ι} {A : Set ι}
    (h : SlotsFresh (p::ps) A) : SlotsFresh ps A :=
  h.2.2.2.mono (by intro x hx; exact Or.inr (Or.inr hx))

lemma coeffDeriv_pair_repeated (p r : ι × ι) (f : Set ι → ℝ) (A : Set ι)
    (hp : p.1 ≠ p.2) (ha : p.1 ∉ A) (hb : p.2 ∉ A) :
    coeffDeriv (pairDirection r) (coeffDeriv (pairDirection p)
      (coeffDeriv (pairDirection p) f)) A =
    2 * coeffDeriv (pairDirection r) f (insert p.1 (insert p.2 A)) := by
  rw [coeffDeriv_comm (pairDirection r) (pairDirection p)]
  have h : coeffDeriv (pairDirection r) (coeffDeriv (pairDirection p) f) =
      coeffDeriv (pairDirection p) (coeffDeriv (pairDirection r) f) := by
    funext S
    exact coeffDeriv_comm _ _ _ _
  rw [h, coeffDeriv_pair_twice p _ A hp ha hb]

theorem coefficient_triple (ps : List (ι × ι)) (f : Set ι → ℝ)
    (hf : ∀ S, 0 < f S) (hsig : HasSlotSignature f)
    (A : Set ι) (p r t : ι × ι)
    (hprt : SlotsFresh (p::r::t::ps) A) :
    slotTotal (t::ps) f (insert r.1 (insert r.2 A)) *
      slotTotal (p::ps) f (insert t.1 (insert t.2 A)) ≤
    slotTotal (p::r::t::ps) f A *
      slotTotal (r::ps) f (insert t.1 (insert t.2 A)) := by
  have hrt := hprt.tail
  have ht := hrt.tail
  have hr := hrt.1
  have hra := hrt.2.1
  have hrb := hrt.2.2.1
  have htr : SlotsFresh (r::ps) (insert t.1 (insert t.2 A)) := hrt.swap.2.2.2
  let g := slotTotal ps f
  let B := (faceHessian (coeffDeriv (pairDirection t) g) A).toBilin'
  let u : {i // i ∉ A} → ℝ := fun i => pairDirection p i.val
  let e : {i // i ∉ A} → ℝ := fun i => pairDirection r i.val
  let v : {i // i ∉ A} → ℝ := fun i => pairDirection t i.val
  have hee : B e e = 2 * slotTotal (t::ps) f (insert r.1 (insert r.2 A)) := by
    rw [faceHessian_bilin_derivatives]
    exact coeffDeriv_pair_twice r _ A hr hra hrb
  have hue : B u e = slotTotal (p::r::t::ps) f A :=
    faceHessian_bilin_derivatives _ _ _ _
  have hve : B v e = 2 * slotTotal (r::ps) f (insert t.1 (insert t.2 A)) := by
    rw [faceHessian_bilin_derivatives, coeffDeriv_comm (pairDirection t) (pairDirection r)]
    exact coeffDeriv_pair_repeated t r _ A ht.1 ht.2.1 ht.2.2.1
  have huv : B u v = 2 * slotTotal (p::ps) f (insert t.1 (insert t.2 A)) := by
    rw [faceHessian_bilin_derivatives]
    exact coeffDeriv_pair_repeated t p _ A ht.1 ht.2.1 ht.2.2.1
  have hepos : 0 < B e e := by
    rw [hee]
    exact mul_pos (by norm_num) (slotTotal_pos _ f hf _ hrt.2.2.2)
  have huepos : 0 < B u e := by
    rw [hue]
    exact slotTotal_pos _ f hf _ hprt
  have hvepos : 0 < B v e := by
    rw [hve]
    exact mul_pos (by norm_num) (slotTotal_pos _ f hf _ htr)
  have hn : ∀ S, 0 ≤ coeffDeriv (pairDirection t) g S :=
    slotTotal_nonneg (t::ps) f (fun S => (hf S).le)
  have h := onePositive_triple_bound B (hsig (t::ps) A)
    (matrix_bilin_symm _ (faceHessian_symm _ _)) u e v hepos huepos hvepos
    (faceHessian_nonnegative_vectors _ hn A _ _ (slotDirection_nonneg _) (slotDirection_nonneg _))
    (faceHessian_nonnegative_vectors _ hn A _ _ (slotDirection_nonneg _) (slotDirection_nonneg _))
  rw [huv,hee,hue,hve] at h
  nlinarith

theorem scores_have_sink [Nonempty ι] (a : ι → ι → ℝ)
    (hpair : ∀ i j, i ≠ j → a i j * a j i ≤ 1/16)
    (htriple : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → a i j * a j k ≤ a i k) :
    ∃ k, ∀ t, k ≠ t → a k t ≤ 1 := by
  classical
  let out : ι → Finset ι := fun i => Finset.univ.filter (fun j => i ≠ j ∧ 1 < a i j)
  obtain ⟨k,_,hk⟩ := Finset.exists_min_image Finset.univ (fun i => (out i).card)
    Finset.univ_nonempty
  refine ⟨k,?_⟩
  intro t hkt
  by_contra hkt'
  have hat : 1 < a k t := lt_of_not_ge hkt'
  have hnocycle : ∀ i j, i ≠ j → 1 < a i j → ¬ 1 < a j i := by
    intro i j hij ha hb
    have hm : 1 < a i j * a j i := by
      nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)]
    have hp := hpair i j hij
    linarith
  have hsub : out t ⊆ out k := by
    intro j hj
    obtain ⟨htj,haj⟩ := (Finset.mem_filter.mp hj).2
    have hkj : k ≠ j := by
      intro heq
      subst j
      exact hnocycle k t hkt hat haj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hkj,?_⟩
    have hm : 1 < a k t * a t j := by
      nlinarith [mul_pos (sub_pos.mpr hat) (sub_pos.mpr haj)]
    exact hm.trans_le (htriple k t j hkt htj hkj)
  have ht : t ∈ out k := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkt,hat⟩
  have htt : t ∉ out t := by simp [out]
  have hss : out t ⊂ out k := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun heq => htt (heq ▸ ht)⟩
  exact (not_lt_of_ge (hk t (Finset.mem_univ _))) (Finset.card_lt_card hss)

end CoefficientInequalities

section MatroidWeights
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance30 : Fintype ι] [sectionInstance31 : DecidableEq ι]

lemma HasSlotSignature.scale {f : Set ι → ℝ} (hf : HasSlotSignature f)
    (c : ℝ) (hc : 0 < c) : HasSlotSignature (fun S => c * f S) := by
  intro ps A
  have heq : faceHessian (slotTotal ps (fun S => c * f S)) A =
      c • faceHessian (slotTotal ps f) A := by
    ext i j
    simp only [faceHessian, Matrix.smul_apply, smul_eq_mul]
    split_ifs
    · simp
    · exact coeffDerivs_scale _ _ _ _
  rw [heq,map_smul]
  exact onePositive_smul _ (hf ps A) c hc

omit sectionInstance30 sectionInstance31 in
lemma matroidWeight_eq_scaled [Fintype ι] [DecidableEq ι] (M : Matroid ι) (n : ℕ) (hR : M.eRank = (n : ℕ∞))
    (q : ℝ) (hq : 0 < q) (S : Set ι) :
    matroidWeight M n q S = q^n * rankWeight M q S := by
  have hr : (M.eRk S).toNat ≤ n := by
    have h := M.eRk_le_eRank S
    rw [hR] at h
    exact ENat.toNat_le_of_le_natCast h
  unfold matroidWeight rankWeight
  rw [inv_pow, ← div_eq_mul_inv]
  exact (eq_div_iff (ne_of_gt (pow_pos hq _))).mpr (by
    rw [← pow_add, Nat.sub_add_cancel hr])

lemma matroidWeight_signature (M : Matroid ι) (hE : M.E = Set.univ)
    (n : ℕ) (hR : M.eRank = (n : ℕ∞)) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    HasSlotSignature (matroidWeight M n q) := by
  have heq : matroidWeight M n q = fun S => q^n * rankWeight M q S := by
    funext S; exact matroidWeight_eq_scaled M n hR q hq S
  rw [heq]
  exact (rankWeight_hasSlotSignature M hE q hq hq1).scale _ (pow_pos hq _)

end MatroidWeights

section IndexedSlotCoefficients
open scoped BigOperators Classical
variable {ι : Type*} [sectionInstance32 : Fintype ι] [DecidableEq ι]

lemma slotTotal_perm {ps qs : List (ι × ι)} (hperm : ps.Perm qs)
    (f : Set ι → ℝ) : slotTotal ps f = slotTotal qs f := by
  induction hperm with
  | nil => rfl
  | cons p h ih =>
    change coeffDeriv _ (slotTotal _ f) = coeffDeriv _ (slotTotal _ f)
    rw [ih]
  | swap p r ps =>
    funext A
    exact coeffDeriv_comm _ _ _ _
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma slotDefect_perm {ps qs : List (ι × ι)} (hperm : ps.Perm qs)
    (f : Set ι → ℝ) (A : Set ι) (p r : ι × ι) :
    slotDefect ps f A p r = slotDefect qs f A p r := by
  unfold slotDefect
  rw [slotTotal_perm ((hperm.erase p).erase r)]

lemma slotDefect_pair_bound (ps : List (ι × ι)) (f : Set ι → ℝ)
    (hf : ∀ S, 0 < f S) (hsig : HasSlotSignature f)
    (A : Set ι) (hps : SlotsFresh ps A) (p r : ι × ι)
    (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    4 * slotDefect ps f A p r * slotDefect ps f A r p ≤ (slotTotal ps f A)^2 := by
  have hperm := slots_perm_two hp hr hpr
  have h := coefficient_pair ((ps.erase p).erase r) f hf hsig A p r
    ((SlotsFresh.perm hperm A).mp hps)
  rw [← slotTotal_perm hperm f] at h
  unfold slotDefect
  rw [List.erase_comm r p]
  nlinarith

lemma slots_perm_three {ps : List (ι × ι)} {p r t : ι × ι}
    (hp : p ∈ ps) (hr : r ∈ ps) (ht : t ∈ ps)
    (hpr : p ≠ r) (hrt : r ≠ t) (hpt : p ≠ t) :
    ps.Perm (p::r::t::((ps.erase p).erase r).erase t) := by
  have ht' : t ∈ (ps.erase p).erase r :=
    (List.mem_erase_of_ne hrt.symm).mpr ((List.mem_erase_of_ne hpt.symm).mpr ht)
  exact (slots_perm_two hp hr hpr).trans ((List.perm_cons_erase ht').cons r |>.cons p)

lemma slotDefect_triple_bound (ps : List (ι × ι)) (f : Set ι → ℝ)
    (hf : ∀ S, 0 < f S) (hsig : HasSlotSignature f)
    (A : Set ι) (hps : SlotsFresh ps A) (p r t : ι × ι)
    (hp : p ∈ ps) (hr : r ∈ ps) (ht : t ∈ ps)
    (hpr : p ≠ r) (hrt : r ≠ t) (hpt : p ≠ t) :
    slotDefect ps f A p r * slotDefect ps f A r t ≤
      slotTotal ps f A * slotDefect ps f A p t := by
  have hperm := slots_perm_three hp hr ht hpr hrt hpt
  have h := coefficient_triple (((ps.erase p).erase r).erase t) f hf hsig A p r t
    ((SlotsFresh.perm hperm A).mp hps)
  rw [slotDefect_perm hperm, slotDefect_perm hperm, slotDefect_perm hperm,
    slotTotal_perm hperm]
  simpa [slotDefect, hpr, hpr.symm, hrt, hrt.symm, hpt, hpt.symm] using h

lemma coefficient_scores_sink {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (c d : J → J → ℝ) (z v : ℝ) (hz : 0 < z) (hv : 0 < v)
    (hc : ∀ i j, i ≠ j → 0 ≤ c i j) (hd : ∀ i j, i ≠ j → 0 ≤ d i j)
    (hcp : ∀ i j, i ≠ j → 4*c i j*c j i ≤ z^2)
    (hdp : ∀ i j, i ≠ j → 4*d i j*d j i ≤ v^2)
    (hct : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → c i j*c j k ≤ z*c i k)
    (hdt : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → d i j*d j k ≤ v*d i k) :
    ∃ i, ∀ j, i ≠ j → c i j*d j i ≤ z*v := by
  let a : J → J → ℝ := fun i j => (c i j * d j i)/(z*v)
  have hzv : 0 < z*v := mul_pos hz hv
  have hp : ∀ i j, i ≠ j → a i j*a j i ≤ 1/16 := by
    intro i j hij
    dsimp [a]
    rw [div_mul_div_comm]
    apply (div_le_iff₀ (mul_pos hzv hzv)).mpr
    have h := mul_le_mul (hcp i j hij) (hdp j i hij.symm)
      (mul_nonneg (mul_nonneg (by norm_num) (hd j i hij.symm)) (hd i j hij))
      (sq_nonneg z)
    nlinarith
  have ht : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → a i j*a j k ≤ a i k := by
    intro i j k hij hjk hik
    dsimp [a]
    rw [div_mul_div_comm]
    apply (div_le_iff₀ (mul_pos hzv hzv)).mpr
    have h := mul_le_mul (hct i j k hij hjk hik) (hdt k j i hjk.symm hij.symm hik.symm)
      (mul_nonneg (hd k j hjk.symm) (hd j i hij.symm))
      (mul_nonneg hz.le (hc i k hik))
    have heq : c i k*d k i/(z*v)*(z*v*(z*v)) = z*c i k*(v*d k i) := by
      field_simp

    rw [heq]
    nlinarith
  obtain ⟨i,hi⟩ := scores_have_sink a hp ht
  refine ⟨i,fun j hij => ?_⟩
  exact (div_le_iff₀ hzv).mp (hi j hij) |>.trans_eq (one_mul _)

theorem slot_scores_have_sink (ps gs : List (ι × ι)) (f : Set ι → ℝ)
    (hf : ∀ S, 0 < f S) (hsig : HasSlotSignature f)
    (A B : Set ι) (hps : SlotsFresh ps A) (hgs : SlotsFresh gs B)
    (hsub : ∀ p ∈ ps, p ∈ gs) (hne : ps ≠ []) :
    ∃ p ∈ ps, ∀ r ∈ ps, p ≠ r →
      slotDefect ps f A r p * slotDefect gs f B p r ≤
        slotTotal ps f A * slotTotal gs f B := by
  classical
  let J := {p : ι × ι // p ∈ ps}
  have : Nonempty J := by
    obtain ⟨p,hp⟩ := List.exists_mem_of_ne_nil ps hne
    exact ⟨⟨p,hp⟩⟩
  have hne' : ∀ p r : J, p ≠ r → p.val ≠ r.val := fun p r h he => h (Subtype.ext he)
  obtain ⟨p,hp⟩ := coefficient_scores_sink
    (fun p r : J => slotDefect ps f A r.val p.val)
    (fun p r : J => slotDefect gs f B r.val p.val)
    (slotTotal ps f A) (slotTotal gs f B)
    (slotTotal_pos ps f hf A hps) (slotTotal_pos gs f hf B hgs)
    (fun p r h => (slotDefect_pos ps f hf A hps r p r.property p.property (hne' r p h.symm)).le)
    (fun p r h => (slotDefect_pos gs f hf B hgs r p (hsub r r.property)
      (hsub p p.property) (hne' r p h.symm)).le)
    (fun p r h => slotDefect_pair_bound ps f hf hsig A hps r p r.property p.property (hne' r p h.symm))
    (fun p r h => slotDefect_pair_bound gs f hf hsig B hgs r p (hsub r r.property)
      (hsub p p.property) (hne' r p h.symm))
    (fun p r t h₁ h₂ h₃ => by
      simpa only [mul_comm] using slotDefect_triple_bound ps f hf hsig A hps t r p
        t.property r.property p.property (hne' t r h₂.symm) (hne' r p h₁.symm) (hne' t p h₃.symm))
    (fun p r t h₁ h₂ h₃ => by
      simpa only [mul_comm] using slotDefect_triple_bound gs f hf hsig B hgs t r p
        (hsub t t.property) (hsub r r.property) (hsub p p.property)
        (hne' t r h₂.symm) (hne' r p h₁.symm) (hne' t p h₃.symm))
  refine ⟨p.val,p.property,?_⟩
  intro r hr hpr
  exact hp ⟨r,hr⟩ (fun h => hpr (congrArg Subtype.val h))

end IndexedSlotCoefficients

section VarianceTree
open scoped BigOperators Classical
variable {ι : Type*} [sectionInstance34 : Fintype ι] [sectionInstance35 : DecidableEq ι]

lemma slotVariance_nil (f H : Set ι → ℝ) (A : Set ι) (_ : f A ≠ 0) :
    slotVariance [] f H A = 0 := by
  unfold slotVariance
  simp only [slotTotal_nil]
  field_simp
  ; ring

lemma slotVariance_perm {ps qs : List (ι × ι)} (h : ps.Perm qs)
    (f H : Set ι → ℝ) (A : Set ι) :
    slotVariance ps f H A = slotVariance qs f H A := by
  unfold slotVariance
  rw [slotTotal_perm h, slotTotal_perm h, slotTotal_perm h]

lemma variance_split_algebra (a b x y u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    x+y-(u+v)^2/(a+b) =
      (x-u^2/a) + (y-v^2/b) + a*b/(a+b)*(u/a-v/b)^2 := by
  have hab : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  field_simp
  ; ring

lemma slotVariance_split (ps : List (ι × ι)) (f H : Set ι → ℝ)
    (hf : ∀ S, 0 < f S) (A : Set ι) (p : ι × ι) (hps : SlotsFresh (p::ps) A) :
    slotVariance (p::ps) f H A =
      slotVariance ps f H (insert p.1 A) + slotVariance ps f H (insert p.2 A) +
      (slotTotal ps f (insert p.1 A)*slotTotal ps f (insert p.2 A) / slotTotal (p::ps) f A)*
        (slotTotal ps (fun S => f S*H S) (insert p.1 A)/slotTotal ps f (insert p.1 A) -
          slotTotal ps (fun S => f S*H S) (insert p.2 A)/slotTotal ps f (insert p.2 A))^2 := by
  unfold slotVariance
  simp only [slotTotal_cons p ps _ A hps.1 hps.2.1 hps.2.2.1]
  apply variance_split_algebra
  · exact slotTotal_pos ps f hf _ (hps.2.2.2.mono (by intro x hx; simp only [Set.mem_insert_iff] at hx ⊢; tauto))
  · exact slotTotal_pos ps f hf _ (hps.2.2.2.mono (Set.subset_insert _ _))

omit sectionInstance34 sectionInstance35 in
lemma slotPunctures_length [Fintype ι] [DecidableEq ι] (ps : List (ι × ι)) : (slotPunctures ps).length = ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [slotPunctures, List.length_cons,List.length_map,ih]

lemma list_sum_map_le_const {β : Type*} (l : List β) (g : β → ℝ) (C : ℝ)
    (h : ∀ x ∈ l, g x ≤ C) : (l.map g).sum ≤ (l.length : ℝ)*C := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    have hh := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self)
    linarith

theorem transport_node_variance (ps : List (ι × ι)) (f H : Set ι → ℝ)
    (A : Set ι) (p d : ι) (W : ι → ℝ)
    (hf : ∀ S, 0 < f S) (hSig : HasSlotSignature f)
    (hpd : p ≠ d) (hpA : p ∉ A) (hdA : d ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2)
    (hWp : W p = 1) (hWd : W d = 1)
    (hsink : ∀ x ∈ slotPunctures ps,
      slotTotal x.2 f (insert p (insert d A))/W x.1.1 ≤
        4*(slotTotal ps f (insert p A)+slotTotal ps f (insert d A))) :
    let sp := slotTotal ps f (insert p A)
    let sd := slotTotal ps f (insert d A)
    sp*sd/(sp+sd) *
      (slotTotal ps (fun S => f S*H S) (insert p A)/sp -
        slotTotal ps (fun S => f S*H S) (insert d A)/sd)^2 ≤
      (1+8*(ps.length : ℝ))*slotGraphEnergy ps f H A (rootEmbedding p d) W := by
  let sp := slotTotal ps f (insert p A)
  let sd := slotTotal ps f (insert d A)
  have hp : 0 < sp := slotTotal_pos ps f hf _ (hps.mono (by
    intro x hx; rcases hx with rfl | hx
    · exact Or.inr ⟨false,rfl⟩
    · exact Or.inl hx))
  have hd : 0 < sd := slotTotal_pos ps f hf _ (hps.mono (by
    intro x hx; rcases hx with rfl | hx
    · exact Or.inr ⟨true,rfl⟩
    · exact Or.inl hx))
  have hpd' : 0 < sp*sd/(sp+sd) := div_pos (mul_pos hp hd) (add_pos hp hd)
  have hsum := list_sum_map_le_const (slotPunctures ps)
    (fun x => slotTotal x.2 f (insert p (insert d A))/W x.1.1) (4*(sp+sd)) hsink
  rw [slotPunctures_length] at hsum
  have hcoef : sp*sd/(sp+sd)*rootCoefficient ps f A p d W ≤ 1+8*(ps.length : ℝ) := by
    unfold rootCoefficient
    change sp*sd/(sp+sd)*(1/(sp*W p)+1/(sd*W d)+2/(sp*sd)*_) ≤ _
    rw [hWp,hWd,mul_one,mul_one]
    have heq (s : ℝ) : sp*sd/(sp+sd)*(1/sp+1/sd+2/(sp*sd)*s) = 1+2/(sp+sd)*s := by
      field_simp
      ; ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2/(sp+sd) by positivity)
    have heq' : 2/(sp+sd)*((ps.length : ℝ)*(4*(sp+sd))) = 8*(ps.length : ℝ) := by
      field_simp
      ; ring
    rw [heq'] at hh
    linarith
  have hE : 0 ≤ slotGraphEnergy ps f H A (rootEmbedding p d) W := by
    unfold slotGraphEnergy
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro ST hST
    unfold slotEdgeEnergy
    apply mul_nonneg _ (sq_nonneg _)
    apply le_min
    · exact mul_nonneg (missingMultiplier_nonneg ps _ W (fun i => (hW i).le) _ ) (hf _).le
    · exact mul_nonneg (missingMultiplier_nonneg ps _ W (fun i => (hW i).le) _ ) (hf _).le
  have ht := mul_le_mul_of_nonneg_left
    (transport_graph_bound ps f H A p d W hf hSig hpd hpA hdA hps hW hw) hpd'.le
  dsimp only
  exact ht.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcoef hE)

end VarianceTree

section StateGeometry
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance36 : Fintype Γ] [sectionInstance37 : DecidableEq Γ]

lemma SlotsFresh.nodup {ps : List (Γ × Γ)} {A : Set Γ} (h : SlotsFresh ps A) : ps.Nodup := by
  induction ps generalizing A with
  | nil => exact List.nodup_nil
  | cons p ps ih =>
    exact List.nodup_cons.mpr ⟨fun hp => (h.pair_ne_of_mem hp) rfl,ih h.2.2.2⟩

omit sectionInstance36 sectionInstance37 in
lemma slotVertices_fixed [Fintype Γ] [DecidableEq Γ] (ps : List (Γ × Γ)) :
    ∀ {J : Type*} [Fintype J] (A : Set Γ) (e : J → Γ) (S : Set Γ),
      S ∈ slotVertices ps A e → A ⊆ S := by
  induction ps with
  | nil =>
    intro J _ A e S h
    rw [slotVertices] at h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    exact Set.subset_insert _ _
  | cons p ps ih =>
    intro J _ A e S h
    rw [slotVertices] at h
    rcases Finset.mem_union.mp h with h | h
    · exact (Set.subset_insert _ _).trans (ih _ _ _ h)
    · exact (Set.subset_insert _ _).trans (ih _ _ _ h)

lemma slotVertices_classify (ps : List (Γ × Γ)) :
    ∀ {J : Type*} [Fintype J] [DecidableEq J] (A : Set Γ) (e : J → Γ),
      Function.Injective e → (∀ j, e j ∉ A) → SlotsFresh ps (A ∪ Set.range e) →
      ∀ S ∈ slotVertices ps A e,
      (∃ j, (∀ i, e i ∈ S ↔ i = j) ∧ ∀ p ∈ ps, PairSingle p S) ∨
      (∃ p ∈ ps, (∀ i, e i ∉ S) ∧ PairFull p S ∧
        ∀ r ∈ ps, r ≠ p → PairSingle r S) := by
  induction ps with
  | nil =>
    intro J _ _ A e he heA _ S h
    rw [slotVertices] at h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    left
    refine ⟨j,fun i => ?_,by simp⟩
    simp only [Set.mem_insert_iff, heA i, or_false]
    exact he.eq_iff
  | cons p ps ih =>
    intro J _ _ A e he heA hps S h
    have hab := hps.1
    have ha := hps.2.1
    have hb := hps.2.2.1
    obtain ⟨hfa,hfb⟩ := slotsFresh_child e A p ps hps
    have branch (a b : Γ) (hab : a ≠ b) (haA : a ∉ A) (hbE : b ∉ Set.range e)
        (haE : a ∉ Set.range e)
        (hf : SlotsFresh ps (insert b A ∪ Set.range (appendPoint e a)))
        (hm : S ∈ slotVertices ps (insert b A) (appendPoint e a)) :
        (∃ j, (∀ i, e i ∈ S ↔ i = j) ∧
          PairSingle (a,b) S ∧ ∀ r ∈ ps, PairSingle r S) ∨
        ((∀ i, e i ∉ S) ∧ PairFull (a,b) S ∧ ∀ r ∈ ps, PairSingle r S) ∨
        (∃ r ∈ ps, (∀ i, e i ∉ S) ∧ PairFull r S ∧ PairSingle (a,b) S ∧
          ∀ t ∈ ps, t ≠ r → PairSingle t S) := by
      have hbS : b ∈ S := slotVertices_fixed ps _ _ S hm (Set.mem_insert _ _)
      have hh := ih (insert b A) (appendPoint e a)
        (appendPoint_injective e a he haE)
        (appendPoint_fresh e A a b heA hab haA hbE) hf S hm
      rcases hh with ⟨j,hj,hr⟩ | ⟨r,hr,he',hfull,hrest⟩
      · cases j with
        | none =>
          right; left
          refine ⟨fun i hi => ?_,⟨?_,hbS⟩,hr⟩
          · exact Option.some_ne_none i ((hj (some i)).mp hi)
          · exact (hj none).mpr rfl
        | some j =>
          left
          refine ⟨j,fun i => ?_,Or.inr ⟨hbS,?_⟩,hr⟩
          · simpa only [appendPoint, Option.some.injEq] using hj (some i)
          · intro haS; exact Option.some_ne_none j (((hj none).mp haS).symm)
      · right; right
        exact ⟨r,hr,fun i => he' (some i),hfull,Or.inr ⟨hbS,he' none⟩,hrest⟩
    rw [slotVertices] at h
    rcases Finset.mem_union.mp h with h | h
    · have hh := branch p.1 p.2 hab (fun h => ha (Or.inl h))
        (fun h => hb (Or.inr h)) (fun h => ha (Or.inr h)) hfa h
      rcases hh with ⟨j,hj,hp,hr⟩ | ⟨hi,hp,hr⟩ | ⟨r,hr,hi,hfull,hp,hrest⟩
      · left; exact ⟨j,hj,fun r hr' => (List.mem_cons.mp hr').elim (fun heq => heq ▸ hp) (hr r)⟩
      · right
        refine ⟨p,List.mem_cons_self,hi,hp,?_⟩
        intro r hr' hne
        exact hr r ((List.mem_cons.mp hr').resolve_left hne)
      · right
        refine ⟨r,List.mem_cons_of_mem _ hr,hi,hfull,?_⟩
        intro t ht hne
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hp
        · exact hrest t ht hne
    · have hh := branch p.2 p.1 hab.symm (fun h => hb (Or.inl h))
        (fun h => ha (Or.inr h)) (fun h => hb (Or.inr h)) hfb h
      have hsingle : PairSingle (p.2,p.1) S → PairSingle p S := fun h => h.elim Or.inr Or.inl
      have hfull : PairFull (p.2,p.1) S → PairFull p S := And.symm
      rcases hh with ⟨j,hj,hp,hr⟩ | ⟨hi,hp,hr⟩ | ⟨r,hr,hi,hfr,hp,hrest⟩
      · left; exact ⟨j,hj,fun r hr' => (List.mem_cons.mp hr').elim (fun heq => heq ▸ hsingle hp) (hr r)⟩
      · right
        refine ⟨p,List.mem_cons_self,hi,hfull hp,?_⟩
        intro r hr' hne
        exact hr r ((List.mem_cons.mp hr').resolve_left hne)
      · right
        refine ⟨r,List.mem_cons_of_mem _ hr,hi,hfr,?_⟩
        intro t ht hne
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hsingle hp
        · exact hrest t ht hne

end StateGeometry

section RestrictedEnergy
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance38 : Fintype Γ] [sectionInstance39 : DecidableEq Γ]

omit sectionInstance38 sectionInstance39 in
lemma Respects.parent [Fintype Γ] [DecidableEq Γ] {A B S : Set Γ} {a b : Γ}
    (h : Respects (insert a A) (insert b B) S) : Respects A B S :=
  ⟨(Set.subset_insert _ _).trans h.1, h.2.mono_left (Set.subset_insert _ _)⟩

omit sectionInstance38 sectionInstance39 in
lemma Respects.child_disjoint [Fintype Γ] [DecidableEq Γ] {A B S : Set Γ} {a b : Γ}
    (h : Respects (insert a A) (insert b B) S) :
    ¬ Respects (insert b A) (insert a B) S := by
  intro h'
  exact Set.disjoint_left.mp h'.2 (Set.mem_insert _ _) (h.1 (Set.mem_insert _ _))

omit sectionInstance38 sectionInstance39 in
lemma restrictedEnergy_nonneg [Fintype Γ] [DecidableEq Γ] (E : Finset (Set Γ × Set Γ))
    (c : (Set Γ × Set Γ) → ℝ) (H : Set Γ → ℝ) (A B : Set Γ)
    (hc : ∀ ST ∈ E, 0 ≤ c ST) : 0 ≤ restrictedEnergy E c H A B := by
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro ST hST
  split_ifs
  · exact mul_nonneg (hc ST hST) (sq_nonneg _)
  · rfl

lemma restrictedEnergy_children (E : Finset (Set Γ × Set Γ))
    (c : (Set Γ × Set Γ) → ℝ) (H : Set Γ → ℝ) (A B : Set Γ) (a b : Γ)
    (hc : ∀ ST ∈ E, 0 ≤ c ST) :
    restrictedEnergy E c H (insert a A) (insert b B) +
      restrictedEnergy E c H (insert b A) (insert a B) ≤ restrictedEnergy E c H A B := by
  unfold restrictedEnergy
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro ST hST
  have hw : 0 ≤ c ST*(H ST.1-H ST.2)^2 := mul_nonneg (hc ST hST) (sq_nonneg _)
  by_cases h₁ : EdgeRespects (insert a A) (insert b B) ST
  · have hp : EdgeRespects A B ST := ⟨h₁.1.parent,h₁.2.parent⟩
    have hn : ¬ EdgeRespects (insert b A) (insert a B) ST := fun h₂ => h₁.1.child_disjoint h₂.1
    simp only [ite_eq_left h₁,ite_eq_right hn,ite_eq_left hp,add_zero,le_refl]
  · by_cases h₂ : EdgeRespects (insert b A) (insert a B) ST
    · have hp : EdgeRespects A B ST := ⟨h₂.1.parent,h₂.2.parent⟩
      simp only [ite_eq_right h₁,ite_eq_left h₂,ite_eq_left hp,zero_add,le_refl]
    · simp only [ite_eq_right h₁,ite_eq_right h₂,zero_add]
      split_ifs <;> positivity

theorem adaptive_variance_bound (f H : Set Γ → ℝ) (hf : ∀ S, 0 < f S)
    (E : Finset (Set Γ × Set Γ)) (c : (Set Γ × Set Γ) → ℝ)
    (hc : ∀ ST ∈ E, 0 ≤ c ST) (C : ℝ) (hC : 0 ≤ C)
    (P : List (Γ × Γ) → Set Γ → Set Γ → Prop)
    (hchoose : ∀ ps A B, P ps A B → ps ≠ [] →
      ∃ p qs, ps.Perm (p::qs) ∧ SlotsFresh (p::qs) A ∧
        P qs (insert p.1 A) (insert p.2 B) ∧ P qs (insert p.2 A) (insert p.1 B) ∧
        slotVariance (p::qs) f H A - slotVariance qs f H (insert p.1 A) -
          slotVariance qs f H (insert p.2 A) ≤ C*restrictedEnergy E c H A B) :
    ∀ ps A B, P ps A B → slotVariance ps f H A ≤
      (ps.length : ℝ)*C*restrictedEnergy E c H A B := by
  intro ps
  induction hn : ps.length using Nat.strong_induction_on generalizing ps with
  | h n ih =>
    intro A B hP
    by_cases hnil : ps = []
    · subst ps
      have hn0 : n = 0 := hn.symm
      subst n
      simp only [slotVariance_nil f H A (ne_of_gt (hf A)),List.length_nil,Nat.cast_zero,zero_mul,le_refl]
    · obtain ⟨p,qs,hperm,hfresh,hP₁,hP₂,hnode⟩ := hchoose ps A B hP hnil
      have hpq : ps.length = qs.length+1 := by simpa using hperm.length_eq
      have hq : qs.length < n := by omega
      have ha := ih qs.length hq qs rfl (insert p.1 A) (insert p.2 B) hP₁
      have hb := ih qs.length hq qs rfl (insert p.2 A) (insert p.1 B) hP₂
      have he := restrictedEnergy_children E c H A B p.1 p.2 hc
      have hmul := mul_le_mul_of_nonneg_left he (mul_nonneg (Nat.cast_nonneg qs.length) hC)
      rw [← hn, slotVariance_perm hperm f H A,hpq,Nat.cast_add,Nat.cast_one]
      nlinarith

end RestrictedEnergy

section ChainIdentification
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance40 : Fintype Γ] [sectionInstance41 : DecidableEq Γ]

omit sectionInstance40 sectionInstance41 in
lemma slotVertices_excluded [Fintype Γ] [DecidableEq Γ] (ps : List (Γ × Γ)) :
    ∀ {J : Type*} [Fintype J] (A B : Set Γ) (e : J → Γ),
      Disjoint A B → (∀ j, e j ∉ B) → (∀ p ∈ ps, p.1 ∉ B ∧ p.2 ∉ B) →
      ∀ S ∈ slotVertices ps A e, Disjoint B S := by
  induction ps with
  | nil =>
    intro J _ A B e hAB he _ S hS
    rw [slotVertices] at hS
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hS
    exact Set.disjoint_insert_right.mpr ⟨he j,hAB.symm⟩
  | cons p ps ih =>
    intro J _ A B e hAB he hp S hS
    obtain ⟨hp₁,hp₂⟩ := hp p List.mem_cons_self
    have hrest := fun r hr => hp r (List.mem_cons_of_mem _ hr)
    rw [slotVertices] at hS
    rcases Finset.mem_union.mp hS with hS | hS
    · apply ih (insert p.2 A) B (appendPoint e p.1)
        (Set.disjoint_insert_left.mpr ⟨hp₂,hAB⟩) _ hrest S hS
      intro j; cases j <;> first | exact hp₁ | exact he _
    · apply ih (insert p.1 A) B (appendPoint e p.2)
        (Set.disjoint_insert_left.mpr ⟨hp₁,hAB⟩) _ hrest S hS
      intro j; cases j <;> first | exact hp₂ | exact he _

omit sectionInstance40 sectionInstance41 in
lemma FixedOutside.single [Fintype Γ] [DecidableEq Γ] {gs ps : List (Γ × Γ)} {A B S : Set Γ}
    (h : FixedOutside gs ps A B) (hS : Respects A B S)
    (r : Γ × Γ) (hr : r ∈ gs) (hn : r ∉ ps) : PairSingle r S := by
  rcases h r hr hn with h | h
  · exact Or.inl ⟨hS.1 h.1,fun hx => Set.disjoint_left.mp hS.2 h.2 hx⟩
  · exact Or.inr ⟨hS.1 h.1,fun hx => Set.disjoint_left.mp hS.2 h.2 hx⟩

lemma list_sum_single {β : Type*} [DecidableEq β] (ps : List β) (hn : ps.Nodup)
    (p : β) (hp : p ∈ ps) (g : β → ℝ) (hg : ∀ r ∈ ps, r ≠ p → g r = 0) :
    (ps.map g).sum = g p := by
  rw [← List.sum_toFinset _ hn]
  exact Finset.sum_eq_single p (fun b hb hbp => hg b (List.mem_toFinset.mp hb) hbp)
    (fun hn => False.elim (hn (List.mem_toFinset.mpr hp)))

lemma missingMultiplier_old {J : Type*} [Fintype J] [DecidableEq J]
    (ps : List (Γ × Γ)) (e : J → Γ) (W : Γ → ℝ) (S : Set Γ) (j : J)
    (hj : ∀ i, e i ∈ S ↔ i = j) (hp : ∀ p ∈ ps, PairSingle p S) :
    missingMultiplier ps e W S = W (e j) := by
  unfold missingMultiplier
  have hz : (ps.map (fun p => if p.1 ∈ S ∧ p.2 ∈ S then W p.1 else 0)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hx
    exact ite_eq_right (hp p hp').not_full
  rw [hz,add_zero]
  simp only [hj]
  simp

lemma missingMultiplier_new {J : Type*} [Fintype J]
    (ps : List (Γ × Γ)) (hn : ps.Nodup) (e : J → Γ) (W : Γ → ℝ) (S : Set Γ)
    (p : Γ × Γ) (hp : p ∈ ps) (he : ∀ i, e i ∉ S) (hf : PairFull p S)
    (hr : ∀ r ∈ ps, r ≠ p → PairSingle r S) :
    missingMultiplier ps e W S = W p.1 := by
  unfold missingMultiplier
  simp only [he,ite_false,Finset.sum_const_zero,zero_add]
  have hh := list_sum_single ps hn p hp
    (fun r => if r.1 ∈ S ∧ r.2 ∈ S then W r.1 else 0)
    (fun r hr' hne => ite_eq_right (hr r hr' hne).not_full)
  exact hh.trans (ite_eq_left hf)

omit sectionInstance40 in
lemma pairMultiplier_pos [Fintype Γ] (ps : List (Γ × Γ)) (w : (Γ × Γ) → ℝ)
    (hw : ∀ p, 0 < w p) (x : Γ) : 0 < pairMultiplier ps w x := by
  unfold pairMultiplier
  split_ifs <;> first | exact hw _ | norm_num

lemma pairMultiplier_on {ps : List (Γ × Γ)} {A : Set Γ} (hps : SlotsFresh ps A)
    (w : (Γ × Γ) → ℝ) (p : Γ × Γ) (hp : p ∈ ps) (x : Γ)
    (hx : x = p.1 ∨ x = p.2) : pairMultiplier ps w x = w p := by
  have he : ∃ p ∈ ps, x = p.1 ∨ x = p.2 := ⟨p,hp,hx⟩
  unfold pairMultiplier
  rw [dite_eq_left he]
  rw [hps.pair_contains_unique he.choose_spec.1 hp he.choose_spec.2 hx]

lemma pairMultiplier_fresh {ps : List (Γ × Γ)} {A : Set Γ} (hps : SlotsFresh ps A)
    (w : (Γ × Γ) → ℝ) (x : Γ) (hx : x ∈ A) : pairMultiplier ps w x = 1 := by
  unfold pairMultiplier
  rw [dite_eq_right]
  rintro ⟨p,hp,h⟩
  rcases h with rfl | rfl
  · exact (hps.elements_fresh p hp).1 hx
  · exact (hps.elements_fresh p hp).2 hx

lemma variance_vertex_identification (gs ps : List (Γ × Γ)) (A B : Set Γ) (p : Γ × Γ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hsub : ∀ r ∈ p::ps, r ∈ gs) (hAB : Disjoint A B)
    (hfresh : SlotsFresh (p::ps) (A ∪ B)) (hout : FixedOutside gs (p::ps) A B)
    (S : Set Γ) (hS : S ∈ slotVertices ps A (rootEmbedding p.1 p.2)) :
    ChainState gs S ∧ Respects A B S ∧
      missingMultiplier ps (rootEmbedding p.1 p.2) (pairMultiplier ps (w p)) S =
        chainMultiplier gs w S := by
  have hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p.1 p.2)) :=
    hfresh.2.2.2.mono (by
      intro x hx
      rcases hx with hx | ⟨i,rfl⟩
      · exact Or.inr (Or.inr (Or.inl hx))
      · cases i <;> simp [rootEmbedding])
  have heA : ∀ j, rootEmbedding p.1 p.2 j ∉ A := by
    intro j; cases j <;> first | exact fun h => hfresh.2.1 (Or.inl h) | exact fun h => hfresh.2.2.1 (Or.inl h)
  have heB : ∀ j, rootEmbedding p.1 p.2 j ∉ B := by
    intro j; cases j <;> first | exact fun h => hfresh.2.1 (Or.inr h) | exact fun h => hfresh.2.2.1 (Or.inr h)
  have hSB : Disjoint B S := slotVertices_excluded ps A B _ hAB heB
    (fun r hr => let hh := hfresh.elements_fresh r (List.mem_cons_of_mem _ hr)
                ⟨fun h => hh.1 (Or.inr h),fun h => hh.2 (Or.inr h)⟩) S hS
  have hrespect : Respects A B S := ⟨slotVertices_fixed ps A _ S hS,hSB⟩
  have hclass := slotVertices_classify ps A _ (rootEmbedding_injective _ _ hfresh.1) heA hps S hS
  rcases hclass with ⟨j,hj,hrest⟩ | ⟨r,hr,he,hfull,hrest⟩
  · have hp : PairSingle p S := by
      cases j
      · exact Or.inl ⟨(hj false).mpr rfl,fun h => Bool.noConfusion ((hj true).mp h)⟩
      · exact Or.inr ⟨(hj true).mpr rfl,fun h => Bool.noConfusion ((hj false).mp h)⟩
    have hplain : PlainState gs S := by
      intro r hr
      by_cases hm : r ∈ p::ps
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact hp
        · exact hrest r hm
      · exact hout.single hrespect r hr hm
    refine ⟨Or.inl hplain,hrespect,?_⟩
    rw [chainMultiplier_plain gs w S hplain,missingMultiplier_old ps _ _ S j hj hrest]
    exact pairMultiplier_fresh hps _ _ (Or.inr ⟨j,rfl⟩)
  · have hdef : DefectState gs p r S := by
      refine ⟨hsub p List.mem_cons_self,hsub r (List.mem_cons_of_mem _ hr),
        hfresh.pair_ne_of_mem hr,⟨he false,he true⟩,hfull,?_⟩
      intro t ht htp htr
      by_cases hm : t ∈ p::ps
      · exact hrest t ((List.mem_cons.mp hm).resolve_left htp) htr
      · exact hout.single hrespect t ht hm
    refine ⟨Or.inr ⟨p,r,hdef⟩,hrespect,?_⟩
    rw [chainMultiplier_defect gs w S hdef,
      missingMultiplier_new ps hps.nodup _ _ S r hr he hfull hrest]
    exact pairMultiplier_on hps _ r hr r.1 (Or.inl rfl)

lemma variance_energy_identification (gs ps : List (Γ × Γ)) (A B : Set Γ) (p : Γ × Γ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ)
    (hw : ∀ p r, 0 < w p r) (hf : ∀ S, 0 < f S)
    (hsub : ∀ r ∈ p::ps, r ∈ gs) (hAB : Disjoint A B)
    (hfresh : SlotsFresh (p::ps) (A ∪ B)) (hout : FixedOutside gs (p::ps) A B) :
    slotGraphEnergy ps f H A (rootEmbedding p.1 p.2) (pairMultiplier ps (w p)) ≤
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H A B := by
  have hvertex := variance_vertex_identification gs ps A B p w hsub hAB hfresh hout
  unfold slotGraphEnergy restrictedEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  let D := slotGraphEdges ps A (rootEmbedding p.1 p.2)
  have hE : D ⊆ chainEdges gs := by
    intro ST hST
    obtain ⟨hprod,hadj⟩ := Finset.mem_filter.mp hST
    obtain ⟨hs,ht⟩ := Finset.mem_product.mp hprod
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hvertex ST.1 hs).1,(hvertex ST.2 ht).1,hadj⟩
  calc
    _ = ∑ ST ∈ D, if EdgeRespects A B ST then
        chainConductance gs w f ST*(H ST.1-H ST.2)^2 else 0 := by
      apply Finset.sum_congr rfl
      intro ST hST
      obtain ⟨hs,ht⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hST).1
      have hs' := hvertex ST.1 hs
      have ht' := hvertex ST.2 ht
      rw [ite_eq_left (show EdgeRespects A B ST from ⟨hs'.2.1,ht'.2.1⟩)]
      simp only [slotEdgeEnergy,hs'.2.2,ht'.2.2,chainConductance]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hE
      intro ST hST _
      split_ifs
      · exact mul_nonneg (le_min
          (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
          (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)) (sq_nonneg _)
      · rfl

end ChainIdentification

section TransversalVariance
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance42 : Fintype Γ] [sectionInstance43 : DecidableEq Γ]

omit sectionInstance42 sectionInstance43 in
lemma slotPunctures_perm [Fintype Γ] [DecidableEq Γ] (ps : List (Γ × Γ)) (x : (Γ × Γ) × List (Γ × Γ))
    (hx : x ∈ slotPunctures ps) : ps.Perm (x.1::x.2) := by
  induction ps generalizing x with
  | nil => simp [slotPunctures] at hx
  | cons p ps ih =>
    rw [slotPunctures,List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact List.Perm.refl _
    · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact ((ih y hy).cons p).trans (List.Perm.swap _ _ _)

lemma slotDefect_puncture (ps : List (Γ × Γ)) (p : Γ × Γ) (A : Set Γ)
    (f : Set Γ → ℝ) (hps : SlotsFresh (p::ps) A)
    (x : (Γ × Γ) × List (Γ × Γ)) (hx : x ∈ slotPunctures ps) :
    slotDefect (p::ps) f A x.1 p = slotTotal x.2 f (insert p.1 (insert p.2 A)) := by
  have hperm := slotPunctures_perm ps x hx
  have hm : x.1 ∈ ps := hperm.mem_iff.mpr List.mem_cons_self
  rw [slotDefect_perm (hperm.cons p)]
  simp [slotDefect,hps.pair_ne_of_mem hm]

lemma VarianceNode.perm {gs ps qs : List (Γ × Γ)} {A B : Set Γ}
    (h : VarianceNode gs ps A B) (hp : ps.Perm qs) : VarianceNode gs qs A B := by
  refine ⟨h.1,(SlotsFresh.perm hp _).mp h.2.1,fun r hr => h.2.2.1 r (hp.mem_iff.mpr hr),?_⟩
  intro r hr hn
  exact h.2.2.2 r hr (fun hm => hn (hp.mem_iff.mp hm))

lemma VarianceNode.children {gs ps : List (Γ × Γ)} {A B : Set Γ} {p : Γ × Γ}
    (h : VarianceNode gs (p::ps) A B) :
    VarianceNode gs ps (insert p.1 A) (insert p.2 B) ∧
      VarianceNode gs ps (insert p.2 A) (insert p.1 B) := by
  obtain ⟨hAB,hfresh,hsub,hout⟩ := h
  have hab := hfresh.1
  have haA : p.1 ∉ A := fun hx => hfresh.2.1 (Or.inl hx)
  have haB : p.1 ∉ B := fun hx => hfresh.2.1 (Or.inr hx)
  have hbA : p.2 ∉ A := fun hx => hfresh.2.2.1 (Or.inl hx)
  have hbB : p.2 ∉ B := fun hx => hfresh.2.2.1 (Or.inr hx)
  have ho (a b : Γ) (hp : (a,b) = p ∨ (a,b) = (p.2,p.1)) :
      FixedOutside gs ps (insert a A) (insert b B) := by
    intro r hr hn
    by_cases hrp : r = p
    · subst r
      rcases hp with hp | hp
      · have h₁ := congrArg Prod.fst hp
        have h₂ := congrArg Prod.snd hp
        exact Or.inl ⟨Or.inl h₁.symm,Or.inl h₂.symm⟩
      · have h₁ := congrArg Prod.fst hp
        have h₂ := congrArg Prod.snd hp
        exact Or.inr ⟨Or.inl h₁.symm,Or.inl h₂.symm⟩
    · rcases hout r hr (by simp [hrp,hn]) with hh | hh
      · exact Or.inl ⟨Or.inr hh.1,Or.inr hh.2⟩
      · exact Or.inr ⟨Or.inr hh.1,Or.inr hh.2⟩
  constructor
  · refine ⟨?_,hfresh.2.2.2.mono ?_,fun r hr => hsub r (List.mem_cons_of_mem _ hr),ho _ _ (Or.inl rfl)⟩
    · simp only [Set.disjoint_insert_left,Set.mem_insert_iff,not_or,Set.disjoint_insert_right]
      tauto
    · intro x hx
      simp only [Set.mem_union,Set.mem_insert_iff] at hx ⊢
      tauto
  · refine ⟨?_,hfresh.2.2.2.mono ?_,fun r hr => hsub r (List.mem_cons_of_mem _ hr),ho _ _ (Or.inr rfl)⟩
    · simp only [Set.disjoint_insert_left,Set.mem_insert_iff,not_or,Set.disjoint_insert_right]
      tauto
    · intro x hx
      simp only [Set.mem_union,Set.mem_insert_iff] at hx ⊢
      tauto

lemma variance_node_bound (gs ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hf : ∀ S, 0 < f S)
    (hsig : HasSlotSignature f) (hgs : SlotsFresh gs ∅)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅ / (4*slotDefect gs f ∅ p r) ≤ w p r)
    (A B : Set Γ) (hnode : VarianceNode gs ps A B) (hne : ps ≠ []) :
    ∃ p qs, ps.Perm (p::qs) ∧ SlotsFresh (p::qs) A ∧
      VarianceNode gs qs (insert p.1 A) (insert p.2 B) ∧
      VarianceNode gs qs (insert p.2 A) (insert p.1 B) ∧
      slotVariance (p::qs) f H A - slotVariance qs f H (insert p.1 A) -
        slotVariance qs f H (insert p.2 A) ≤
        (1+8*(gs.length : ℝ))*restrictedEnergy (chainEdges gs) (chainConductance gs w f) H A B := by
  obtain ⟨p,hp,hsink⟩ := slot_scores_have_sink ps gs f hf hsig A ∅
    (hnode.2.1.mono Set.subset_union_left) hgs hnode.2.2.1 hne
  let qs := ps.erase p
  have hperm : ps.Perm (p::qs) := List.perm_cons_erase hp
  have hnode' := hnode.perm hperm
  have hfr := hnode'.2.1
  have hfrA : SlotsFresh (p::qs) A := hfr.mono Set.subset_union_left
  have hps : SlotsFresh qs (A ∪ Set.range (rootEmbedding p.1 p.2)) :=
    hfrA.2.2.2.mono (by
      intro x hx
      rcases hx with hx | ⟨i,rfl⟩
      · exact Or.inr (Or.inr hx)
      · cases i <;> simp [rootEmbedding])
  let W := pairMultiplier qs (w p)
  have hW : ∀ x, 0 < W x := pairMultiplier_pos qs (w p) (hw p)
  have hws : ∀ r ∈ qs, W r.1 = W r.2 := by
    intro r hr
    dsimp only [W]
    rw [pairMultiplier_on hps _ r hr r.1 (Or.inl rfl),
      pairMultiplier_on hps _ r hr r.2 (Or.inr rfl)]
  have hWp : W p.1 = 1 := pairMultiplier_fresh hps _ _ (Or.inr ⟨false,rfl⟩)
  have hWd : W p.2 = 1 := pairMultiplier_fresh hps _ _ (Or.inr ⟨true,rfl⟩)
  have hsink' : ∀ x ∈ slotPunctures qs,
      slotTotal x.2 f (insert p.1 (insert p.2 A))/W x.1.1 ≤
        4*(slotTotal qs f (insert p.1 A)+slotTotal qs f (insert p.2 A)) := by
    intro x hx
    have hxq : x.1 ∈ qs := (slotPunctures_perm qs x hx).mem_iff.mpr List.mem_cons_self
    have hxp : p ≠ x.1 := hfr.pair_ne_of_mem hxq
    have hxps : x.1 ∈ ps := hperm.mem_iff.mpr (List.mem_cons_of_mem _ hxq)
    have hpG := hnode.2.2.1 p hp
    have hxG := hnode.2.2.1 x.1 hxps
    have hcpos := slotDefect_pos gs f hf ∅ hgs p x.1 hpG hxG hxp
    have hzpos := slotTotal_pos ps f hf A (hnode.2.1.mono Set.subset_union_left)
    have hs := hsink x.1 hxps hxp
    rw [slotDefect_perm hperm,slotDefect_puncture qs p A f hfrA x hx] at hs
    have hg := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hcpos)).mp (hgood p hpG x.1 hxG hxp)
    have hgz := mul_le_mul_of_nonneg_left hg hzpos.le
    have hbound : slotTotal x.2 f (insert p.1 (insert p.2 A)) ≤
        4*slotTotal ps f A*w p x.1 := by
      apply (mul_le_mul_iff_of_pos_right hcpos).mp
      nlinarith
    change slotTotal x.2 f (insert p.1 (insert p.2 A))/pairMultiplier qs (w p) x.1.1 ≤ _
    rw [pairMultiplier_on hps _ x.1 hxq x.1.1 (Or.inl rfl)]
    apply (div_le_iff₀ (hw p x.1)).mpr
    rw [slotTotal_perm hperm f,slotTotal_cons p qs f A hfrA.1 hfrA.2.1 hfrA.2.2.1] at hbound
    exact hbound
  have ht := transport_node_variance qs f H A p.1 p.2 W hf hsig hfrA.1 hfrA.2.1 hfrA.2.2.1
    hps hW hws hWp hWd hsink'
  have he := variance_energy_identification gs qs A B p w f H hw hf
    hnode'.2.2.1 hnode'.1 hfr hnode'.2.2.2
  have hqle : qs.length ≤ gs.length := by
    have hnodup := (hnode.2.1.nodup).erase p
    exact List.Subperm.length_le (List.subperm_of_subset hnodup (fun r hr => hnode'.2.2.1 r (List.mem_cons_of_mem _ hr)))
  have hqleR : (qs.length : ℝ) ≤ gs.length := by exact_mod_cast hqle
  have hepos : 0 ≤ restrictedEnergy (chainEdges gs) (chainConductance gs w f) H A B := by
    apply restrictedEnergy_nonneg
    intro ST _
    exact le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
  have hfinal := ht.trans ((mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ 1+8*(qs.length : ℝ))).trans
    (mul_le_mul_of_nonneg_right (by linarith : (1:ℝ)+8*(qs.length:ℝ) ≤ 1+8*(gs.length:ℝ)) hepos))
  refine ⟨p,qs,hperm,hfrA,hnode'.children.1,hnode'.children.2,?_⟩
  rw [slotVariance_split qs f H hf A p hfrA,slotTotal_cons p qs f A hfrA.1 hfrA.2.1 hfrA.2.2.1]
  linarith

theorem transversal_variance_bound (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hf : ∀ S, 0 < f S)
    (hsig : HasSlotSignature f) (hgs : SlotsFresh gs ∅)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅ / (4*slotDefect gs f ∅ p r) ≤ w p r) :
    slotVariance gs f H ∅ ≤ (gs.length : ℝ)*(1+8*(gs.length : ℝ))*
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  apply adaptive_variance_bound f H hf (chainEdges gs) (chainConductance gs w f)
    (fun ST _ => le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le))
    (1+8*(gs.length:ℝ)) (by positivity) (VarianceNode gs)
    (fun ps A B hnode hne => variance_node_bound gs ps f H w hf hsig hgs hw hgood A B hnode hne)
  exact ⟨by simp,by simpa using hgs,fun _ => id,fun r hr hn => False.elim (hn hr)⟩

end TransversalVariance

section ChoiceEnumeration
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance44 : Fintype Γ] [sectionInstance45 : DecidableEq Γ]

lemma slotVariance_eq_plain_variance (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f H : Set Γ → ℝ) :
    slotVariance gs f H ∅ =
      (∑ S ∈ Finset.univ.filter (PlainState gs), f S*(H S)^2) -
      (∑ S ∈ Finset.univ.filter (PlainState gs), f S*H S)^2 /
        (∑ S ∈ Finset.univ.filter (PlainState gs), f S) := by
  unfold slotVariance
  rw [slotTotal_eq_plain_sum gs hgs hcover,slotTotal_eq_plain_sum gs hgs hcover,
    slotTotal_eq_plain_sum gs hgs hcover]

end ChoiceEnumeration

section Observable
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance52 : Fintype Γ] [DecidableEq Γ]

omit sectionInstance52 in
lemma defectTypes_card_le [Fintype Γ] (gs : List (Γ × Γ)) :
    (defectTypes gs).card ≤ gs.length*gs.length := by
  calc
    _ ≤ gs.toFinset.card*gs.toFinset.card := by simp [defectTypes,Finset.offDiag_card]
    _ ≤ _ := Nat.mul_le_mul (List.toFinset_card_le _) (List.toFinset_card_le _)

lemma chainTotal_le (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hf : ∀ S, 0 < f S)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    chainTotal gs w f ≤ 5*(gs.length:ℝ)^2*slotTotal gs f ∅ := by
  rw [chainTotal_eq gs hgs hcover w f]
  have hz := slotTotal_pos gs f hf ∅ hgs
  have hc : (∑ pr ∈ defectTypes gs, w pr.1 pr.2*slotDefect gs f ∅ pr.1 pr.2) ≤
      (defectTypes gs).card*(4*slotTotal gs f ∅) := by
    calc
      _ ≤ ∑ _pr ∈ defectTypes gs, 4*slotTotal gs f ∅ := by
        apply Finset.sum_le_sum
        intro pr hm
        obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr).mp hm
        exact (le_div_iff₀ (slotDefect_pos gs f hf ∅ hgs pr.1 pr.2 hp hr hpr)).mp
          (hupper pr.1 hp pr.2 hr hpr)
      _ = _ := by simp
  have hcard : ((defectTypes gs).card:ℝ) ≤ (gs.length:ℝ)^2 := by
    exact_mod_cast (show (defectTypes gs).card ≤ gs.length^2 by simpa [pow_two] using defectTypes_card_le gs)
  have hn : 1 ≤ (gs.length:ℝ) := by exact_mod_cast List.length_pos_iff.mpr hne
  have hn2 : 1 ≤ (gs.length:ℝ)^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hcard (show 0 ≤ 4*slotTotal gs f ∅ by positivity)]

end Observable

open scoped BigOperators Classical

namespace FiniteChain
variable {X : Type*} [sectionInstance56 : Fintype X] (C : FiniteChain X)

lemma inner_nonneg (f : X → ℝ) : 0 ≤ C.inner f f := by
  apply Finset.sum_nonneg
  intro x _
  nlinarith [C.positive x,sq_nonneg (f x)]
lemma apply_const (a : ℝ) : C.apply (fun _ => a) = fun _ => a := by
  funext x
  simp [apply,← Finset.sum_mul,C.stochastic]

lemma stationary (y : X) : ∑ x, C.π x*C.P x y = C.π y := by
  simp_rw [C.reversible]
  rw [← Finset.mul_sum,C.stochastic,mul_one]

lemma energy_eq (f : X → ℝ) : C.energy f =
    (∑ x, ∑ y, C.π x*C.P x y*(f x-f y)^2)/2 := by
  have h₁ : (∑ x,∑ y,C.π x*C.P x y*(f x)^2) = C.inner f f := by
    simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul,C.stochastic,one_mul]
    unfold inner
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h₂ : (∑ x,∑ y,C.π x*C.P x y*(f y)^2) = C.inner f f := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,C.stationary]
    unfold inner
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h₃ : (∑ x,∑ y,C.π x*C.P x y*(f x*f y)) = C.inner f (C.apply f) := by
    unfold inner apply
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have he (x y : X) : C.π x*C.P x y*(f x-f y)^2 =
      C.π x*C.P x y*(f x)^2+C.π x*C.P x y*(f y)^2-2*(C.π x*C.P x y*(f x*f y)) := by ring
  simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [h₁,h₂,h₃,energy,inner_sub_right]
  ring

lemma energy_nonneg (f : X → ℝ) : 0 ≤ C.energy f := by
  rw [C.energy_eq]
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (mul_nonneg (C.positive x).le (C.nonnegative x y)) (sq_nonneg _)

lemma energy_le_inner (f : X → ℝ) : C.energy f ≤ C.inner f f := by
  classical
  have ho (x : X) : ∑ y ∈ Finset.univ.erase x,C.P x y ≤ 1/2 := by
    have h := Finset.sum_erase_add Finset.univ (fun y => C.P x y) (Finset.mem_univ x)
    rw [C.stochastic] at h
    linarith [C.lazy x]
  have hbound : (∑ x,∑ y,C.π x*C.P x y*(f x-f y)^2) ≤
      ∑ x,∑ y ∈ Finset.univ.erase x,2*(C.π x*C.P x y*(f x)^2+C.π x*C.P x y*(f y)^2) := by
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
    simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero]
    apply Finset.sum_le_sum
    intro y _
    have h := mul_le_mul_of_nonneg_left (show (f x-f y)^2 ≤ 2*((f x)^2+(f y)^2) by nlinarith [sq_nonneg (f x+f y)])
      (mul_nonneg (C.positive x).le (C.nonnegative x y))
    nlinarith
  have hs (x : X) : (∑ y ∈ Finset.univ.erase x,C.π x*C.P x y*(f x)^2) ≤ (C.π x*(f x)^2)/2 := by
    calc
      _ = (C.π x*(f x)^2)*(∑ y ∈ Finset.univ.erase x,C.P x y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (ho x) (mul_nonneg (C.positive x).le (sq_nonneg (f x)))]
  have hswap : (∑ x,∑ y ∈ Finset.univ.erase x,C.π x*C.P x y*(f y)^2) =
      ∑ x,∑ y ∈ Finset.univ.erase x,C.π x*C.P x y*(f x)^2 := by
    simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [C.reversible]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hs x)
  have heq : (∑ x,C.π x*(f x)^2/2) = C.inner f f/2 := by
    rw [← Finset.sum_div]
    congr 1
    unfold inner
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq] at hsum
  simp_rw [← Finset.mul_sum,Finset.sum_add_distrib] at hbound
  rw [hswap] at hbound
  rw [C.energy_eq]
  linarith

lemma apply_positive (f : X → ℝ) : 0 ≤ C.inner f (C.apply f) := by
  have h := C.energy_le_inner f
  rw [energy,inner_sub_right] at h
  linarith

lemma iterate_succ (k : ℕ) (f : X → ℝ) : C.iterate (k+1) f = C.apply (C.iterate k f) := by
  exact Function.iterate_succ_apply' C.apply k f

variable [DecidableEq X]

lemma ofMoves_energy (π : X → ℝ) (m : X → X → ℝ)
    (hπ : ∀ x,0 < π x) (hπsum : ∑ x,π x = 1)
    (hm : ∀ x y,0 ≤ m x y) (hrow : ∀ x,∑ y,m x y ≤ 1/2)
    (hrev : ∀ x y,π x*m x y = π y*m y x) (f : X → ℝ) :
    (ofMoves π m hπ hπsum hm hrow hrev).energy f =
      (∑ x,∑ y,π x*m x y*(f x-f y)^2)/2 := by
  rw [energy_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change π x*(m x y+if x=y then _ else _)*(f x-f y)^2 = _
  by_cases h : x=y
  · subst y; simp
  · simp [h]

end FiniteChain
section Metropolis
open scoped BigOperators Classical
variable {Γ : Type*} [Fintype Γ] [sectionInstance59 : DecidableEq Γ]

lemma chainEdges_sum (gs : List (Γ × Γ)) (g : (Set Γ × Set Γ) → ℝ) :
    (∑ ST ∈ chainEdges gs,g ST) =
      ∑ S : ChainIndex gs,∑ T : ChainIndex gs,
        if ExchangeAdjacent S.val T.val then g (S.val,T.val) else 0 := by
  calc
    _ = ∑ S ∈ chainStates gs,∑ T ∈ chainStates gs,
        if ExchangeAdjacent S T then g (S,T) else 0 := by
      simp only [chainEdges,chainStates,Finset.sum_filter,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hs : ChainState gs S
      · simp only [hs,true_and,ite_true]
        apply Finset.sum_congr rfl
        intro T _
        by_cases ht : ChainState gs T <;> simp [ht]
      · simp [hs]
    _ = _ := by
      rw [chain_sum_subtype]
      apply Finset.sum_congr rfl
      intro S _
      exact chain_sum_subtype gs _

lemma restrictedEnergy_chain_eq (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ) :
    restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ =
      (∑ S : ChainIndex gs, ∑ T : ChainIndex gs,
        if ExchangeAdjacent S.val T.val then
          min (chainWeight gs w f S.val) (chainWeight gs w f T.val)*(H S.val-H T.val)^2 else 0)/2 := by
  unfold restrictedEnergy
  simp only [EdgeRespects,Respects,Set.empty_subset,Set.empty_disjoint,and_self,ite_true]
  rw [chainEdges_sum]
  rfl

theorem metropolisChain_energy (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f H : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) :
    (metropolisChain gs hgs hne hcover w f hw hf).energy (fun S => H S.val) = chainDirichlet gs w f H := by
  unfold metropolisChain
  rw [FiniteChain.ofMoves_energy]
  have he (S T : ChainIndex gs) :
      (chainWeight gs w f S.val/chainTotal gs w f)*metropolisMove gs w f S T*(H S.val-H T.val)^2 =
      (if ExchangeAdjacent S.val T.val then
        min (chainWeight gs w f S.val) (chainWeight gs w f T.val)*(H S.val-H T.val)^2 else 0)/
        (2*(gs.length:ℝ)^2*chainTotal gs w f) := by
    have hs := (chainWeight_pos gs w f hw hf S.val).ne'
    unfold metropolisMove
    split_ifs
    · field_simp
    · simp
  simp_rw [he,← Finset.sum_div]
  rw [chainDirichlet,restrictedEnergy_chain_eq]
  ring

end Metropolis

namespace FiniteChain
variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma inner_cauchy (f g : X → ℝ) : (C.inner f g)^2 ≤ C.inner f f*C.inner g g := by
  have he (f g : X → ℝ) : (∑ x,(Real.sqrt (C.π x)*f x)*(Real.sqrt (C.π x)*g x)) = C.inner f g := by
    unfold inner
    apply Finset.sum_congr rfl
    intro x _
    have hs := Real.sq_sqrt (C.positive x).le
    calc
      _ = (Real.sqrt (C.π x))^2*f x*g x := by ring
      _ = _ := by rw [hs]
  have hf (f : X → ℝ) : (∑ x,(Real.sqrt (C.π x)*f x)^2) = C.inner f f := by
    simpa only [pow_two] using he f f
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (C.π x)*f x) (fun x => Real.sqrt (C.π x)*g x)
  rwa [he,hf,hf] at h

end FiniteChain
section ProjectionBridge
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance61 : Fintype Γ] [sectionInstance62 : DecidableEq Γ]

omit sectionInstance61 sectionInstance62 in
lemma extendChainFun_apply [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (H : ChainIndex gs → ℝ) (S : ChainIndex gs) :
    extendChainFun gs H S.val = H S := by simp [extendChainFun,S.property]

end ProjectionBridge

namespace KilledKernel
open scoped BigOperators Classical
open Filter
variable {B : Type*} [Fintype B] (Q : KilledKernel B)
lemma apply_mul (a : ℝ) (f : B → ℝ) : Q.apply (fun x => a*f x) = fun x => a*Q.apply f x := by
  funext x
  simp only [apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring
lemma iterate_mul (a : ℝ) (f : B → ℝ) (k : ℕ) :
    Q.iterate k (fun x => a*f x) = fun x => a*Q.iterate k f x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Q.iterate_succ,ih,Q.apply_mul,← Q.iterate_succ]

end KilledKernel
namespace FiniteChain

section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
variable (Q : KilledKernel (Outside A)) (hQ : ∀ x y : Outside A,Q.Q x y = C.P x.val y.val)

lemma traceChain_energy [Nonempty (Inside A)] (h : Inside A → ℝ) :
    C.energy (C.harmonicExtension A Q h) =
      C.insideMass A*(C.traceChain A Q hQ).energy h := by
  rw [energy,C.harmonic_inner_residual A Q hQ]
  change _ = C.insideMass A*(∑ x : Inside A,
    (C.π x.val/C.insideMass A)*h x*(h x-C.traceApply A Q h x))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(C.insideMass_pos A).ne']

lemma mean_apply (f : X → ℝ) : C.mean (C.apply f) = C.mean f := by
  unfold mean apply
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc,← Finset.sum_mul,C.stationary]
lemma mean_residual (f : X → ℝ) : C.mean (fun x => f x-C.apply f x) = 0 := by
  unfold mean
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  change C.mean f-C.mean (C.apply f) = 0
  rw [C.mean_apply,sub_self]

lemma duration_nonneg (x : Outside A) : 0 ≤ duration A Q x :=
  Q.green_nonneg _ (by intro; norm_num) x
lemma returnCost_nonneg (x : Inside A) : 0 ≤ C.returnCost A Q x :=
  add_nonneg (by norm_num) (Finset.sum_nonneg (fun y _ =>
    mul_nonneg (C.nonnegative _ _) (duration_nonneg A Q y)))

include hQ in
lemma expected_returnCost : (∑ x : Inside A,C.π x.val*C.returnCost A Q x) = 1 := by
  let l : X → ℝ := mergeFun A (fun _ => 0) (duration A Q)
  have hi (x : Inside A) : l x.val = 0 := by simp [l]
  have ho (x : Outside A) : l x.val = duration A Q x := by simp [l]
  have hai (x : Inside A) : C.apply l x.val = ∑ y : Outside A,C.P x.val y.val*duration A Q y := by
    unfold apply
    rw [← Fintype.sum_subtype_add_sum_subtype A]
    simp only [hi,ho,mul_zero,Finset.sum_const_zero,zero_add]
  have hao (x : Outside A) : C.apply l x.val = Q.apply (duration A Q) x := by
    unfold apply
    rw [← Fintype.sum_subtype_add_sum_subtype A]
    simp only [hi,ho,mul_zero,Finset.sum_const_zero,zero_add,KilledKernel.apply,hQ]
  have hr (x : Outside A) : l x.val-C.apply l x.val = 1 := by
    rw [ho,hao]
    have hg := Q.green_firstStep (fun _ => (1:ℝ)) x
    change duration A Q x = 1+Q.apply (duration A Q) x at hg
    linarith
  have hm := C.mean_residual l
  unfold mean at hm
  rw [← Fintype.sum_subtype_add_sum_subtype A] at hm
  simp only [hi,hai,hr,zero_sub,mul_neg,Finset.sum_neg_distrib,mul_one] at hm
  have hmass := Fintype.sum_subtype_add_sum_subtype A C.π
  rw [C.normalized] at hmass
  unfold returnCost
  simp only [mul_add,mul_one,Finset.sum_add_distrib]
  linarith

lemma traceChain_returnCost [Nonempty (Inside A)] :
    (C.traceChain A Q hQ).mean (C.returnCost A Q) = 1/C.insideMass A := by
  change (∑ x : Inside A,(C.π x.val/C.insideMass A)*C.returnCost A Q x) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,C.expected_returnCost A Q hQ]

lemma warm_returnCost [Nonempty (Inside A)] (ν : Inside A → ℝ) (U : ℝ)
    (hν : ∀ x,ν x ≤ U*(C.traceChain A Q hQ).π x) :
    (∑ x,ν x*C.returnCost A Q x) ≤ U/C.insideMass A := by
  calc
    _ ≤ ∑ x,U*(C.traceChain A Q hQ).π x*C.returnCost A Q x :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hν x) (C.returnCost_nonneg A Q x))
    _ = U*(C.traceChain A Q hQ).mean (C.returnCost A Q) := by simp [mean,Finset.mul_sum,mul_assoc]
    _ = _ := by rw [C.traceChain_returnCost A Q hQ]; ring
end
open scoped Classical BigOperators
variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma apply_cauchy (f g : X → ℝ) :
    (C.inner f (C.apply g))^2 ≤ C.inner f (C.apply f)*C.inner g (C.apply g) := by
  let B : LinearMap.BilinForm ℝ (X → ℝ) := Matrix.toBilin' (fun x y => C.π x*C.P x y)
  have he (u v : X → ℝ) : B u v = C.inner u (C.apply v) := by
    simp only [B,inner,apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    change v y*(u x*(C.π x*C.P x y))=C.π x*u x*(C.P x y*v y)
    ring
  have hs : LinearMap.IsSymm B := by
    constructor
    intro u v
    simp only [he,RingHom.id_apply]
    rw [C.apply_selfAdjoint,C.inner_symm]
  simpa only [he] using B.apply_sq_le_of_symm (fun u => by rw [he]; exact C.apply_positive u) hs f g

lemma inner_sub_left (f g h : X → ℝ) :
    C.inner (fun x => f x-g x) h = C.inner f h-C.inner g h := by
  rw [C.inner_symm,C.inner_sub_right,C.inner_symm h f,C.inner_symm h g]
lemma apply_sub (f g : X → ℝ) : C.apply (fun x => f x-g x) = fun x => C.apply f x-C.apply g x := by
  funext x
  simp [apply,mul_sub,Finset.sum_sub_distrib]
lemma mean_const (a : ℝ) : C.mean (fun _ => a) = a := by
  simp [mean,← Finset.sum_mul,C.normalized]
lemma mean_sub (f g : X → ℝ) : C.mean (fun x => f x-g x) = C.mean f-C.mean g := by
  simp [mean,mul_sub,Finset.sum_sub_distrib]
lemma variance_eq_inner (f : X → ℝ) (hf : C.mean f = 0) : C.variance f = C.inner f f := by
  simp [variance,hf]

lemma apply_contraction (r : ℝ) (hr : 0 ≤ r)
    (hgap : ∀ f : X → ℝ,C.mean f = 0 → C.inner f (C.apply f) ≤ r*C.inner f f)
    (f : X → ℝ) (hf : C.mean f = 0) :
    C.inner (C.apply f) (C.apply f) ≤ r^2*C.inner f f := by
  have hg : C.mean (C.apply f) = 0 := by rw [C.mean_apply,hf]
  have hcs := C.apply_cauchy (C.apply f) f
  have h₁ := hgap f hf
  have h₂ := hgap (C.apply f) hg
  have hp₁ := C.apply_positive f
  have hp₂ := C.apply_positive (C.apply f)
  have hn := C.inner_nonneg (C.apply f)
  have hm := C.inner_nonneg f
  have hb := mul_le_mul h₂ h₁ hp₁ (mul_nonneg hr hn)
  by_cases hz : C.inner (C.apply f) (C.apply f) = 0
  · rw [hz]; positivity
  · have hpos : 0 < C.inner (C.apply f) (C.apply f) := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith

lemma iterate_mean (k : ℕ) (f : X → ℝ) : C.mean (C.iterate k f) = C.mean f := by
  induction k with
  | zero => rfl
  | succ k ih => rw [C.iterate_succ,C.mean_apply,ih]
lemma iterate_contraction (r : ℝ) (hr : 0 ≤ r)
    (hgap : ∀ f : X → ℝ,C.mean f = 0 → C.inner f (C.apply f) ≤ r*C.inner f f)
    (k : ℕ) (f : X → ℝ) (hf : C.mean f = 0) :
    C.inner (C.iterate k f) (C.iterate k f) ≤ r^(2*k)*C.inner f f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [C.iterate_succ]
    calc
      _ ≤ r^2*C.inner (C.iterate k f) (C.iterate k f) :=
        C.apply_contraction r hr hgap _ (by rw [C.iterate_mean,hf])
      _ ≤ r^2*(r^(2*k)*C.inner f f) := mul_le_mul_of_nonneg_left ih (sq_nonneg r)
      _ = _ := by rw [show 2*(k+1)=2+2*k by omega,pow_add]; ring

lemma pointDensity_mean (x : X) : C.mean (C.pointDensity x) = 1 := by
  simp [mean,pointDensity,(C.positive x).ne']
lemma centeredPoint_mean (x : X) : C.mean (C.centeredPoint x) = 0 := by
  change C.mean (fun z => C.pointDensity x z-1) = 0
  rw [C.mean_sub,C.pointDensity_mean,C.mean_const,sub_self]
lemma pointDensity_inner (x : X) (f : X → ℝ) : C.inner (C.pointDensity x) f = f x := by
  simp [inner,pointDensity,(C.positive x).ne']
lemma centeredPoint_norm (x : X) : C.inner (C.centeredPoint x) (C.centeredPoint x) ≤ 1/C.π x := by
  unfold centeredPoint
  rw [C.inner_sub_left,C.inner_sub_right,C.inner_sub_right,C.pointDensity_inner,
    C.pointDensity_inner,C.inner_symm (fun _ => 1),C.pointDensity_inner]
  have h₁ : C.inner (fun _ => 1) (fun _ => 1) = 1 := by simp [inner,C.normalized]
  rw [h₁]
  simp only [pointDensity,ite_true]
  linarith

lemma iterate_const (k : ℕ) (a : ℝ) : C.iterate k (fun _ => a) = fun _ => a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [C.iterate_succ,ih,C.apply_const]
lemma iterate_sub (k : ℕ) (f g : X → ℝ) :
    C.iterate k (fun x => f x-g x) = fun x => C.iterate k f x-C.iterate k g x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [C.iterate_succ,ih,C.apply_sub,C.iterate_succ,C.iterate_succ]

lemma point_mixing_squared (r : ℝ) (hr : 0 ≤ r)
    (hgap : ∀ f : X → ℝ,C.mean f = 0 → C.inner f (C.apply f) ≤ r*C.inner f f)
    (k : ℕ) (x y : X) :
    (C.iterate k (C.pointDensity y) x-1)^2 ≤ r^(2*k)/(C.π x*C.π y) := by
  have he : C.inner (C.centeredPoint x) (C.iterate k (C.centeredPoint y)) =
      C.iterate k (C.pointDensity y) x-1 := by
    change C.inner (fun z => C.pointDensity x z-1) (C.iterate k (C.centeredPoint y)) = _
    rw [C.inner_sub_left,C.pointDensity_inner]
    have hm : C.inner (fun _ => 1) (C.iterate k (C.centeredPoint y)) = 0 := by
      have hz := C.iterate_mean k (C.centeredPoint y)
      rw [C.centeredPoint_mean] at hz
      simpa only [inner,mean,mul_one] using hz
    rw [hm,sub_zero]
    change C.iterate k (fun z => C.pointDensity y z-1) x = _
    rw [C.iterate_sub,C.iterate_const]
  have hcs := C.inner_cauchy (C.centeredPoint x) (C.iterate k (C.centeredPoint y))
  rw [he] at hcs
  have hcon := C.iterate_contraction r hr hgap k (C.centeredPoint y) (C.centeredPoint_mean y)
  have hny := C.centeredPoint_norm y
  have hnx := C.centeredPoint_norm x
  have hb := mul_le_mul hnx (hcon.trans (mul_le_mul_of_nonneg_left hny (pow_nonneg hr _)))
    (C.inner_nonneg _) (div_nonneg (by norm_num) (C.positive x).le)
  calc
    _ ≤ _ := hcs.trans hb
    _ = _ := by field_simp
lemma variance_formula (f : X → ℝ) : C.variance f = C.inner f f-(C.mean f)^2 := by
  rw [variance,C.inner_sub_left,C.inner_sub_right,C.inner_sub_right]
  have h₁ : C.inner f (fun _ => C.mean f) = (C.mean f)^2 := by
    unfold inner
    rw [← Finset.sum_mul]
    change C.mean f*C.mean f = (C.mean f)^2
    ring
  have h₂ : C.inner (fun _ => C.mean f) (fun _ => C.mean f) = (C.mean f)^2 := by
    simp only [inner,← Finset.sum_mul,C.normalized,one_mul,pow_two]
  rw [h₁,C.inner_symm (fun _ => C.mean f) f,h₁,h₂]
  ring

lemma poincare_rayleigh (K : ℝ) (hK : 0 < K)
    (hp : ∀ f : X → ℝ,C.variance f ≤ K*C.energy f)
    (f : X → ℝ) (hf : C.mean f = 0) :
    C.inner f (C.apply f) ≤ (1-1/K)*C.inner f f := by
  have h := hp f
  rw [C.variance_eq_inner f hf,energy,C.inner_sub_right] at h
  apply (mul_le_mul_iff_right₀ hK).mp
  field_simp
  nlinarith

lemma point_mixing (r m : ℝ) (hr : 0 ≤ r) (hm : 0 < m) (hπ : ∀ x,m ≤ C.π x)
    (hgap : ∀ f : X → ℝ,C.mean f = 0 → C.inner f (C.apply f) ≤ r*C.inner f f)
    (k : ℕ) (x y : X) :
    |C.iterate k (C.pointDensity y) x-1| ≤ r^k/m := by
  have hs := C.point_mixing_squared r hr hgap k x y
  have hd : m^2 ≤ C.π x*C.π y := by simpa only [pow_two] using mul_le_mul (hπ x) (hπ y) hm.le (C.positive x).le
  have hb : r^(2*k)/(C.π x*C.π y) ≤ (r^k/m)^2 := by
    calc
      _ ≤ r^(2*k)/m^2 := div_le_div_of_nonneg_left (pow_nonneg hr _) (sq_pos_of_pos hm) hd
      _ = _ := by rw [mul_comm 2 k,pow_mul,div_pow]
  have ha : (|C.iterate k (C.pointDensity y) x-1|)^2 ≤ (r^k/m)^2 := by
    rw [sq_abs]
    exact hs.trans hb
  exact (sq_le_sq₀ (abs_nonneg _) (div_nonneg (pow_nonneg hr _) hm.le)).mp ha

lemma point_mixing_exp (K m : ℝ) (hK : 1 ≤ K) (hm : 0 < m) (hπ : ∀ x,m ≤ C.π x)
    (hp : ∀ f : X → ℝ,C.variance f ≤ K*C.energy f)
    (k : ℕ) (x y : X) :
    |C.iterate k (C.pointDensity y) x-1| ≤ Real.exp (-(k:ℝ)/K)/m := by
  have hKp : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hr : 0 ≤ 1-1/K := sub_nonneg.mpr ((div_le_one hKp).mpr hK)
  have hpow : (1-1/K)^k ≤ Real.exp (-(k:ℝ)/K) := by
    have hle : 1-1/K ≤ Real.exp (-1/K) := by
      have hh := Real.add_one_le_exp (-1/K)
      convert hh using 1 <;> first | rfl | ring
    calc
      _ ≤ (Real.exp (-1/K))^k := pow_le_pow_left₀ hr hle k
      _ = Real.exp ((k:ℝ)*(-1/K)) := (Real.exp_nat_mul _ _).symm
      _ = _ := by congr 1; ring
  exact (C.point_mixing _ m hr hm hπ (C.poincare_rayleigh K hKp hp) k x y).trans
    (div_le_div_of_nonneg_right hpow hm.le)
end FiniteChain
section TracePoincare
open scoped Classical BigOperators
variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
  (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
  (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)

lemma metropolis_insideMass :
    (metropolisChain gs hgs hne hcover w f hw hf).insideMass (plainPredicate gs) =
      slotTotal gs f ∅/chainTotal gs w f := by
  change (∑ S : PlainIndex gs,chainWeight gs w f S.val.val/chainTotal gs w f) = _
  have he (S : PlainIndex gs) : chainWeight gs w f S.val.val = f S.val.val := by
    rw [chainWeight,chainMultiplier_plain gs w S.val.val S.property,one_mul]
  simp_rw [he]
  rw [← Finset.sum_div,plainIndex_sum,slotTotal_eq_plain_sum gs hgs hcover]

lemma metropolisTrace_pi (S : PlainIndex gs) :
    (metropolisTrace gs hgs hne hcover w f hw hf).π S = f S.val.val/slotTotal gs f ∅ := by
  change (chainWeight gs w f S.val.val/chainTotal gs w f)/
    (metropolisChain gs hgs hne hcover w f hw hf).insideMass (plainPredicate gs) = _
  rw [metropolis_insideMass gs hgs hne hcover w f hw hf,chainWeight,
    chainMultiplier_plain gs w S.val.val S.property,one_mul]
  field_simp [(chainTotal_pos gs hgs hcover w f hf hw).ne']

lemma metropolisTrace_variance (H : Set Γ → ℝ) :
    (metropolisTrace gs hgs hne hcover w f hw hf).variance (fun S => H S.val.val) =
      slotVariance gs f H ∅/slotTotal gs f ∅ := by
  rw [FiniteChain.variance_formula]
  unfold FiniteChain.inner FiniteChain.mean
  simp_rw [metropolisTrace_pi,div_mul_eq_mul_div,← Finset.sum_div]
  rw [plainIndex_sum gs (fun S => f S*H S*H S),plainIndex_sum gs (fun S => f S*H S),
    slotVariance_eq_plain_variance gs hgs hcover,slotTotal_eq_plain_sum gs hgs hcover]
  have he : (∑ S with PlainState gs S,f S*H S*H S) = ∑ S with PlainState gs S,f S*(H S)^2 := by
    apply Finset.sum_congr rfl; intro S _; ring
  rw [he]
  have hz := (slotTotal_pos gs f hf ∅ hgs).ne'
  rw [slotTotal_eq_plain_sum gs hgs hcover] at hz
  field_simp

theorem metropolisTrace_poincare (hsig : HasSlotSignature f)
    (hgood : ∀ p ∈ gs,∀ r ∈ gs,p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (h : PlainIndex gs → ℝ) :
    (metropolisTrace gs hgs hne hcover w f hw hf).variance h ≤
      18*(gs.length:ℝ)^4*(metropolisTrace gs hgs hne hcover w f hw hf).energy h := by
  let := plainIndex_nonempty gs hgs hcover
  let C := metropolisChain gs hgs hne hcover w f hw hf
  let Q := metropolisKilled gs hgs hne hcover w f hw hf
  let H := C.harmonicExtension (plainPredicate gs) Q h
  let F := extendChainFun gs H
  have hF (S : ChainIndex gs) : F S.val = H S := extendChainFun_apply gs H S
  have hh (S : PlainIndex gs) : F S.val.val = h S := by
    rw [hF]; exact C.harmonicExtension_inside (plainPredicate gs) Q h S
  have hvar := metropolisTrace_variance gs hgs hne hcover w f hw hf F
  have hefun : (fun S : PlainIndex gs => F S.val.val) = h := funext hh
  rw [hefun] at hvar
  have hv := transversal_variance_bound gs f F w hf hsig hgs hw hgood
  have hz := slotTotal_pos gs f hf ∅ hgs
  have hΛ := chainTotal_pos gs hgs hcover w f hf hw
  have hn : (1:ℝ) ≤ gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have henergy : restrictedEnergy (chainEdges gs) (chainConductance gs w f) F ∅ ∅ =
      (2*(gs.length:ℝ)^2*slotTotal gs f ∅)*(metropolisTrace gs hgs hne hcover w f hw hf).energy h := by
    have hc := metropolisChain_energy gs hgs hne hcover w f F hw hf
    have hfFn : (fun S : ChainIndex gs => F S.val) = H := funext hF
    rw [hfFn] at hc
    change C.energy (C.harmonicExtension (plainPredicate gs) Q h) = _ at hc
    rw [C.traceChain_energy (plainPredicate gs) Q (by intro _ _; rfl)] at hc
    change C.insideMass (plainPredicate gs)*(metropolisTrace gs hgs hne hcover w f hw hf).energy h = _ at hc
    rw [metropolis_insideMass gs hgs hne hcover w f hw hf] at hc
    unfold chainDirichlet at hc
    field_simp at hc
    nlinarith
  rw [henergy] at hv
  rw [hvar]
  have hE := (metropolisTrace gs hgs hne hcover w f hw hf).energy_nonneg h
  apply (div_le_iff₀ hz).mpr
  have hconst : (gs.length:ℝ)*(1+8*(gs.length:ℝ))*(2*(gs.length:ℝ)^2) ≤ 18*(gs.length:ℝ)^4 := by
    nlinarith [sq_nonneg ((gs.length:ℝ)-1),sq_nonneg (gs.length:ℝ)]
  have hb := mul_le_mul_of_nonneg_right hconst (mul_nonneg hz.le hE)
  nlinarith
end TracePoincare

namespace KilledKernel
open scoped BigOperators Classical
variable {B : Type*} [Fintype B] (Q : KilledKernel B)
lemma apply_mono {f g : B → ℝ} (h : ∀ x,f x ≤ g x) (x : B) : Q.apply f x ≤ Q.apply g x :=
  Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (h y) (Q.nonnegative x y))
lemma iterate_mono {f g : B → ℝ} (h : ∀ x,f x ≤ g x) (k : ℕ) (x : B) :
    Q.iterate k f x ≤ Q.iterate k g x := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih => rw [Q.iterate_succ,Q.iterate_succ]; exact Q.apply_mono ih x
lemma survival_antitone (x : B) : Antitone (fun k => Q.iterate k (fun _ => 1) x) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [Q.iterate_succ']
  apply Q.iterate_mono
  intro y
  simpa only [apply,mul_one] using (Q.rowbound y).trans Q.rlt.le
lemma duration_tail (N : ℕ) (x : B) :
    (N:ℝ)*Q.iterate N (fun _ => 1) x ≤ Q.green (fun _ => 1) x := by
  calc
    _ = ∑ k ∈ Finset.range N,Q.iterate N (fun _ => 1) x := by simp
    _ ≤ ∑ k ∈ Finset.range N,Q.iterate k (fun _ => 1) x :=
      Finset.sum_le_sum (fun k hk => Q.survival_antitone x (Finset.mem_range.mp hk).le)
    _ ≤ _ := (Q.summable_iterate (fun _ => 1) x).sum_le_tsum (Finset.range N)
      (fun k _ => Q.iterate_nonneg k _ (by intro; norm_num) x)
lemma partialGreen_sum {J : Type*} (s : Finset J) (f : J → B → ℝ) (N : ℕ) (x : B) :
    Q.partialGreen N (fun y => ∑ j ∈ s,f j y) x = ∑ j ∈ s,Q.partialGreen N (f j) x := by
  unfold partialGreen
  simp_rw [Q.iterate_sum]
  exact Finset.sum_comm
end KilledKernel

namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
  (Q : KilledKernel (Outside A)) (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)

include hQ in
lemma cappedTrace_mass (N : ℕ) (x : Inside A) :
    ∑ y,C.cappedTrace A Q N x y = 1-∑ z : Outside A,C.P x.val z.val*Q.iterate N (fun _ => 1) z := by
  unfold cappedTrace
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,← Q.partialGreen_sum]
  have he : (fun t : Outside A => ∑ y : Inside A,C.P t.val y.val) =
      fun t => 1-Q.apply (fun _ => 1) t := by
    funext t
    exact C.exitRow A Q hQ t
  rw [he]
  simp_rw [KilledKernel.partialGreen,Q.iterate_residual_sum,mul_sub,mul_one,Finset.sum_sub_distrib]
  have hs := Fintype.sum_subtype_add_sum_subtype A (fun y => C.P x.val y)
  rw [C.stochastic] at hs
  linarith

include hQ in
lemma cappedTrace_loss (N : ℕ) (x : Inside A) :
    (N:ℝ)*(1-∑ y,C.cappedTrace A Q N x y) ≤ C.returnCost A Q x := by
  rw [C.cappedTrace_mass A Q hQ]
  simp only [sub_sub_cancel]
  calc
    _ = ∑ z : Outside A,C.P x.val z.val*((N:ℝ)*Q.iterate N (fun _ => 1) z) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
    _ ≤ ∑ z : Outside A,C.P x.val z.val*duration A Q z :=
      Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (Q.duration_tail N z) (C.nonnegative _ _))
    _ ≤ _ := by unfold returnCost; linarith

lemma cappedTrace_warm_loss [Nonempty (Inside A)] (N : ℕ) (U : ℝ) (ν : Inside A → ℝ)
    (hν : ∀ x,0 ≤ ν x) (hwarm : ∀ x,ν x ≤ U*(C.traceChain A Q hQ).π x) :
    (N:ℝ)*(∑ x,ν x*(1-∑ y,C.cappedTrace A Q N x y)) ≤ U/C.insideMass A := by
  calc
    _ = ∑ x,ν x*((N:ℝ)*(1-∑ y,C.cappedTrace A Q N x y)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ ∑ x,ν x*C.returnCost A Q x := Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (C.cappedTrace_loss A Q hQ N x) (hν x))
    _ ≤ _ := C.warm_returnCost A Q hQ ν U hwarm
end FiniteChain

namespace FiniteKernel
open scoped BigOperators Classical
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
lemma push_nonneg (K : FiniteKernel X Y) (ν : X → ℝ) (hν : ∀ x,0 ≤ ν x) (y : Y) :
    0 ≤ K.push ν y := Finset.sum_nonneg (fun x _ => mul_nonneg (hν x) (K.nonnegative x y))
lemma push_mono (K : FiniteKernel X Y) {ν ν' : X → ℝ} (h : ∀ x,ν x ≤ ν' x) (y : Y) :
    K.push ν y ≤ K.push ν' y := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (h x) (K.nonnegative x y))
lemma push_comp (K : FiniteKernel X Y) (L : FiniteKernel Y Z) (ν : X → ℝ) :
    (K.comp L).push ν = L.push (K.push ν) := by
  funext z
  simp only [push,comp,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  exact Finset.sum_comm
lemma push_identity (ν : X → ℝ) : (identity : FiniteKernel X X).push ν = ν := by
  funext x; simp [push,identity]
lemma push_mass (K : FiniteKernel X Y) (ν : X → ℝ) :
    ∑ y,K.push ν y = ∑ x,ν x*(∑ y,K.P x y) := by
  unfold push; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
lemma push_mass_le (K : FiniteKernel X Y) (ν : X → ℝ) (hν : ∀ x,0 ≤ ν x) :
    ∑ y,K.push ν y ≤ ∑ x,ν x := by
  rw [K.push_mass]
  exact Finset.sum_le_sum (fun x _ => by simpa using mul_le_mul_of_nonneg_left (K.substochastic x) (hν x))
lemma power_push_succ (K : FiniteKernel X X) (n : ℕ) (ν : X → ℝ) :
    (K.power (n+1)).push ν = K.push ((K.power n).push ν) := (K.power n).push_comp K ν
lemma push_domination (K L : FiniteKernel X Y) (hKL : ∀ x y,K.P x y ≤ L.P x y)
    (ν : X → ℝ) (hν : ∀ x,0 ≤ ν x) (y : Y) : K.push ν y ≤ L.push ν y :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hKL x y) (hν x))
lemma power_domination (K L : FiniteKernel X X) (hKL : ∀ x y,K.P x y ≤ L.P x y)
    (n : ℕ) (ν : X → ℝ) (hν : ∀ x,0 ≤ ν x) (y : X) :
    (K.power n).push ν y ≤ (L.power n).push ν y := by
  induction n generalizing y with
  | zero => exact le_rfl
  | succ n ih =>
    rw [K.power_push_succ,L.power_push_succ]
    exact (K.push_mono (fun y => ih y) y).trans
      (K.push_domination L hKL _ ((L.power n).push_nonneg ν hν) y)

lemma one_step_defect (K L : FiniteKernel X Y) (hL : ∀ x,∑ y,L.P x y=1)
    (a b : X → ℝ) (_ : ∀ x,0 ≤ a x) (hab : ∀ x,a x ≤ b x) :
    (∑ y,L.push b y)-(∑ y,K.push a y) ≤
      (∑ x,b x)-(∑ x,a x)+∑ x,b x*(1-∑ y,K.P x y) := by
  rw [L.push_mass,K.push_mass]
  simp_rw [hL,mul_one]
  have hh : ∑ x,a x*(1-∑ y,K.P x y) ≤ ∑ x,b x*(1-∑ y,K.P x y) :=
    Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hab x) (sub_nonneg.mpr (K.substochastic x)))
  simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib] at hh ⊢
  linarith
end FiniteKernel

namespace FiniteChain

section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
lemma push_warm (ν : X → ℝ) (U : ℝ) (hν : ∀ x,ν x ≤ U*C.π x) (y : X) :
    C.kernel.push ν y ≤ U*C.π y := by
  calc
    _ ≤ ∑ x,U*C.π x*C.P x y := C.kernel.push_mono hν y
    _ = U*C.π y := by simp only [mul_assoc,← Finset.mul_sum,C.stationary]
lemma power_warm (n : ℕ) (ν : X → ℝ) (U : ℝ) (hν : ∀ x,ν x ≤ U*C.π x) (y : X) :
    (C.kernel.power n).push ν y ≤ U*C.π y := by
  induction n generalizing y with
  | zero => simpa [FiniteKernel.power,FiniteKernel.push_identity] using hν y
  | succ n ih => rw [FiniteKernel.power_push_succ]; exact C.push_warm _ U (fun y => ih y) y
lemma kernel_power_stochastic (n : ℕ) (x : X) : ∑ y,(C.kernel.power n).P x y=1 := by
  induction n with
  | zero => simp [FiniteKernel.power,FiniteKernel.identity]
  | succ n ih =>
    change (∑ y,∑ z,(C.kernel.power n).P x z*C.P z y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,C.stochastic,mul_one]
    exact ih
lemma power_push_mass (n : ℕ) (ν : X → ℝ) : ∑ y,(C.kernel.power n).push ν y = ∑ x,ν x := by
  rw [FiniteKernel.push_mass]
  simp_rw [C.kernel_power_stochastic,mul_one]

end

open scoped BigOperators Classical
end FiniteChain

section SamplingObservables
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance85 : Fintype Γ] [DecidableEq Γ]
lemma plain_mass_lower (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs≠[])
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)
    (hupper : ∀ p∈gs,∀ r∈gs,p≠r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    1/(5*(gs.length:ℝ)^2) ≤ slotTotal gs f ∅/chainTotal gs w f := by
  have hz := slotTotal_pos gs f hf ∅ hgs
  have hΛ := chainTotal_pos gs hgs hcover w f hf hw
  have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  apply (div_le_div_iff₀ (by positivity) hΛ).mpr
  simpa only [one_mul,mul_one,mul_comm] using chainTotal_le gs hgs hne hcover w f hf hupper
end SamplingObservables

open Set

section PairedReduction
variable {α β : Type*}

lemma sum_eRank (M : Matroid α) (N : Matroid β) :
    (M.sum N).eRank = M.eRank + N.eRank := by
  obtain ⟨B,hB⟩ := M.exists_isBase
  obtain ⟨C,hC⟩ := N.exists_isBase
  have hBC : (M.sum N).IsBase (Sum.inl '' B ∪ Sum.inr '' C) := by
    rw [Matroid.sum_isBase_iff]
    simpa [Set.preimage_image_eq _ Sum.inl_injective,
      Set.preimage_image_eq _ Sum.inr_injective] using And.intro hB hC
  rw [← hBC.encard_eq_eRank, Set.encard_union_eq,
    Set.InjOn.encard_image, Set.InjOn.encard_image,
    hB.encard_eq_eRank, hC.encard_eq_eRank]
  · exact Sum.inr_injective.injOn
  · exact Sum.inl_injective.injOn
  · exact Set.disjoint_image_inl_image_inr

lemma paired_ground (M₁ M₂ : Matroid α) (h₁ : M₁.E = Set.univ)
    (h₂ : M₂.E = Set.univ) : (pairedMatroid M₁ M₂).E = Set.univ := by
  ext x
  cases x <;> simp [pairedMatroid, h₁, h₂]

lemma transversal_isBase_iff (M₁ M₂ : Matroid α) (h₂ : M₂.E = Set.univ)
    (A : Set α) :
    (pairedMatroid M₁ M₂).IsBase (transversal A) ↔ M₁.IsBase A ∧ M₂.IsBase A := by
  simp only [pairedMatroid, Matroid.sum_isBase_iff, preimage_inl_transversal,
    preimage_inr_transversal, Matroid.dual_isBase_iff', h₂,
    ← Set.compl_eq_univ_sdiff, compl_compl, Set.subset_univ, and_true]

lemma paired_eRank [Fintype α] (M₁ M₂ : Matroid α) (h₂ : M₂.E = Set.univ)
    (hr : M₁.eRank = M₂.eRank) :
    (pairedMatroid M₁ M₂).eRank = (Fintype.card α : ℕ∞) := by
  rw [pairedMatroid, sum_eRank,hr, M₂.eRank_add_eRank_dual,h₂,
    Set.encard_univ, ENat.card_eq_coe_fintype_card]

lemma transversal_encard [Fintype α] (A : Set α) :
    (transversal A).encard = (Fintype.card α : ℕ∞) := by
  rw [transversal, Set.encard_union_eq,
    Set.InjOn.encard_image, Set.InjOn.encard_image,
    ← Set.encard_union_eq disjoint_compl_right, union_compl_self, Set.encard_univ,
    ENat.card_eq_coe_fintype_card]
  · exact Sum.inr_injective.injOn
  · exact Sum.inl_injective.injOn
  · exact Set.disjoint_image_inl_image_inr

end PairedReduction

open scoped BigOperators Classical

section CoefficientDrift
variable {X : Type*} [Fintype X]

lemma deficiencyPartition_pos [Nonempty X] (d : X → ℕ) (q : ℝ) (hq : 0<q) :
    0 < deficiencyPartition d q := Finset.sum_pos (fun _ _ => pow_pos hq _) Finset.univ_nonempty
end CoefficientDrift

lemma relative_product_lower (a : ℕ → ℝ) (L : ℕ) (η : ℝ) (hη0 : 0≤η) (hη1 : η≤1/2)
    (ha : ∀ j<L,(1-η)/(1+η)≤a j) :
    1-2*(L:ℝ)*η ≤ ∏ j ∈ Finset.range L,a j := by
  have hdiv : 1-2*η ≤ (1-η)/(1+η) := by
    rw [le_div_iff₀ (by linarith : 0<1+η)]
    nlinarith [sq_nonneg η]
  have hp : (1-2*η)^L ≤ ∏ j ∈ Finset.range L,a j := by
    have he : (1-2*η)^L = ∏ _j ∈ Finset.range L,(1-2*η) := by simp
    rw [he]
    apply Finset.prod_le_prod
    · intro j _; linarith
    · intro j hj; exact hdiv.trans (ha j (Finset.mem_range.mp hj))
  have hb := one_add_mul_le_pow (a := -2*η) (by linarith) L
  have he : (1+(-2*η))^L=(1-2*η)^L := by congr 1; ring
  rw [he] at hb
  nlinarith

lemma product_accuracy (a : ℕ → ℝ) (ε : ℝ) (L : ℕ) (hε0 : 0<ε) (hε1 : ε<1)
    (ha : ∀ j<L,(1-annealTolerance ε L)/(1+annealTolerance ε L)≤a j ∧
      a j≤(1+annealTolerance ε L)/(1-annealTolerance ε L)) :
    1-ε/4 ≤ ∏ j ∈ Finset.range L,a j ∧ ∏ j ∈ Finset.range L,a j≤1+ε/4 := by
  let η := annealTolerance ε L
  have hL : 0 ≤ (L:ℝ) := Nat.cast_nonneg _
  have hden : 0<32*((L:ℝ)+1) := by positivity
  have hη0 : 0 < η := div_pos hε0 hden
  have hη1 : η < 1/32 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hη2 : 2*(L:ℝ)*η ≤ ε/16 := by
    dsimp only [η,annealTolerance]
    rw [← mul_div_assoc,div_le_iff₀ hden]
    nlinarith
  have hlo := relative_product_lower a L η hη0.le (by linarith) (fun j hj => (ha j hj).1)
  have hap : ∀ j<L,0<a j := by
    intro j hj
    have hh := (ha j hj).1
    exact lt_of_lt_of_le (div_pos (by linarith) (by linarith)) hh
  have hainv : ∀ j<L,(1-η)/(1+η) ≤ (a j)⁻¹ := by
    intro j hj
    rw [inv_eq_one_div,le_div_iff₀ (hap j hj)]
    have hu := (le_div_iff₀ (show 0<1-η by linarith)).mp (ha j hj).2
    rw [div_mul_eq_mul_div,div_le_iff₀ (by linarith : 0<1+η)]
    nlinarith
  have hinv := relative_product_lower (fun j => (a j)⁻¹) L η hη0.le (by linarith) hainv
  rw [Finset.prod_inv_distrib] at hinv
  have hp : 0 < ∏ j ∈ Finset.range L,a j := Finset.prod_pos (fun j hj => hap j (Finset.mem_range.mp hj))
  have hlow : 1-ε/16 ≤ (∏ j ∈ Finset.range L,a j)⁻¹ := by linarith
  have hmul := (le_div_iff₀ hp).mp (show 1-ε/16 ≤ 1/(∏ j ∈ Finset.range L,a j) by simpa only [one_div] using hlow)
  constructor
  · linarith
  · nlinarith [mul_nonneg (show 0≤ε by linarith) (show 0≤1-ε by linarith)]

lemma final_estimate_accuracy (ε Z C Zhat : ℝ) (hε0 : 0<ε) (hε1 : ε<1) (hZ : 0≤Z)
    (hC : Z≤C ∧ C≤(1+ε/10)*Z)
    (hhat : (1-ε/4)*C≤Zhat ∧ Zhat≤(1+ε/4)*C) :
    (1-ε)*Z≤Zhat ∧ Zhat≤(1+ε)*Z := by
  have hl := mul_le_mul_of_nonneg_left hC.1 (show 0≤1-ε/4 by linarith)
  have hu := mul_le_mul_of_nonneg_left hC.2 (show 0≤1+ε/4 by linarith)
  have he : (1+ε/4)*(1+ε/10)≤1+ε := by nlinarith [sq_nonneg ε]
  have he' := mul_le_mul_of_nonneg_right he hZ
  constructor <;> nlinarith [mul_nonneg hε0.le hZ]

section Contamination
variable {X : Type*} [Fintype X]
lemma partition_contamination (d : X → ℕ) (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) :
    (zeroDeficiencyCount d:ℝ) ≤ deficiencyPartition d q ∧
      deficiencyPartition d q ≤ (zeroDeficiencyCount d:ℝ)+(Fintype.card X:ℝ)*q := by
  have hcount : (zeroDeficiencyCount d:ℝ) = ∑ x,if d x=0 then (1:ℝ) else 0 := by
    simp [zeroDeficiencyCount,Finset.sum_boole]
  rw [hcount]
  constructor
  · apply Finset.sum_le_sum
    intro x _
    by_cases h : d x=0
    · simp [h]
    · simp [h,pow_nonneg hq0]
  · have hs : ∀ x,q^(d x) ≤ (if d x=0 then 1 else 0)+q := by
      intro x
      by_cases h : d x=0
      · simp [h,hq0]
      · simp only [h,ite_false,zero_add]
        have hd : 1≤d x := Nat.one_le_iff_ne_zero.mpr h
        simpa using pow_le_pow_of_le_one hq0 hq1 hd
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hs x)
    simpa [deficiencyPartition,Finset.sum_add_distrib] using hh
end Contamination

open scoped BigOperators Classical
lemma subsetDeficiency_zero {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (A : Set (Fin n)) :
    subsetDeficiency M₁ M₂ A=0 ↔ M₁.IsBase A ∧ M₂.IsBase A := by
  have hR : (pairedMatroid M₁ M₂).eRank=(n:ℕ∞) := by simpa using paired_eRank M₁ M₂ hE₂ hr
  have hk : ((pairedMatroid M₁ M₂).eRk (transversal A)).toNat≤n :=
    ENat.toNat_le_of_le_natCast (by rw [← hR]; exact Matroid.eRk_le_eRank _ _)
  rw [← transversal_isBase_iff M₁ M₂ hE₂ A]
  constructor
  · intro hd
    have hn : ((pairedMatroid M₁ M₂).eRk (transversal A)).toNat=n := by unfold subsetDeficiency at hd; omega
    have he : (pairedMatroid M₁ M₂).eRk (transversal A)=(n:ℕ∞) := by
      calc
        _ = (((pairedMatroid M₁ M₂).eRk (transversal A)).toNat:ℕ∞) :=
          (ENat.natCast_toNat (Matroid.isRkFinite_set _ _).eRk_lt_top.ne).symm
        _ = _ := congrArg (fun k : ℕ => (k:ℕ∞)) hn
    have hi : (pairedMatroid M₁ M₂).Indep (transversal A) := by
      apply (Matroid.indep_iff_eRk_eq_encard_of_finite (Set.toFinite _)).mpr
      rw [he,transversal_encard,Fintype.card_fin]
    exact hi.isBase_of_eRk_ge (Set.toFinite _) (by rw [he,hR])
  · intro h
    unfold subsetDeficiency
    rw [h.eRk_eq_eRank,hR,ENat.toNat_natCast,Nat.sub_self]

lemma zeroDeficiency_eq_commonBaseCount {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) :
    zeroDeficiencyCount (subsetDeficiency M₁ M₂)=commonBaseCount M₁ M₂ := by
  have hp : (fun A => subsetDeficiency M₁ M₂ A=0) = (fun A => M₁.IsBase A ∧ M₂.IsBase A) :=
    funext (fun A => propext (subsetDeficiency_zero M₁ M₂ hE₂ hr A))
  unfold zeroDeficiencyCount commonBaseCount
  rw [← Fintype.card_subtype,← Nat.card_eq_fintype_card]
  calc
    _ = Nat.card {A : Set (Fin n) // M₁.IsBase A ∧ M₂.IsBase A} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun A => subsetDeficiency_zero M₁ M₂ hE₂ hr A))
    _ = _ := Nat.card_congr (commonSetFinsetEquiv M₁ M₂)

lemma plainPartition_eq_subsets {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (q : ℝ) :
    slotTotal (pairedSlots n) (matroidWeight (pairedMatroid M₁ M₂) n q) ∅ =
      deficiencyPartition (subsetDeficiency M₁ M₂) q := by
  rw [slotTotal_eq_plain_sum (pairedSlots n) (pairedSlots_fresh n) (pairedSlots_cover n)]
  rw [Finset.sum_subtype (p := PlainState (pairedSlots n)) _ (by intro S; simp)]
  unfold deficiencyPartition
  apply Fintype.sum_equiv (plainEquivSubsets n)
  intro S
  change q^(n-((pairedMatroid M₁ M₂).eRk S.val).toNat)=
    q^(n-((pairedMatroid M₁ M₂).eRk (transversal (Sum.inl ⁻¹' S.val))).toNat)
  rw [← plain_eq_transversal n S.val S.property]

theorem paired_partition_contamination {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) :
    (commonBaseCount M₁ M₂:ℝ) ≤ slotTotal (pairedSlots n) (matroidWeight (pairedMatroid M₁ M₂) n q) ∅ ∧
      slotTotal (pairedSlots n) (matroidWeight (pairedMatroid M₁ M₂) n q) ∅ ≤
        (commonBaseCount M₁ M₂:ℝ)+(2:ℝ)^n*q := by
  have h := partition_contamination (subsetDeficiency M₁ M₂) q hq0 hq1
  rw [zeroDeficiency_eq_commonBaseCount M₁ M₂ hE₂ hr,Fintype.card_set,Fintype.card_fin] at h
  rw [plainPartition_eq_subsets]
  exact_mod_cast h
open scoped BigOperators Classical
lemma annealRho_pow_upper (n : ℕ) (hn : 0<n) : annealRho n^(2*n)≤1/2 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hr0 : 0≤annealRho n := le_trans (by norm_num) (annealRho_bounds n hn).1
  have he : annealRho n≤Real.exp (-1/(2*(n:ℝ))) := by
    have h := Real.add_one_le_exp (-1/(2*(n:ℝ)))
    unfold annealRho
    convert h using 1 <;> first | rfl | ring
  calc
    _ ≤ (Real.exp (-1/(2*(n:ℝ))))^(2*n) := pow_le_pow_left₀ hr0 he _
    _ = Real.exp (-1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    _ ≤ 1/2 := by
      rw [Real.exp_neg]
      have h2 : (2:ℝ)≤Real.exp 1 := by nlinarith [Real.add_one_le_exp (1:ℝ)]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h2
lemma anneal_final_bounds (n b : ℕ) (hn : 0<n) :
    (1/2:ℝ)^annealLength n b≤annealRho n^annealLength n b ∧
      annealRho n^annealLength n b≤(1/2:ℝ)^(n+b) := by
  constructor
  · exact pow_le_pow_left₀ (by norm_num) (annealRho_bounds n hn).1 _
  · unfold annealLength
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (le_trans (by norm_num) (annealRho_bounds n hn).1) _)
      (annealRho_pow_upper n hn) _
lemma anneal_final_contamination (n b : ℕ) (hn : 0<n) (ε : ℝ) (hb : (1/2:ℝ)^b≤ε/10) :
    (2:ℝ)^n*(annealRho n^annealLength n b)≤ε/10 := by
  calc
    _ ≤ (2:ℝ)^n*((1/2:ℝ)^(n+b)) := mul_le_mul_of_nonneg_left (anneal_final_bounds n b hn).2 (by positivity)
    _ = (1/2:ℝ)^b := by rw [pow_add,← mul_assoc,← mul_pow]; norm_num
    _ ≤ _ := hb
lemma partition_le_card {X : Type*} [Fintype X] (d : X → ℕ) (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) :
    deficiencyPartition d q≤Fintype.card X := by
  calc
    _ ≤ ∑ _ : X,(1:ℝ) := Finset.sum_le_sum (fun x _ => pow_le_one₀ hq0 hq1)
    _ = _ := by simp

lemma anneal_minimum_mass {X : Type*} [Fintype X] [Nonempty X]
    (n L j : ℕ) (hn : 0<n) (hj : j≤L) (hcard : Fintype.card X=2^n)
    (d : X → ℕ) (hd : ∀ x,d x≤n) (x : X) :
    (1/2:ℝ)^(n*(L+1))≤(annealRho n^j)^(d x)/deficiencyPartition d (annealRho n^j) := by
  have hr := annealRho_bounds n hn
  have hr0 : 0<annealRho n := lt_of_lt_of_le (by norm_num) hr.1
  have hq0 : 0<annealRho n^j := pow_pos hr0 _
  have hq1 : annealRho n^j≤1 := pow_le_one₀ hr0.le hr.2.le
  have hf : (1/2:ℝ)^(n*L)≤(annealRho n^j)^(d x) := by
    calc
      _ = ((1/2:ℝ)^L)^n := by simp only [← pow_mul,Nat.mul_comm]
      _ ≤ (annealRho n^L)^n := pow_le_pow_left₀ (by positivity)
        (pow_le_pow_left₀ (by norm_num) hr.1 L) _
      _ ≤ (annealRho n^j)^n := pow_le_pow_left₀ (by positivity)
        (pow_le_pow_of_le_one hr0.le hr.2.le hj) _
      _ ≤ _ := pow_le_pow_of_le_one hq0.le hq1 (hd x)
  have hZ := deficiencyPartition_pos d _ hq0
  calc
    _ = ((1/2:ℝ)^(n*L))/(2:ℝ)^n := by
      rw [Nat.mul_add,Nat.mul_one,pow_add]
      simp [inv_pow,div_eq_mul_inv]
    _ ≤ ((annealRho n^j)^(d x))/(2:ℝ)^n := div_le_div_of_nonneg_right hf (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hZ (by
      have h := partition_le_card d (annealRho n^j) hq0.le hq1
      rw [hcard] at h
      exact_mod_cast h)
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
lemma kernel_power_action (k : ℕ) (f : X → ℝ) (x : X) :
    ∑ y,(C.kernel.power k).P x y*f y=C.iterate k f x := by
  induction k generalizing f with
  | zero => simp [FiniteKernel.power,FiniteKernel.identity]
  | succ k ih =>
    change (∑ y,(∑ z,(C.kernel.power k).P x z*C.P z y)*f y)=_
    simp_rw [Finset.sum_mul,mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    change (∑ z,(C.kernel.power k).P x z*C.apply f z)=_
    rw [ih]
    exact congrFun (Function.iterate_succ_apply C.apply k f).symm x
lemma kernel_power_density (k : ℕ) (x y : X) :
    (C.kernel.power k).P x y/C.π y=C.iterate k (C.pointDensity y) x := by
  rw [← C.kernel_power_action]
  simp [pointDensity,div_eq_mul_inv]
lemma kernel_point_mixing (K m : ℝ) (hK : 1≤K) (hm : 0 < m) (hπ : ∀ x,m≤C.π x)
    (hp : ∀ f : X → ℝ,C.variance f≤K*C.energy f) (k : ℕ) (x y : X) :
    |(C.kernel.power k).P x y/C.π y-1|≤Real.exp (-(k:ℝ)/K)/m := by
  rw [C.kernel_power_density]
  exact C.point_mixing_exp K m hK hm hπ hp k x y

lemma kernel_power_warm_any (K m e : ℝ) (hK : 1≤K) (hm : 0 < m)
    (hπ : ∀ x,m≤C.π x) (hp : ∀ f : X → ℝ,C.variance f≤K*C.energy f)
    (k : ℕ) (he : Real.exp (-(k:ℝ)/K)/m≤e) (he' : 0≤1+e)
    (ν : X → ℝ) (hν : ∀ x,0≤ν x) (hnorm : ∑ x,ν x≤1) (y : X) :
    (C.kernel.power k).push ν y≤(1+e)*C.π y := by
  have hrow : ∀ x,(C.kernel.power k).P x y≤(1+e)*C.π y := by
    intro x
    have h := (le_abs_self _).trans ((C.kernel_point_mixing K m hK hm hπ hp k x y).trans he)
    apply (div_le_iff₀ (C.positive y)).mp
    linarith
  calc
    _ ≤ ∑ x,ν x*((1+e)*C.π y) := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hrow x) (hν x))
    _ = (∑ x,ν x)*((1+e)*C.π y) := by rw [Finset.sum_mul]
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hnorm (mul_nonneg he' (C.positive y).le)
end FiniteChain

namespace Annealing

lemma restart_exponential (n L : ℕ) (hn : 0<n) :
    Real.exp (-((20*n^4*(n*(L+1)+2):ℕ):ℝ)/(18*(n:ℝ)^4)) /
      ((2:ℝ)^(-((n*(L+1):ℕ):ℤ))) ≤ 1/2 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h2 : (2:ℝ)≤Real.exp 1 := by nlinarith [Real.add_one_le_exp (1:ℝ)]
  have hpow : (2:ℝ)^(n*(L+1))≤Real.exp ((n*(L+1):ℕ):ℝ) := by
    calc
      _ ≤ (Real.exp 1)^(n*(L+1)) := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; simp
  rw [zpow_neg,zpow_natCast,div_inv_eq_mul]
  calc
    _ ≤ Real.exp (-((20*n^4*(n*(L+1)+2):ℕ):ℝ)/(18*(n:ℝ)^4))*
        Real.exp ((n*(L+1):ℕ):ℝ) := mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = Real.exp (-((20*n^4*(n*(L+1)+2):ℕ):ℝ)/(18*(n:ℝ)^4)+((n*(L+1):ℕ):ℝ)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-1) := by
      apply Real.exp_le_exp.mpr
      have heq : -((20*n^4*(n*(L+1)+2):ℕ):ℝ)/(18*(n:ℝ)^4) =
          -(10/9)*((n:ℝ)*(L+1)+2) := by
        push_cast
        field_simp
        ; ring
      rw [heq]
      push_cast
      nlinarith [show 0≤(n:ℝ)*(L+1) by positivity]
    _ ≤ 1/2 := by rw [Real.exp_neg]; simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h2
end Annealing
section ActualAnnealing
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance93 : Fintype Γ] [sectionInstance94 : DecidableEq Γ]

lemma anneal_ratio_mean (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (M : Matroid Γ) (n j : ℕ) (hn : 0<n)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) :
    chainMean gs w (annealWeight M n j)
      (plainObservable gs (fun S => annealRho n^(n-(M.eRk S).toNat))) =
      slotTotal gs (annealWeight M n (j+1)) ∅/chainTotal gs w (annealWeight M n j) := by
  rw [plainObservable_mean gs hgs hcover]
  congr 2
  funext S
  exact (annealWeight_step M n j hn S).symm
lemma anneal_plainPartition (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (M : Matroid Γ) (n j : ℕ) :
    slotTotal gs (annealWeight M n j) ∅=
      deficiencyPartition (fun S : PlainIndex gs => n-(M.eRk S.val.val).toNat) (annealRho n^j) := by
  rw [slotTotal_eq_plain_sum gs hgs hcover]
  symm
  exact plainIndex_sum gs (annealWeight M n j)
lemma actual_trace_minimum (n L j : ℕ) (hn : 0<n) (hj : j ≤ L) (M : Matroid (Fin n ⊕ Fin n))
    (w : ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℝ)
    (hw : ∀ p r,0<w p r) (S : PlainIndex (pairedSlots n)) :
    (1/2:ℝ)^(n*(L+1))  ≤
      (metropolisTrace (pairedSlots n) (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
        w (annealWeight M n j) hw (annealWeight_pos M n j hn)).π S := by
  let := plainIndex_nonempty (pairedSlots n) (pairedSlots_fresh n) (pairedSlots_cover n)
  rw [metropolisTrace_pi,anneal_plainPartition _ (pairedSlots_fresh n) (pairedSlots_cover n)]
  exact anneal_minimum_mass n L j hn hj (plainIndex_card n) (fun S : PlainIndex (pairedSlots n) => n-(M.eRk S.val.val).toNat) (fun _ => Nat.sub_le _ _) S

theorem successful_phase_ratio (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (M : Matroid Γ) (n j : ℕ) (hn : 0<n)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hw : ∀ p r,0<w p r)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1) (l : List (Set Γ))
    (hacc : AccuratePhase gs w (annealWeight M n j)
      (fun S => annealRho n^(n-(M.eRk S).toNat)) η l) :
    (1-η)/(1+η) ≤ empiricalRatio gs (fun S => annealRho n^(n-(M.eRk S).toNat)) l/
      (slotTotal gs (annealWeight M n (j+1)) ∅/slotTotal gs (annealWeight M n j) ∅) ∧
    empiricalRatio gs (fun S => annealRho n^(n-(M.eRk S).toNat)) l/
      (slotTotal gs (annealWeight M n (j+1)) ∅/slotTotal gs (annealWeight M n j) ∅) ≤ (1+η)/(1-η) := by
  let f := annealWeight M n j
  let g := fun S => annealRho n^(n-(M.eRk S).toNat)
  have hΛ := chainTotal_pos gs hgs hcover w f (annealWeight_pos M n j hn) hw
  have hp0 : 0<chainMean gs w f (plainObservable gs (fun _ => 1)) := by
    rw [plain_probability_mean gs hgs hcover]
    exact div_pos (slotTotal_pos gs f (annealWeight_pos M n j hn) ∅ hgs) hΛ
  have hu : 0<chainMean gs w f (plainObservable gs g) := by
    rw [anneal_ratio_mean gs hgs hcover M n j hn]
    exact div_pos (slotTotal_pos gs _ (annealWeight_pos M n (j+1) hn) ∅ hgs) hΛ
  have he : chainMean gs w f (plainObservable gs g)/chainMean gs w f (plainObservable gs (fun _ => 1)) =
      slotTotal gs (annealWeight M n (j+1)) ∅/slotTotal gs (annealWeight M n j) ∅ := by
    rw [anneal_ratio_mean gs hgs hcover M n j hn,plain_probability_mean gs hgs hcover]
    dsimp only [f] at hΛ ⊢
    field_simp [hΛ.ne']
  have h := estimated_ratio_bounds η _ _ _ _ hη0 hη1 hp0 hu
    (accurate_plain gs w f g η l hacc) (relative_error_bounds _ _ _ (hacc (.inr ())))
  rw [he] at h
  exact h.2
end ActualAnnealing
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
lemma capped_power_submass (K : FiniteKernel X X) (hK : ∀ x y,K.P x y ≤ C.P x y)
    (ν : X → ℝ) (hν : ∀ x,0 ≤ ν x) (U e : ℝ) (hwarm : ∀ x,ν x ≤ U*C.π x)
    (hloss : ∀ a : X → ℝ,(∀ x,0 ≤ a x) → (∀ x,a x ≤ U*C.π x) →
      (∑ x,a x*(1-∑ y,K.P x y)) ≤ e) (T : ℕ) :
    (∑ x,ν x)-(∑ x,(K.power T).push ν x) ≤ (T:ℝ)*e := by
  have hdom := fun n x => K.power_domination C.kernel hK n ν hν x
  induction T with
  | zero => simp [FiniteKernel.power,FiniteKernel.push_identity]
  | succ T ih =>
    have h := K.one_step_defect C.kernel C.stochastic
      ((K.power T).push ν) ((C.kernel.power T).push ν)
      ((K.power T).push_nonneg ν hν) (hdom T)
    have hl := hloss ((C.kernel.power T).push ν)
      ((C.kernel.power T).push_nonneg ν hν) (C.power_warm T ν U hwarm)
    have hm := C.power_push_mass T ν
    have hm' := C.power_push_mass (T+1) ν
    rw [FiniteKernel.power_push_succ] at hm'
    rw [FiniteKernel.power_push_succ]
    rw [hm,hm'] at h
    push_cast
    linarith
variable (A : X → Prop) (Q : KilledKernel (Outside A)) (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
lemma cappedTrace_power_submass [Nonempty (Inside A)] (N T : ℕ) (hN : 0<N)
    (U : ℝ) (ν : Inside A → ℝ) (hν : ∀ x,0 ≤ ν x)
    (hwarm : ∀ x,ν x ≤ U*(C.traceChain A Q hQ).π x) :
    (∑ x,ν x)-(∑ x,((C.cappedTraceKernel A Q hQ N).power T).push ν x) ≤
      (T:ℝ)*(U/C.insideMass A/(N:ℝ)) := by
  apply (C.traceChain A Q hQ).capped_power_submass (C.cappedTraceKernel A Q hQ N)
    (C.cappedTrace_le A Q N) ν hν U _ hwarm
  intro a ha haw
  have h := C.cappedTrace_warm_loss A Q hQ N U a ha haw
  apply (le_div_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)).mpr
  simpa only [cappedTraceKernel,mul_comm] using h
end FiniteChain

section RestartBridge
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
    (hE : M.E=Set.univ) (hR : M.eRank=(n:ℕ∞))
local notation "GS" => pairedSlots n
local notation "W" => (((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℝ)
include hE hR in
lemma actual_trace_poincare (j : ℕ) (w : W) (hw : GoodMultipliers GS (annealWeight M n j) w)
    (H : PlainIndex GS → ℝ) :
    (actualTrace n hn M j w hw.positive).variance H ≤
      18*(n:ℝ)^4*(actualTrace n hn M j w hw.positive).energy H := by
  have hr := annealRho_bounds n hn
  have hp : 0<annealRho n := lt_of_lt_of_le (by norm_num) hr.1
  have hs := matroidWeight_signature M hE n hR (annealRho n^j) (pow_pos hp j) (pow_le_one₀ hp.le hr.2.le)
  simpa only [actualTrace,pairedSlots_length] using
    metropolisTrace_poincare GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
      w (annealWeight M n j) hw.positive (annealWeight_pos M n j hn) hs hw.lower H
include hE hR in
lemma actual_trace_mixing_warm (L j : ℕ) (hj : j ≤ L) (w : W)
    (hw : GoodMultipliers GS (annealWeight M n j) w)
    (ν : PlainIndex GS → ℝ) (hν : ∀ x,0 ≤ ν x) (hnorm : ∑ x,ν x ≤ 1)
    (y : PlainIndex GS) :
    ((actualTrace n hn M j w hw.positive).kernel.power (20*n^4*(n*(L+1)+2))).push ν y ≤
      (3/2)*(actualTrace n hn M j w hw.positive).π y := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hK : (1:ℝ) ≤ 18*(n:ℝ)^4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hn' 4]
  have he := Annealing.restart_exponential n L hn
  have hm : (1/2:ℝ)^(n*(L+1))=(2:ℝ)^(-((n*(L+1):ℕ):ℤ)) := by
    simp only [zpow_neg,zpow_natCast,one_div,inv_pow]
  rw [← hm] at he
  convert (actualTrace n hn M j w hw.positive).kernel_power_warm_any
    (18*(n:ℝ)^4) ((1/2)^(n*(L+1))) (1/2) hK (by positivity)
    (actual_trace_minimum n L j hn hj M w hw.positive)
    (actual_trace_poincare n hn M hE hR j w hw) _ he (by norm_num) ν hν hnorm y using 1 ; norm_num
lemma actual_mu_drift (j : ℕ) (w w' : W) (hw : ∀ p r,0<w p r) (hw' : ∀ p r,0<w' p r)
    (x : PlainIndex GS) :
    (actualTrace n hn M j w hw).π x ≤ 2*(actualTrace n hn M (j+1) w' hw').π x := by
  dsimp only [actualTrace]
  rw [metropolisTrace_pi,metropolisTrace_pi]
  have ha := annealWeight_drift M n j hn x.val.val
  have hb := anneal_slot_drift GS M n j hn ∅
  have hz := slotTotal_pos GS (annealWeight M n j) (annealWeight_pos M n j hn) ∅ (pairedSlots_fresh n)
  have hz' := slotTotal_pos GS (annealWeight M n (j+1)) (annealWeight_pos M n (j+1) hn) ∅ (pairedSlots_fresh n)
  rw [← mul_div_assoc,div_le_div_iff₀ hz hz']
  have hfp := (annealWeight_pos M n j hn x.val.val).le
  nlinarith [mul_nonneg hfp (sub_nonneg.mpr hb.2),mul_nonneg hz.le (sub_nonneg.mpr ha.1)]
end RestartBridge

section ActualRestart
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
local notation "GS" => pairedSlots n
local notation "W" => (((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℝ)
lemma actualCappedTrace_le (j : ℕ) (w : W) (hw : ∀ p r,0<w p r) (cap : ℕ) (x y : PlainIndex GS) :
    (actualCappedTrace n hn M j w hw cap).P x y ≤ (actualTrace n hn M j w hw).P x y := by
  exact FiniteChain.cappedTrace_le _ _ _ cap x y
lemma actual_capped_mixing (hE : M.E=Set.univ) (hR : M.eRank=(n:ℕ∞))
    (L j : ℕ) (hj : j ≤ L) (w : W) (hw : GoodMultipliers GS (annealWeight M n j) w)
    (cap : ℕ) (ν : PlainIndex GS → ℝ) (hν : ∀ x,0 ≤ ν x) (hnorm : ∑ x,ν x ≤ 1)
    (y : PlainIndex GS) :
    ((actualCappedTrace n hn M j w hw.positive cap).power (20*n^4*(n*(L+1)+2))).push ν y ≤
      (3/2)*(actualTrace n hn M j w hw.positive).π y := by
  exact ((actualCappedTrace n hn M j w hw.positive cap).power_domination
    (actualTrace n hn M j w hw.positive).kernel (actualCappedTrace_le n hn M j w hw.positive cap)
    _ ν hν y).trans (actual_trace_mixing_warm n hn M hE hR L j hj w hw ν hν hnorm y)
lemma actual_capped_loss (j : ℕ) (w : W) (hw : GoodMultipliers GS (annealWeight M n j) w)
    (cap T : ℕ) (hcap : 0<cap) (ν : PlainIndex GS → ℝ) (hν : ∀ x,0 ≤ ν x)
    (hwarm : ∀ x,ν x ≤ 4*(actualTrace n hn M j w hw.positive).π x) :
    (∑ x,ν x)-(∑ x,((actualCappedTrace n hn M j w hw.positive cap).power T).push ν x) ≤
      (T:ℝ)*(20*(n:ℝ)^2/(cap:ℝ)) := by
  let := plainIndex_nonempty GS (pairedSlots_fresh n) (pairedSlots_cover n)
  let C := metropolisChain GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
    w (annealWeight M n j) hw.positive (annealWeight_pos M n j hn)
  let Q := metropolisKilled GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
    w (annealWeight M n j) hw.positive (annealWeight_pos M n j hn)
  have h := C.cappedTrace_power_submass (plainPredicate GS) Q (by intros; rfl) cap T hcap 4 ν hν hwarm
  change _ ≤ (T:ℝ)*(4/C.insideMass (plainPredicate GS)/(cap:ℝ)) at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hmass := plain_mass_lower GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
    w (annealWeight M n j) hw.positive (annealWeight_pos M n j hn) hw.upper
  simp only [pairedSlots_length] at hmass
  have hm' : 1/(5*(n:ℝ)^2) ≤ C.insideMass (plainPredicate GS) := by
    rw [metropolis_insideMass]; exact hmass
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hp : 0<C.insideMass (plainPredicate GS) := (by positivity : (0:ℝ)<1/(5*(n:ℝ)^2)).trans_le hm'
  apply (div_le_iff₀ hp).mpr
  have hh := (div_le_iff₀ (by positivity : (0:ℝ)<5*(n:ℝ)^2)).mp hm'
  nlinarith
lemma uniformPlain_mass : ∑ x : PlainIndex GS,uniformPlain n x=1 := by
  simp [uniformPlain,plainIndex_card]
lemma uniformPlain_pi (w : W) (hw : ∀ p r,0<w p r) (x : PlainIndex GS) :
    uniformPlain n x=(actualTrace n hn M 0 w hw).π x := by
  rw [actualTrace,metropolisTrace_pi]
  have he : annealWeight M n 0=(fun _ => 1) := by funext S; simp [annealWeight,matroidWeight]
  rw [he,slotTotal_one GS ∅ (pairedSlots_fresh n),pairedSlots_length]
  rfl
lemma restartLaw_nonneg (L cap : ℕ) (w : ℕ → W) (hw : ∀ j p r,0<w j p r)
    (j : ℕ) (x : PlainIndex GS) : 0 ≤ restartLaw n hn M L cap w hw j x := by
  induction j generalizing x with
  | zero => simp only [restartLaw,uniformPlain]; positivity
  | succ j ih => exact FiniteKernel.push_nonneg _ _ ih x
lemma restartLaw_mass_le (L cap : ℕ) (w : ℕ → W) (hw : ∀ j p r,0<w j p r) (j : ℕ) :
    (∑ x,restartLaw n hn M L cap w hw j x) ≤ 1 := by
  induction j with
  | zero => exact (uniformPlain_mass n).le
  | succ j ih => exact (FiniteKernel.push_mass_le _ _ (restartLaw_nonneg n hn M L cap w hw j)).trans ih
lemma restartLaw_warm (hE : M.E=Set.univ) (hR : M.eRank=(n:ℕ∞))
    (L cap : ℕ) (w : ℕ → W) (hw : ∀ j p r,0<w j p r)
    (j : ℕ) (hj : j ≤ L) (hgood : GoodMultipliers GS (annealWeight M n j) (w j))
    (x : PlainIndex GS) :
    restartLaw n hn M L cap w hw j x ≤ 2*(actualTrace n hn M j (w j) (hw j)).π x := by
  cases j with
  | zero =>
    rw [restartLaw,uniformPlain_pi n hn M (w 0) (hw 0)]
    have h := (actualTrace n hn M 0 (w 0) (hw 0)).positive x
    linarith
  | succ j =>
    have h := actual_capped_mixing n hn M hE hR L (j+1) hj (w (j+1)) hgood cap
      (restartLaw n hn M L cap w hw j) (restartLaw_nonneg n hn M L cap w hw j)
      (restartLaw_mass_le n hn M L cap w hw j) x
    change _ ≤ 2*(actualTrace n hn M (j+1) (w (j+1)) (hw (j+1))).π x
    have hp := (actualTrace n hn M (j+1) (w (j+1)) (hw (j+1))).positive x
    exact h.trans (by linarith)
lemma restartLaw_missing_mass (hE : M.E=Set.univ) (hR : M.eRank=(n:ℕ∞))
    (L cap : ℕ) (hcap : 0<cap) (w : ℕ → W) (hw : ∀ j p r,0<w j p r)
    (j : ℕ) (hj : j ≤ L)
    (hgood : ∀ a ≤ j,GoodMultipliers GS (annealWeight M n a) (w a)) :
    1-(∑ x,restartLaw n hn M L cap w hw j x) ≤
      (j:ℝ)*((20*n^4*(n*(L+1)+2):ℕ):ℝ)*(20*(n:ℝ)^2/(cap:ℝ)) := by
  induction j with
  | zero => simp [restartLaw,uniformPlain_mass]
  | succ j ih =>
    have hj' : j ≤ L := by omega
    have hb := ih hj' (fun a ha => hgood a (by omega))
    have hwarm : ∀ x,restartLaw n hn M L cap w hw j x ≤ 4*(actualTrace n hn M (j+1) (w (j+1)) (hw (j+1))).π x := by
      intro x
      have h1 := restartLaw_warm n hn M hE hR L cap w hw j hj' (hgood j (by omega)) x
      have h2 := actual_mu_drift n hn M j (w j) (w (j+1)) (hw j) (hw (j+1)) x
      linarith
    have h := actual_capped_loss n hn M (j+1) (w (j+1)) (hgood (j+1) le_rfl) cap
      (20*n^4*(n*(L+1)+2)) hcap (restartLaw n hn M L cap w hw j)
      (restartLaw_nonneg n hn M L cap w hw j) hwarm
    change 1-(∑ x,(_ : FiniteKernel _ _).push _ x) ≤ _
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith
end ActualRestart
section EstimatorBridge
open scoped BigOperators Classical
variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
lemma product_ratios_telescope (a : ℕ → ℝ) (ha : ∀ j,a j≠0) (L : ℕ) :
    (∏ j ∈ Finset.range L,a (j+1)/a j)=a L/a 0 := by
  induction L with
  | zero => simp [ha]
  | succ L ih => rw [Finset.prod_range_succ,ih]; field_simp [ha L,ha 0]
lemma accurate_phases_product (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (M : Matroid Γ) (n : ℕ) (hn : 0<n)
    (ε : ℝ) (hε0 : 0<ε) (hε1 : ε<1) (L : ℕ)
    (w : ℕ → (Γ × Γ) → (Γ × Γ) → ℝ) (hw : ∀ j p r,0<w j p r)
    (ls : ℕ → List (Set Γ))
    (hacc : ∀ j<L,AccuratePhase gs (w j) (annealWeight M n j)
      (fun S => annealRho n^(n-(M.eRk S).toNat)) (annealTolerance ε L) (ls j)) :
    let Zhat := (2:ℝ)^gs.length * ∏ j ∈ Finset.range L,
      empiricalRatio gs (fun S => annealRho n^(n-(M.eRk S).toNat)) (ls j)
    (1-ε/4)*slotTotal gs (annealWeight M n L) ∅ ≤ Zhat ∧
      Zhat ≤ (1+ε/4)*slotTotal gs (annealWeight M n L) ∅ := by
  let c := fun j => slotTotal gs (annealWeight M n j) ∅
  let R := fun j => empiricalRatio gs (fun S => annealRho n^(n-(M.eRk S).toNat)) (ls j)
  have hc : ∀ j,0<c j := fun j => slotTotal_pos gs _ (annealWeight_pos M n j hn) ∅ hgs
  have ht := product_ratios_telescope c (fun j => (hc j).ne') L
  have he : c 0=(2:ℝ)^gs.length := by
    have hf : annealWeight M n 0=(fun _ => 1) := by funext S; simp [annealWeight,matroidWeight]
    dsimp only [c]; rw [hf,slotTotal_one gs ∅ hgs]
  have hη : 0<annealTolerance ε L ∧ annealTolerance ε L<1/32 := by
    have hd : 0<32*((L:ℝ)+1) := by positivity
    constructor
    · exact div_pos hε0 hd
    · apply (div_lt_iff₀ hd).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hp := product_accuracy (fun j => R j/(c (j+1)/c j)) ε L hε0 hε1
    (fun j hj => successful_phase_ratio gs hgs hcover M n j hn (w j) (hw j)
      (annealTolerance ε L) hη.1.le (by linarith [hη.2]) (ls j) (hacc j hj))
  have hidentity : (∏ j ∈ Finset.range L,R j/(c (j+1)/c j)) =
      ((2:ℝ)^gs.length*(∏ j ∈ Finset.range L,R j))/c L := by
    rw [Finset.prod_div_distrib,ht,he]
    field_simp
  rw [hidentity] at hp
  constructor
  · exact (le_div_iff₀ (hc L)).mp hp.1
  · exact (div_le_iff₀ (hc L)).mp hp.2

theorem actual_estimator_accuracy {n : ℕ} (hn : 0<n) (M₁ M₂ : Matroid (Fin n))
    (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (ε : ℝ) (hε0 : 0<ε) (hε1 : ε<1) (b : ℕ) (hb : (1/2:ℝ)^b ≤ ε/10)
    (hZ : 0<commonBaseCount M₁ M₂)
    (w : ℕ → ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℝ)
    (hw : ∀ j p r,0<w j p r) (ls : ℕ → List (Set (Fin n ⊕ Fin n)))
    (hacc : ∀ j<annealLength n b,AccuratePhase (pairedSlots n) (w j) (annealWeight (pairedMatroid M₁ M₂) n j)
      (fun S => annealRho n^(n-((pairedMatroid M₁ M₂).eRk S).toNat))
      (annealTolerance ε (annealLength n b)) (ls j)) :
    let Zhat := (2:ℝ)^n * ∏ j ∈ Finset.range (annealLength n b),
      empiricalRatio (pairedSlots n) (fun S => annealRho n^(n-((pairedMatroid M₁ M₂).eRk S).toNat)) (ls j)
    (1-ε)*(commonBaseCount M₁ M₂:ℝ) ≤ Zhat ∧ Zhat ≤ (1+ε)*(commonBaseCount M₁ M₂:ℝ) := by
  have hp := accurate_phases_product (pairedSlots n) (pairedSlots_fresh n) (pairedSlots_cover n)
    (pairedMatroid M₁ M₂) n hn ε hε0 hε1 (annealLength n b) w hw ls hacc
  simp only [pairedSlots_length] at hp
  have hrho := annealRho_bounds n hn
  have hq0 : 0 ≤ annealRho n^annealLength n b := pow_nonneg (le_trans (by norm_num) hrho.1) _
  have hq1 : annealRho n^annealLength n b ≤ 1 := pow_le_one₀ (le_trans (by norm_num) hrho.1) hrho.2.le
  have hc := paired_partition_contamination M₁ M₂ hE₂ hr _ hq0 hq1
  have hcont := anneal_final_contamination n b hn ε hb
  have hZ' : (1:ℝ) ≤ commonBaseCount M₁ M₂ := by exact_mod_cast hZ
  apply final_estimate_accuracy ε _ _ _ hε0 hε1 (by positivity) ⟨hc.1,?_⟩ hp
  have hm := mul_le_mul_of_nonneg_left hZ' (show 0 ≤ ε/10 by positivity)
  nlinarith [hc.2]
end EstimatorBridge
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance101 : Fintype X]
universe u

variable (C : FiniteChain X)
lemma sampleMass_nonneg (ν : X → ℝ) (hν : ∀ x,0 ≤ ν x) {k : ℕ} (v : Sample X k) :
    0 ≤ C.sampleMass ν v := by
  induction k generalizing ν with
  | zero => exact hν v
  | succ k ih => exact mul_nonneg (hν _) (ih _ (C.nonnegative _) v.2)
end FiniteChain
section WarmLift
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance102 : Fintype Γ] [sectionInstance103 : DecidableEq Γ]
omit sectionInstance102 sectionInstance103 in
lemma plainLift_nonneg [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (ν : PlainIndex gs → ℝ) (hν : ∀ x,0 ≤ ν x) (S : ChainIndex gs) :
    0 ≤ plainLift gs ν S := by unfold plainLift; split_ifs; exact hν _; rfl
omit sectionInstance103 in
lemma plainLift_mass [DecidableEq Γ] (gs : List (Γ × Γ)) (ν : PlainIndex gs → ℝ) :
    (∑ S,plainLift gs ν S)=∑ S : PlainIndex gs,ν S := by
  have h := Fintype.sum_subtype_add_sum_subtype (plainPredicate gs) (fun S => plainLift gs ν S)
  have ht : ∀ S : PlainIndex gs,plainLift gs ν S.val=ν S := by
    intro S; exact dite_eq_left S.property
  have hf : ∀ S : {S : ChainIndex gs // ¬plainPredicate gs S},plainLift gs ν S.val=0 := by
    intro S; exact dite_eq_right S.property
  simp_rw [ht,hf,Finset.sum_const_zero,add_zero] at h
  exact h.symm
end WarmLift
section ActualHistory
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance105 : Fintype Γ] [DecidableEq Γ]
variable (gs : List (Γ × Γ))
variable (M : Matroid Γ) (n : ℕ) (η : ℝ)
lemma successfulHistory_snoc_iff {X : Type*} (sample : X → List (Set Γ)) (h : List X) (x : X)
    (hh : SuccessfulHistory gs M n η sample h) :
    SuccessfulHistory gs M n η sample (h++[x]) ↔
      AccuratePhase gs (historyWeights gs sample h) (annealWeight M n h.length)
        (fun S => annealRho n^(n-(M.eRk S).toNat)) η (sample x) := by
  constructor
  · intro hs
    have aux : ∀ l,SuccessfulHistory gs M n η sample l → ∀ h x,l=h++[x] →
        AccuratePhase gs (historyWeights gs sample h) (annealWeight M n h.length)
          (fun S => annealRho n^(n-(M.eRk S).toNat)) η (sample x) := by
      intro l hl h x he
      cases hl with
      | nil => simp at he
      | snoc l y hl hy =>
        have hlen := congrArg List.length he
        simp only [List.length_append,List.length_singleton] at hlen
        have hex := List.append_inj he (by omega : l.length=h.length)
        obtain ⟨rfl,hyx⟩ := hex
        have : y=x := by simpa using hyx
        subst y
        exact hy
    exact aux _ hs h x rfl
  · exact SuccessfulHistory.snoc h x hh
end ActualHistory
section ActualPhase
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
local notation "GS" => pairedSlots n
include hn in
lemma restartCap_pos (L : ℕ) : 0<restartCap n L := by unfold restartCap; positivity
include hn in
lemma restartCap_loss (L j : ℕ) (hj : j ≤ L) :
    (j:ℝ)*((20*n^4*(n*(L+1)+2):ℕ):ℝ)*(20*(n:ℝ)^2/(restartCap n L:ℝ)) ≤
      1/(100*(L+1:ℝ)) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hL : 0<(L:ℝ)+1 := by positivity
  have hτ : (0:ℝ)<20*n^4*(n*(L+1)+2) := by positivity
  have hcap : (restartCap n L:ℝ)=2000*((L:ℝ)+1)^2*(n:ℝ)^2*(20*n^4*(n*(L+1)+2)) := by
    simp only [restartCap,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  have hj' : (j:ℝ) ≤ L := by exact_mod_cast hj
  rw [hcap]
  push_cast
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hj') (show 0 ≤ (n:ℝ)^6 by positivity)]
variable (N : ℕ)
include hn in
lemma successfulHistory_stored_good (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/3)
    (h : List (PhaseSample n N)) (hh : SuccessfulHistory GS M n η (observedSets n N) h)
    (j : ℕ) (hj : j ≤ h.length) :
    GoodMultipliers GS (annealWeight M n j) (storedWeights n N h j) := by
  have ht := successfulHistory_good GS M n η (observedSets n N) (pairedSlots_fresh n) (pairedSlots_cover n)
    hn hη0 hη1 (h.take j) (successfulHistory_take GS M n η (observedSets n N) h hh j)
  simpa only [List.length_take,Nat.min_eq_left hj,storedWeights] using ht
variable (L : ℕ)
lemma phaseStart_nonneg (h : List (PhaseSample n N)) (hp : HistoryPositive n N h) (S : ChainIndex GS) :
    0 ≤ phaseStart n hn M N L h hp S :=
  plainLift_nonneg _ _ (restartLaw_nonneg n hn M L _ _ _ _) S
lemma phaseKernel_nonneg (h : List (PhaseSample n N)) (v : PhaseSample n N) :
    0 ≤ phaseKernel n hn M N L h v := by
  unfold phaseKernel; split_ifs with hp
  · exact FiniteChain.sampleMass_nonneg _ _ (phaseStart_nonneg n hn M N L h hp) v
  · rfl
end ActualPhase
section PhaseSuccess
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
    (hE : M.E=Set.univ) (hR : M.eRank=(n:ℕ∞))
local notation "GS" => pairedSlots n
variable (N L : ℕ) (η : ℝ) (hη0 : 0<η) (hη1 : η ≤ 1/3)
include hE hR hη0 hη1 in
lemma phaseStart_mass_lower (h : List (PhaseSample n N))
    (hh : SuccessfulHistory GS M n η (observedSets n N) h) (hj : h.length ≤ L) :
    let hp := successfulHistory_positive n hn M N η hη0.le hη1 h hh
    1-1/(100*(L+1:ℝ)) ≤ ∑ S,phaseStart n hn M N L h hp S := by
  intro hp
  have hm := restartLaw_missing_mass n hn M hE hR L (restartCap n L) (restartCap_pos n hn L)
    (storedWeights n N h) (historyPositive_all n N h hp) h.length hj
    (fun a ha => successfulHistory_stored_good n hn M N η hη0.le hη1 h hh a ha)
  have he := restartCap_loss n hn L h.length hj
  simp only [phaseStart,plainLift_mass]
  linarith
end PhaseSuccess
section HistoryEstimate
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance107 : Fintype Γ] [sectionInstance108 : DecidableEq Γ]
variable {X : Type*} (sample : X → List (Set Γ))
omit sectionInstance107 sectionInstance108 in
lemma historySample_getElem [Fintype Γ] [DecidableEq Γ] (h : List X) (j : ℕ) (hj : j<h.length) :
    historySample sample h j=sample h[j] := by simp [historySample,List.getElem?_eq_getElem hj]
lemma successfulHistory_accurate (gs : List (Γ × Γ)) (M : Matroid Γ) (n : ℕ) (η : ℝ)
    (h : List X) (hh : SuccessfulHistory gs M n η sample h) (j : ℕ) (hj : j<h.length) :
    AccuratePhase gs (historyWeights gs sample (h.take j)) (annealWeight M n j)
      (fun S => annealRho n^(n-(M.eRk S).toNat)) η (historySample sample h j) := by
  have ht := successfulHistory_take gs M n η sample h hh j
  have hs := successfulHistory_take gs M n η sample h hh (j+1)
  rw [List.take_succ_eq_append_getElem hj] at hs
  have ha := (successfulHistory_snoc_iff gs M n η sample (h.take j) h[j] ht).mp hs
  simpa only [List.length_take,Nat.min_eq_left hj.le,historySample_getElem sample h j hj] using ha
end HistoryEstimate
section ActualHistoryEstimate
open scoped BigOperators Classical
variable (n : ℕ) (N L : ℕ) (M : Matroid (Fin n ⊕ Fin n))
lemma historyEstimate_accuracy (hn : 0<n) (M₁ M₂ : Matroid (Fin n))
    (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (ε : ℝ) (hε0 : 0<ε) (hε1 : ε<1) (b : ℕ) (hb : (1/2:ℝ)^b ≤ ε/10)
    (hZ : 0<commonBaseCount M₁ M₂) (h : List (PhaseSample n N))
    (hlen : h.length=annealLength n b)
    (hh : SuccessfulHistory (pairedSlots n) (pairedMatroid M₁ M₂) n
      (annealTolerance ε (annealLength n b)) (observedSets n N) h) :
    (1-ε)*(commonBaseCount M₁ M₂:ℝ) ≤ historyEstimate n N (annealLength n b) (pairedMatroid M₁ M₂) h ∧
      historyEstimate n N (annealLength n b) (pairedMatroid M₁ M₂) h ≤ (1+ε)*(commonBaseCount M₁ M₂:ℝ) := by
  have hη0 : 0<annealTolerance ε (annealLength n b) := by unfold annealTolerance; positivity
  have hη1 : annealTolerance ε (annealLength n b) ≤ 1/3 := by
    unfold annealTolerance
    apply (div_le_iff₀ (by positivity : (0:ℝ)<32*((annealLength n b:ℝ)+1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (annealLength n b)]
  have hp := successfulHistory_positive n hn (pairedMatroid M₁ M₂) N _ hη0.le hη1 h hh
  exact actual_estimator_accuracy hn M₁ M₂ hE₂ hr ε hε0 hε1 b hb hZ
    (storedWeights n N h) (historyPositive_all n N h hp) (historySample (observedSets n N) h)
    (fun j hj => successfulHistory_accurate (observedSets n N) (pairedSlots n) (pairedMatroid M₁ M₂)
      n (annealTolerance ε (annealLength n b)) h hh j (by omega))
end ActualHistoryEstimate
section WitnessRestart
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n))
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n
local notation "W" => (((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℝ)
include hn in
lemma warm_witness_bad_mass (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (ε : ℝ) (_ : 0<ε) (b : ℕ) (hb : (1/2:ℝ)^b ≤ ε/10)
    (hZ : 0<commonBaseCount M₁ M₂) (w : W) (hw : ∀ p r,0<w p r)
    (ν : PlainIndex GS → ℝ)
    (hwarm : ∀ x,ν x ≤ 2*(actualTrace n hn K (annealLength n b) w hw).π x) :
    (∑ x,if Witnessed n M₁ M₂ x then 0 else ν x) ≤ ε/5 := by
  let q := annealRho n^annealLength n b
  have hρ := annealRho_bounds n hn
  have hq0 : 0 ≤ q := pow_nonneg (le_trans (by norm_num) hρ.1) _
  have hq1 : q ≤ 1 := pow_le_one₀ (le_trans (by norm_num) hρ.1) hρ.2.le
  have hc := (paired_partition_contamination M₁ M₂ hE₂ hr q hq0 hq1).1
  have hz : (1:ℝ) ≤ commonBaseCount M₁ M₂ := by exact_mod_cast hZ
  have hc1 : (1:ℝ) ≤ slotTotal GS (annealWeight K n (annealLength n b)) ∅ := hz.trans hc
  have hlocal : ∀ x : PlainIndex GS,(if Witnessed n M₁ M₂ x then 0 else ν x) ≤ 2*q := by
    intro x
    split_ifs with hx
    · positivity
    · have hd : 1 ≤ n-((K).eRk x.val.val).toNat := by unfold Witnessed at hx; omega
      have hpow : q^(n-((K).eRk x.val.val).toNat) ≤ q := by
        simpa using pow_le_pow_of_le_one hq0 hq1 hd
      have hmu : (actualTrace n hn K (annealLength n b) w hw).π x ≤ q := by
        rw [actualTrace,metropolisTrace_pi]
        exact (div_le_self (pow_nonneg hq0 _) hc1).trans hpow
      exact (hwarm x).trans (by linarith)
  have hs := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => hlocal x)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,plainIndex_card,Nat.cast_pow,Nat.cast_ofNat] at hs
  have he := anneal_final_contamination n b hn ε hb
  dsimp only [q] at hs
  linarith
variable (N : ℕ)
lemma witnessKernel_nonneg (L : ℕ) (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    0 ≤ witnessKernel n hn M₁ M₂ N L h x := by
  unfold witnessKernel
  split_ifs with hp
  · exact restartLaw_nonneg n hn K L _ _ _ _ x
  · rfl
include hn in
lemma witnessKernel_good_mass (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (ε : ℝ) (hε0 : 0<ε) (hε1 : ε<1) (b : ℕ) (hb : (1/2:ℝ)^b ≤ ε/10)
    (hZ : 0<commonBaseCount M₁ M₂) (h : List (PhaseSample n N))
    (hlen : h.length=annealLength n b)
    (hh : SuccessfulHistory GS K n (annealTolerance ε (annealLength n b)) (observedSets n N) h) :
    79/100 ≤ ∑ x,if Witnessed n M₁ M₂ x then witnessKernel n hn M₁ M₂ N (annealLength n b) h x else 0 := by
  let L := annealLength n b
  let η := annealTolerance ε L
  have hη0 : 0<η := by dsimp only [η,annealTolerance]; positivity
  have hη1 : η ≤ 1/3 := by
    dsimp only [η,annealTolerance]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<32*((L:ℝ)+1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hE := paired_ground M₁ M₂ hE₁ hE₂
  have hR : (K).eRank=(n:ℕ∞) := by simpa using paired_eRank M₁ M₂ hE₂ hr
  let hp := successfulHistory_positive n hn K N η hη0.le hη1 h hh
  have hg := successfulHistory_stored_good n hn K N η hη0.le hη1 h hh h.length le_rfl
  have hW := restartLaw_warm n hn K hE hR L (restartCap n L) (storedWeights n N h)
    (historyPositive_all n N h hp) h.length (by rw [hlen]) hg
  have hbad := warm_witness_bad_mass n hn M₁ M₂ hE₂ hr ε hε0 b hb hZ
    (storedWeights n N h h.length) (hp h.length le_rfl)
    (witnessKernel n hn M₁ M₂ N L h) (by
      intro x
      simpa only [witnessKernel,dite_eq_left hp,hlen] using hW x)
  have hm := phaseStart_mass_lower n hn K hE hR N L η hη0 hη1 h hh (by rw [hlen])
  simp only [phaseStart,plainLift_mass] at hm
  have hsplit : (∑ x,if Witnessed n M₁ M₂ x then witnessKernel n hn M₁ M₂ N L h x else 0)+
      (∑ x,if Witnessed n M₁ M₂ x then 0 else witnessKernel n hn M₁ M₂ N L h x)=
      ∑ x,witnessKernel n hn M₁ M₂ N L h x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  have hsmall : 1/(100*(L+1:ℝ)) ≤ 1/100 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(L+1:ℝ))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hm' : 99/100 ≤ ∑ x,witnessKernel n hn M₁ M₂ N L h x := by
    simp only [witnessKernel,dite_eq_left hp]
    linarith
  change 79/100 ≤ ∑ x,if Witnessed n M₁ M₂ x then witnessKernel n hn M₁ M₂ N L h x else 0
  linarith
end WitnessRestart
namespace FiniteExperiment
open scoped BigOperators Classical
variable {X : Type*} [Fintype X]
lemma expect_mul_left (K : List X → X → ℝ) (r : ℝ) (φ : List X → ℝ) (t : ℕ) (h : List X) :
    expect K t h (fun l => r*φ l)=r*expect K t h φ := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [expect,ih]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
lemma expect_mono_length (K : List X → X → ℝ) (hK : ∀ h x,0 ≤ K h x)
    (φ ψ : List X → ℝ) (t : ℕ) (h : List X)
    (hh : ∀ l,l.length=h.length+t → φ l ≤ ψ l) :
    expect K t h φ ≤ expect K t h ψ := by
  induction t generalizing h with
  | zero => exact hh h (by simp)
  | succ t ih =>
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hK h x)
    apply ih
    intro l hl
    apply hh l
    simp only [List.length_append,List.length_singleton] at hl
    omega
end FiniteExperiment
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n

theorem real_annealing_success (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (hr : M₁.eRank=M₂.eRank) (ε : ℝ) (hε0 : 0<ε) (hε1 : ε<1)
    (b : ℕ) (hb : (1/2:ℝ)^b ≤ ε/10) (hZ : 0<commonBaseCount M₁ M₂)
    (hN : (10:ℝ)^10*(annealLength n b+1)*n^14/(annealTolerance ε (annealLength n b))^2 ≤ N) :
    3/4 ≤ actualRealSuccess n hn M₁ M₂ N (annealLength n b) ε := by
  let L := annealLength n b
  let η := annealTolerance ε L
  have hη0 : 0<η := by dsimp only [η,annealTolerance]; positivity
  have hη1 : η ≤ 1/3 := by
    dsimp only [η,annealTolerance]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<32*((L:ℝ)+1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hE := paired_ground M₁ M₂ hE₁ hE₂
  have hR : (K).eRank=(n:ℕ∞) := by simpa using paired_eRank M₁ M₂ hE₂ hr
  let Good := SuccessfulHistory GS K n η (observedSets n N)
  have hmain := actual_history_success n hn K hE hR N L η hη0 hη1 hN
  have hmono := FiniteExperiment.expect_mono_length (phaseKernel n hn K N L)
    (phaseKernel_nonneg n hn K N L)
    (fun h => (79/100)*(if Good h then 1 else 0))
    (fun h => ∑ x,if (1-ε)*(commonBaseCount M₁ M₂:ℝ) ≤ guardedEstimate n M₁ M₂ N L h x ∧
      guardedEstimate n M₁ M₂ N L h x ≤ (1+ε)*(commonBaseCount M₁ M₂:ℝ)
      then witnessKernel n hn M₁ M₂ N L h x else 0) L [] (by
      intro h hlen
      have hlen' : h.length=L := by simpa using hlen
      by_cases hh : Good h
      · simp only [ite_eq_left hh,mul_one]
        have he := historyEstimate_accuracy n N hn M₁ M₂ hE₂ hr ε hε0 hε1 b hb hZ h hlen' hh
        apply (witnessKernel_good_mass n hn M₁ M₂ N hE₁ hE₂ hr ε hε0 hε1 b hb hZ h hlen' hh).trans
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : Witnessed n M₁ M₂ x
        · simp only [guardedEstimate,ite_eq_left hx]
          rw [ite_eq_left he]
        · simp only [ite_eq_right hx]
          split_ifs
          · exact witnessKernel_nonneg n hn M₁ M₂ N L h x
          · rfl
      · simp only [ite_eq_right hh,mul_zero]
        exact Finset.sum_nonneg (fun x _ => by
          split_ifs
          · exact witnessKernel_nonneg n hn M₁ M₂ N L h x
          · rfl))
  rw [FiniteExperiment.expect_mul_left] at hmono
  change 3/4 ≤ actualRealSuccess n hn M₁ M₂ N L ε
  apply le_trans _ hmono
  have h := mul_le_mul_of_nonneg_left hmain (by norm_num : (0:ℝ) ≤ 79/100)
  norm_num at h ⊢
  exact le_trans (by norm_num) h

end

section

open scoped BigOperators Classical
lemma uniformAverage_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : uniformAverage (fun x => f (e x))=uniformAverage f := by
  rw [uniformAverage,uniformAverage,e.sum_comp,Fintype.card_congr e]
lemma uniformAverage_const {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) :
    uniformAverage (fun _ : X => r)=r := by
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  simp [uniformAverage,h]
lemma uniformAverage_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    uniformAverage (fun x => f x+g x)=uniformAverage f+uniformAverage g := by
  simp [uniformAverage,Finset.sum_add_distrib,add_div]
lemma acceptedCard (v T : ℕ) (hv : v≤T) :
    Fintype.card {x : Fin T // x.val < v}=v := by
  let e : {x : Fin T // x.val < v} ≃ Fin v :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      invFun := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hv⟩,x.isLt⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  simpa using Fintype.card_congr e
lemma sum_ite_count {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] (r : ℝ) :
    (∑ x,if p x then r else 0)=(Fintype.card {x // p x}:ℝ)*r := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  congr 1
  exact_mod_cast (Fintype.card_subtype p).symm
namespace DrawTree

open scoped BigOperators Classical
variable {A B : Type*}
lemma expectation_bind (t : DrawTree A) (k : A → DrawTree B) (φ : B → ℝ) :
    (t.bind k).expectation φ=t.expectation (fun a => (k a).expectation φ) := by
  induction t with
  | leaf a => rfl
  | draw v f ih => simp only [bind,expectation,ih]
lemma expectation_map (t : DrawTree A) (f : A → B) (φ : B → ℝ) :
    (t.map f).expectation φ=t.expectation (fun a => φ (f a)) := by
  rw [map,expectation_bind]; rfl
lemma rationalCoin_expectation (a v : ℕ) (ha : a≤v+1) (φ : Bool → ℝ) :
    (rationalCoin a v).expectation φ=
      (a:ℝ)/(v+1:ℕ)*φ true+(1-(a:ℝ)/(v+1:ℕ))*φ false := by
  change uniformAverage (fun i : Fin (v+1) => φ (decide (i.val<a)))=_
  have he : (fun i : Fin (v+1) => φ (decide (i.val<a)))=
      fun i => φ false+if i.val<a then φ true-φ false else 0 := by
    funext i; by_cases h : i.val<a <;> simp [h]
  rw [he,uniformAverage_add,uniformAverage_const]
  unfold uniformAverage
  rw [sum_ite_count,acceptedCard a (v+1) ha,Fintype.card_fin]
  have hv : ((v+1:ℕ):ℝ)≠0 := by positivity
  field_simp
  ; ring
lemma bernoulli_expectation (p : ℚ) (hp0 : 0≤p) (hp1 : p≤1) (φ : Bool → ℝ) :
    (bernoulli p).expectation φ=(p:ℝ)*φ true+(1-(p:ℝ))*φ false := by
  have hd : p.den-1+1=p.den := by have h := p.den_pos; omega
  have hn : (p.num.natAbs:ℤ)=p.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hp0)
  have hnr : (p.num.natAbs:ℝ)=(p.num:ℝ) := by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) hn
  have he : (p.num.natAbs:ℝ)/(p.den:ℝ)=(p:ℝ) := by rw [hnr,Rat.cast_def]
  have ha : p.num.natAbs≤p.den := by
    have hd' : (0:ℝ)<p.den := by exact_mod_cast p.den_pos
    have hp1' : (p:ℝ)≤1 := by exact_mod_cast hp1
    have hh' : (p.num.natAbs:ℝ)≤p.den := by
      have h := (div_le_iff₀ hd').mp (he.symm ▸ hp1')
      simpa only [one_mul] using h
    exact_mod_cast hh'
  unfold bernoulli
  rw [rationalCoin_expectation _ _ (by omega),hd,he]
end DrawTree

section MetropolisSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance110 : Fintype Γ] [sectionInstance111 : DecidableEq Γ]
omit sectionInstance110 in
lemma exchangedSet_adjacent [Fintype Γ] (S : Set Γ) (a : ExchangeChoice S) :
    ExchangeAdjacent S (exchangedSet S a) := by
  refine ⟨S\{a.1.val},a.1.val,a.2.val,?_,?_,?_,?_,rfl⟩
  · intro he
    exact a.2.property (he ▸ a.1.property)
  · simp
  · intro hx; exact a.2.property hx.1
  · ext x
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · intro hx; by_cases he : x=a.1.val
      · exact Or.inl he
      · exact Or.inr ⟨hx,he⟩
    · rintro (rfl|⟨hx,_⟩)
      · exact a.1.property
      · exact hx
omit sectionInstance110 in
lemma exchangedSet_left_difference [Fintype Γ] (S : Set Γ) (a : ExchangeChoice S) :
    S\exchangedSet S a={a.1.val} := by
  ext x
  simp only [exchangedSet,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or,not_and]
  constructor
  · rintro ⟨hx,_,ha⟩
    by_contra hh
    exact ha hx hh
  · intro he
    subst x
    refine ⟨a.1.property,?_,fun _ hn => hn rfl⟩
    intro he
    exact a.2.property (he ▸ a.1.property)
omit sectionInstance110 sectionInstance111 in
lemma exchangedSet_right_difference [Fintype Γ] [DecidableEq Γ] (S : Set Γ) (a : ExchangeChoice S) :
    exchangedSet S a\S={a.2.val} := by
  ext x
  simp only [exchangedSet,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hh,hn⟩
    exact hh.resolve_right (fun h => hn h.1)
  · intro he; subst x
    exact ⟨Or.inl rfl,a.2.property⟩
lemma exchangedSet_injective (S : Set Γ) : Function.Injective (exchangedSet S) := by
  intro a b he
  apply Prod.ext
  · apply Subtype.ext
    have h := congrArg (fun T => S\T) he
    rw [exchangedSet_left_difference,exchangedSet_left_difference] at h
    exact Set.singleton_injective h
  · apply Subtype.ext
    have h := congrArg (fun T => T\S) he
    rw [exchangedSet_right_difference,exchangedSet_right_difference] at h
    exact Set.singleton_injective h
lemma exchangedSet_exists_iff (S T : Set Γ) :
    (∃ a : ExchangeChoice S,exchangedSet S a=T) ↔ ExchangeAdjacent S T := by
  constructor
  · rintro ⟨a,rfl⟩; exact exchangedSet_adjacent S a
  · intro h
    obtain ⟨a,ha,b,hb,he⟩ := h.move
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),he.symm⟩
lemma sum_exchangedSet_indicator (S T : Set Γ) (r : ℝ) :
    (∑ a : ExchangeChoice S,if exchangedSet S a=T then r else 0)=
      if ExchangeAdjacent S T then r else 0 := by
  by_cases h : ExchangeAdjacent S T
  · obtain ⟨a,ha⟩ := (exchangedSet_exists_iff S T).mpr h
    have he : ∀ b : ExchangeChoice S,exchangedSet S b=T ↔ b=a := by
      intro b; rw [←ha]; exact (exchangedSet_injective S).eq_iff
    simp [he,h]
  · have he : ∀ a : ExchangeChoice S, exchangedSet S a≠T := by
      intro a ha; exact h ((exchangedSet_exists_iff S T).mp ⟨a,ha⟩)
    simp [he,h]
omit sectionInstance111 in
lemma exchangeOffer_expansion [DecidableEq Γ] (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) (S : ChainIndex gs)
    (a : ExchangeChoice S.val) (φ : ChainIndex gs → ℝ) :
    exchangeOffer gs w f S a φ=φ S+∑ T : ChainIndex gs,
      if exchangedSet S.val a=T.val then metropolisAcceptance gs w f S T*(φ T-φ S) else 0 := by
  unfold exchangeOffer
  split_ifs with ht
  · let T : ChainIndex gs := ⟨exchangedSet S.val a,ht⟩
    have he : ∀ U : ChainIndex gs,exchangedSet S.val a=U.val ↔ U=T := by
      intro U
      constructor
      · intro he; exact Subtype.ext he.symm
      · intro he; subst U; rfl
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    change _=φ S+metropolisAcceptance gs w f S T*(φ T-φ S)
    ring
  · have he : ∀ T : ChainIndex gs,exchangedSet S.val a≠T.val := by
      intro T he; exact ht (he ▸ T.property)
    simp [he]
lemma metropolisAcceptance_min (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ)
    (hw : ∀ p r,0<w p r) (hf : ∀ S,0<f S) (S T : ChainIndex gs) :
    metropolisAcceptance gs w f S T=
      min (chainWeight gs w f S.val) (chainWeight gs w f T.val)/chainWeight gs w f S.val := by
  have hs := chainWeight_pos gs w f hw hf S.val
  unfold metropolisAcceptance
  rw [←min_div_div_right hs.le,div_self hs.ne']

lemma lazy_exchange_expectation (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hne : gs≠[]) (hcover : pairSupport gs=Set.univ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ)
    (hw : ∀ p r,0<w p r) (hf : ∀ S,0<f S)
    (S : ChainIndex gs) (φ : ChainIndex gs → ℝ) :
    (φ S+uniformAverage (fun a => exchangeOffer gs w f S a φ))/2=
      (metropolisChain gs hgs hne hcover w f hw hf).apply φ S := by
  have hn : (gs.length:ℝ)≠0 := by exact_mod_cast ne_of_gt (List.length_pos_iff.mpr hne)
  have hc : (Fintype.card (ExchangeChoice S.val):ℝ)=(gs.length:ℝ)^2 := by
    rw [exchangeChoice_card gs hgs hcover S,Nat.cast_pow]
  have hex : uniformAverage (fun a => exchangeOffer gs w f S a φ)=
      φ S+(∑ T : ChainIndex gs,if ExchangeAdjacent S.val T.val then
        metropolisAcceptance gs w f S T*(φ T-φ S) else 0)/(gs.length:ℝ)^2 := by
    simp_rw [exchangeOffer_expansion]
    rw [uniformAverage_add]
    have hnon : Nonempty (ExchangeChoice S.val) := Fintype.card_pos_iff.mp (by
      rw [exchangeChoice_card gs hgs hcover S]
      exact pow_pos (List.length_pos_iff.mpr hne) _)
    let := hnon
    rw [uniformAverage_const]
    congr 1
    unfold uniformAverage
    rw [hc,Finset.sum_comm]
    simp_rw [sum_exchangedSet_indicator]
  rw [hex]
  change _=∑ T,(metropolisMove gs w f S T+if S=T then 1-∑ U,metropolisMove gs w f S U else 0)*φ T
  simp_rw [add_mul,ite_mul,zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have he : (∑ T : ChainIndex gs,if ExchangeAdjacent S.val T.val then
        metropolisAcceptance gs w f S T*(φ T-φ S) else 0)/(gs.length:ℝ)^2/2=
      ∑ T : ChainIndex gs,metropolisMove gs w f S T*(φ T-φ S) := by
    rw [Finset.sum_div,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro T _
    by_cases ht : ExchangeAdjacent S.val T.val
    · simp only [metropolisMove,ite_eq_left ht,metropolisAcceptance_min gs w f hw hf]
      field_simp

    · simp [metropolisMove,ht]
  have hsum : (∑ T : ChainIndex gs,metropolisMove gs w f S T*(φ T-φ S))=
      (∑ T : ChainIndex gs,metropolisMove gs w f S T*φ T)-
        (∑ T : ChainIndex gs,metropolisMove gs w f S T)*φ S := by
    simp [mul_sub,Finset.sum_sub_distrib,Finset.sum_mul]
  linarith
end MetropolisSampling
section RationalSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance112 : Fintype Γ] [sectionInstance113 : DecidableEq Γ]
omit sectionInstance113 in
lemma rationalMultiplier_cast [DecidableEq Γ] (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (S : Set Γ) :
    (rationalMultiplier gs w S:ℝ)=chainMultiplier gs (fun p r => (w p r:ℝ)) S := by
  unfold rationalMultiplier chainMultiplier
  split_ifs <;> simp
lemma rationalWeight_cast (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (f : Set Γ → ℚ) (S : Set Γ) :
    (rationalWeight gs w f S:ℝ)=chainWeight gs (fun p r => (w p r:ℝ)) (fun S => (f S:ℝ)) S := by
  simp [rationalWeight,chainWeight,rationalMultiplier_cast]
omit sectionInstance112 sectionInstance113 in
lemma rationalEmpirical_cast [Fintype Γ] [DecidableEq Γ] (H : Set Γ → ℚ) (l : List (Set Γ)) :
    (rationalEmpirical H l:ℝ)=empirical (fun S => (H S:ℝ)) l := by
  simp [rationalEmpirical,empirical,Rat.cast_list_sum,List.map_map,Function.comp_def]
omit sectionInstance112 sectionInstance113 in
lemma rationalPlain_cast [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (S : Set Γ) :
    (rationalPlain gs g S:ℝ)=plainObservable gs (fun S => (g S:ℝ)) S := by
  unfold rationalPlain plainObservable; split_ifs <;> simp
omit sectionInstance112 sectionInstance113 in
lemma rationalDefect_cast [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) :
    (rationalDefect gs p r S:ℝ)=defectIndicator gs p r S := by
  unfold rationalDefect defectIndicator; split_ifs <;> simp
lemma rationalLearn_cast (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (l : List (Set Γ)) (p r : Γ × Γ) :
    (rationalLearn gs w l p r:ℝ)=learnedMultipliers gs (fun p r => (w p r:ℝ)) l p r := by
  unfold rationalLearn learnedMultipliers
  split_ifs <;> simp [rationalEmpirical_cast,rationalPlain_cast,rationalDefect_cast]
lemma rationalHistory_cast {X : Type*} (gs : List (Γ × Γ))
    (sample : X → List (Set Γ)) (h : List X) (p r : Γ × Γ) :
    (rationalHistory gs sample h p r:ℝ)=historyWeights gs sample h p r := by
  induction h using List.reverseRecOn generalizing p r with
  | nil => norm_num [rationalHistory,historyWeights]
  | append_singleton h x ih =>
    simp only [rationalHistory,List.foldl_append,List.foldl_cons,List.foldl_nil,historyWeights_snoc]
    rw [rationalLearn_cast]
    have he : (fun p r => ((h.foldl (fun w x => rationalLearn gs w (sample x)) (fun _ _ => 4)) p r:ℝ))=
        historyWeights gs sample h := by funext p r; exact ih p r
    rw [he]

lemma rationalRho_cast (n : ℕ) : (rationalRho n:ℝ)=annealRho n := by simp [rationalRho,annealRho]
omit sectionInstance112 sectionInstance113 in
lemma rationalAnneal_cast [Fintype Γ] [DecidableEq Γ] (M : Matroid Γ) (n j : ℕ) (S : Set Γ) :
    (rationalAnneal M n j S:ℝ)=annealWeight M n j S := by simp [rationalAnneal,annealWeight,matroidWeight,rationalRho_cast]
lemma rationalRatio_cast (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (l : List (Set Γ)) :
    (rationalRatio gs g l:ℝ)=empiricalRatio gs (fun S => (g S:ℝ)) l := by
  simp [rationalRatio,empiricalRatio,rationalEmpirical_cast,rationalPlain_cast]
end RationalSampling

namespace DrawTree
open scoped BigOperators Classical
lemma uniformChoice_expectation (A : Type*) [Fintype A] [Nonempty A] (φ : A → ℝ) :
    (uniformChoice A).expectation φ=uniformAverage φ := by
  unfold uniformChoice
  change uniformAverage (fun i => φ ((Fintype.equivFin A).symm (Fin.cast _ i)))=_
  exact uniformAverage_equiv ((finCongr (by have hh := Fintype.card_pos (α := A); omega)).trans (Fintype.equivFin A).symm) φ
end DrawTree

section RationalMetropolis
open scoped BigOperators Classical
variable {Γ : Type*} [Fintype Γ] [sectionInstance115 : DecidableEq Γ]
variable (gs : List (Γ × Γ))
lemma rationalAcceptance_cast (w : (Γ × Γ) → (Γ × Γ) → ℚ) (f : Set Γ → ℚ) (S T : ChainIndex gs) :
    (rationalAcceptance gs w f S T:ℝ)=metropolisAcceptance gs (fun p r => (w p r:ℝ)) (fun S => (f S:ℝ)) S T := by
  simp [rationalAcceptance,metropolisAcceptance,rationalWeight_cast]
omit sectionInstance115 in
lemma rationalAcceptance_bounds [DecidableEq Γ] (w : (Γ × Γ) → (Γ × Γ) → ℚ) (f : Set Γ → ℚ)
    (hw : ∀ p r,0<w p r) (hf : ∀ S,0<f S) (S T : ChainIndex gs) :
    0≤rationalAcceptance gs w f S T ∧ rationalAcceptance gs w f S T≤1 := by
  have hpos : ∀ S,rationalWeight gs w f S>0 := by
    intro S
    unfold rationalWeight rationalMultiplier
    apply mul_pos _ (hf S)
    split_ifs <;> first | exact hw _ _ | norm_num
  exact ⟨le_min (by norm_num) (div_nonneg (hpos _).le (hpos _).le),min_le_left _ _⟩
lemma rationalExchange_expectation (w : (Γ × Γ) → (Γ × Γ) → ℚ) (f : Set Γ → ℚ)
    (hw : ∀ p r,0<w p r) (hf : ∀ S,0<f S) (S : ChainIndex gs) (a : ExchangeChoice S.val)
    (φ : ChainIndex gs → ℝ) :
    (rationalExchange gs w f S a).expectation φ=
      exchangeOffer gs (fun p r => (w p r:ℝ)) (fun S => (f S:ℝ)) S a φ := by
  unfold rationalExchange exchangeOffer
  split_ifs with ht
  · rw [DrawTree.expectation_map,DrawTree.bernoulli_expectation _
      (rationalAcceptance_bounds gs w f hw hf S _).1 (rationalAcceptance_bounds gs w f hw hf S _).2]
    simp only [ite_true,Bool.false_eq_true,ite_false,rationalAcceptance_cast]
  · rfl
lemma rationalMetropolis_expectation (hgs : SlotsFresh gs ∅) (hne : gs≠[])
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℚ) (f : Set Γ → ℚ)
    (hw : ∀ p r,0<w p r) (hf : ∀ S,0<f S) (S : ChainIndex gs) (φ : ChainIndex gs → ℝ) :
    (rationalMetropolis gs hgs hne hcover w f S).expectation φ=
      (metropolisChain gs hgs hne hcover (fun p r => (w p r:ℝ)) (fun S => (f S:ℝ))
        (by intro p r; exact_mod_cast hw p r) (by intro S; exact_mod_cast hf S)).apply φ S := by
  unfold rationalMetropolis
  rw [DrawTree.expectation_bind,DrawTree.bernoulli_expectation _ (by norm_num) (by norm_num)]
  simp only [ite_true,Bool.false_eq_true,ite_false,DrawTree.expectation,
    DrawTree.expectation_bind,DrawTree.uniformChoice_expectation,
    rationalExchange_expectation gs w f hw hf]
  have he := lazy_exchange_expectation gs hgs hne hcover (fun p r => (w p r:ℝ)) (fun S => (f S:ℝ))
    (by intro p r; exact_mod_cast hw p r) (by intro S; exact_mod_cast hf S) S φ
  rw [←he]
  norm_num
  ring
end RationalMetropolis
namespace DrawTree
open scoped BigOperators Classical
variable {A B D : Type*}
lemma expectation_optionBind (t : DrawTree (Option A)) (k : A → DrawTree (Option B)) (φ : B → ℝ) :
    (t.optionBind k).expectation (optionValue φ)=
      t.expectation (optionValue (fun a => (k a).expectation (optionValue φ))) := by
  rw [optionBind,expectation_bind]
  congr 1; funext a; cases a <;> rfl
lemma matches_comp [Fintype A] [Fintype B] [Fintype D]
    (t : A → DrawTree (Option B)) (u : B → DrawTree (Option D))
    (P : A → B → ℝ) (Q : B → D → ℝ) (ht : Matches t P) (hu : Matches u Q) :
    Matches (fun a => (t a).optionBind u) (fun a d => ∑ b,P a b*Q b d) := by
  intro a φ
  rw [expectation_optionBind,ht]
  simp_rw [show ∀ b,(u b).expectation (optionValue φ)=∑ d,Q b d*φ d from fun b => hu b φ]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
  exact Finset.sum_comm

lemma iterate_matches [Fintype A] (t : A → DrawTree (Option A)) (K : FiniteKernel A A)
    (ht : Matches t K.P) (k : ℕ) : Matches (iterate t k) (K.power k).P := by
  induction k with
  | zero =>
    intro a φ
    change φ a=∑ b,(if a=b then (1:ℝ) else 0)*φ b
    simp
  | succ k ih =>
    have h := matches_comp (iterate t k) t (K.power k).P K.P ih ht
    simpa only [iterate,FiniteKernel.power,FiniteKernel.comp] using h
end DrawTree

section DrawHitting
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance116 : Fintype X]
variable (step : X → DrawTree X) (A : X → Prop)
variable (C : FiniteChain X) (Q : KilledKernel (FiniteChain.Outside A))
    (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
    (hstep : ∀ x φ,(step x).expectation φ=C.apply φ x)
lemma partialGreen_succ_apply (k : ℕ) (f : FiniteChain.Outside A → ℝ) (x : FiniteChain.Outside A) :
    Q.partialGreen (k+1) f x=f x+Q.apply (Q.partialGreen k f) x := by
  unfold KilledKernel.partialGreen
  rw [Finset.sum_range_succ']
  simp only [KilledKernel.iterate_succ,KilledKernel.iterate_zero]
  rw [KilledKernel.apply_sum]
  ring
include hQ hstep in
lemma hittingTree_outside (k : ℕ) (φ : FiniteChain.Inside A → ℝ) (x : FiniteChain.Outside A) :
    (hittingTree step A k x.val).expectation (DrawTree.optionValue φ)=
      Q.partialGreen k (fun z => ∑ y : FiniteChain.Inside A,C.P z.val y.val*φ y) x := by
  induction k generalizing x with
  | zero => simp [hittingTree,DrawTree.expectation,DrawTree.optionValue,KilledKernel.partialGreen]
  | succ k ih =>
    rw [hittingTree,DrawTree.expectation_bind,hstep,FiniteChain.apply]
    rw [←Fintype.sum_subtype_add_sum_subtype A]
    have hin : (∑ y : FiniteChain.Inside A,C.P x.val y.val*
        (if hy : A y.val then DrawTree.leaf (some (⟨y.val,hy⟩ : FiniteChain.Inside A)) else hittingTree step A k y.val).expectation (DrawTree.optionValue φ))=
        ∑ y : FiniteChain.Inside A,C.P x.val y.val*φ y := by
      apply Finset.sum_congr rfl; intro y _
      simp only [dite_eq_left y.property,DrawTree.expectation,DrawTree.optionValue]
    have hout : (∑ y : FiniteChain.Outside A,C.P x.val y.val*
        (if hy : A y.val then DrawTree.leaf (some (⟨y.val,hy⟩ : FiniteChain.Inside A)) else hittingTree step A k y.val).expectation (DrawTree.optionValue φ))=
        Q.apply (Q.partialGreen k (fun z => ∑ y : FiniteChain.Inside A,C.P z.val y.val*φ y)) x := by
      unfold KilledKernel.apply
      apply Finset.sum_congr rfl; intro y _
      rw [dite_eq_right y.property,ih,hQ]
    rw [hin,hout,partialGreen_succ_apply]
include hQ hstep in
lemma hittingTree_inside (k : ℕ) (x : FiniteChain.Inside A) (φ : FiniteChain.Inside A → ℝ) :
    (hittingTree step A (k+1) x.val).expectation (DrawTree.optionValue φ)=
      ∑ y : FiniteChain.Inside A,C.cappedTrace A Q k x y*φ y := by
  rw [hittingTree,DrawTree.expectation_bind,hstep,FiniteChain.apply]
  rw [←Fintype.sum_subtype_add_sum_subtype A]
  have hin : (∑ y : FiniteChain.Inside A,C.P x.val y.val*
      (if hy : A y.val then DrawTree.leaf (some (⟨y.val,hy⟩ : FiniteChain.Inside A)) else hittingTree step A k y.val).expectation (DrawTree.optionValue φ))=
      ∑ y : FiniteChain.Inside A,C.P x.val y.val*φ y := by
    apply Finset.sum_congr rfl; intro y _
    simp only [dite_eq_left y.property,DrawTree.expectation,DrawTree.optionValue]
  have hout : (∑ y : FiniteChain.Outside A,C.P x.val y.val*
      (if hy : A y.val then DrawTree.leaf (some (⟨y.val,hy⟩ : FiniteChain.Inside A)) else hittingTree step A k y.val).expectation (DrawTree.optionValue φ))=
      ∑ z : FiniteChain.Outside A,C.P x.val z.val*
        Q.partialGreen k (fun t => ∑ y : FiniteChain.Inside A,C.P t.val y.val*φ y) z := by
    apply Finset.sum_congr rfl; intro y _
    rw [dite_eq_right y.property,hittingTree_outside step A C Q hQ hstep]
  rw [hin,hout]
  simp only [FiniteChain.cappedTrace,add_mul,Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro z _
  simp only [mul_assoc]
  rw [←Finset.mul_sum,KilledKernel.partialGreen_sum]
  congr 1
  apply Finset.sum_congr rfl; intro y _
  unfold KilledKernel.partialGreen
  simp_rw [show (fun t : FiniteChain.Outside A => C.P t.val y.val*φ y)=fun t => φ y*C.P t.val y.val by funext t; ring]
  simp only [KilledKernel.iterate_mul,←Finset.mul_sum]
  ring
end DrawHitting
namespace DrawTree
open scoped BigOperators Classical
variable {X Y : Type*} [sectionInstance117 : Fintype X]
lemma sampleMass_delta (C : FiniteChain X) (ν : X → ℝ) (k : ℕ) (v : FiniteChain.Sample X k) :
    (∑ x,ν x*C.sampleMass (fun y => if x=y then 1 else 0) v)=C.sampleMass ν v := by
  cases k with
  | zero =>
    dsimp only [FiniteChain.Sample] at v
    change (∑ x : X,ν x*(if x=v then 1 else 0))=ν v
    simp
  | succ k =>
    change (∑ x,ν x*((if x=v.1 then 1 else 0)*C.sampleMass (C.P v.1) v.2))=_
    change (∑ x : X,ν x*((if x=v.1 then 1 else 0)*C.sampleMass (C.P v.1) v.2))=ν v.1*C.sampleMass (C.P v.1) v.2
    simp
lemma sample_expectation (step : X → DrawTree X) (C : FiniteChain X)
    (hs : ∀ x φ,(step x).expectation φ=C.apply φ x) (k : ℕ) (x : X)
    (F : FiniteChain.Sample X k → ℝ) :
    (sample step k x).expectation F=∑ v : FiniteChain.Sample X k,C.sampleMass (fun y => if x=y then 1 else 0) v*F v := by
  induction k generalizing x with
  | zero =>
    dsimp only [FiniteChain.Sample,FiniteChain.sampleFintype] at F ⊢
    change F x=∑ v : X,(if x=v then (1:ℝ) else 0)*F v
    simp
  | succ k ih =>
    dsimp only [FiniteChain.Sample,FiniteChain.sampleFintype] at F ⊢
    change ((step x).bind (fun y => (sample step k y).map (fun v : FiniteChain.Sample X k => (x,v)))).expectation F=∑ v : X × FiniteChain.Sample X k,_
    rw [expectation_bind]
    simp_rw [expectation_map,ih]
    rw [hs,FiniteChain.apply,Fintype.sum_prod_type]
    simp only [FiniteChain.sampleMass,ite_mul,one_mul,zero_mul]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    simp only [←mul_assoc]
    rw [←Finset.sum_mul,sampleMass_delta]
lemma sample_start_expectation (start : DrawTree (Option X)) (step : X → DrawTree X)
    (ν : X → ℝ) (C : FiniteChain X)
    (hstart : ∀ φ,start.expectation (optionValue φ)=∑ x,ν x*φ x)
    (hs : ∀ x φ,(step x).expectation φ=C.apply φ x) (k : ℕ)
    (F : FiniteChain.Sample X k → ℝ) :
    (start.optionBind (fun x => (sample step k x).map some)).expectation (optionValue F)=
      ∑ v : FiniteChain.Sample X k,C.sampleMass ν v*F v := by
  rw [expectation_optionBind,hstart]
  simp_rw [expectation_map]
  simp only [optionValue]
  simp_rw [sample_expectation step C hs,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v _
  simp only [←mul_assoc]
  rw [←Finset.sum_mul]
  congr 1
  exact sampleMass_delta C ν k v
lemma history_expectation (K : List X → DrawTree (Option X)) (P : List X → X → ℝ)
    (hK : Matches K P) (k : ℕ) (h : List X) (F : List X → ℝ) :
    (history K k h).expectation (optionValue F)=FiniteExperiment.expect P k h F := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    rw [history,expectation_optionBind,hK]
    simp_rw [ih]
    rfl
end DrawTree
section DrawActual
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n)) (N L : ℕ)
local notation "GS" => pairedSlots n
lemma rationalStored_cast (h : List (PhaseSample n N)) (j : ℕ) (p r) :
    (rationalStored n N h j p r:ℝ)=storedWeights n N h j p r := by
  exact rationalHistory_cast GS (observedSets n N) (h.take j) p r
lemma rationalStored_pos (h : List (PhaseSample n N)) (hp : HistoryPositive n N h)
    (j : ℕ) (p r) : 0<rationalStored n N h j p r := by
  have hh := historyPositive_all n N h hp j p r
  rw [←rationalStored_cast] at hh
  exact_mod_cast hh
lemma actualStepTree_expectation (h : List (PhaseSample n N)) (hp : HistoryPositive n N h) (j : ℕ)
    (x : ChainIndex GS) (φ : ChainIndex GS → ℝ) :
    (actualStepTree n hn M N h j x).expectation φ=
      (metropolisChain GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
        (storedWeights n N h j) (annealWeight M n j) (historyPositive_all n N h hp j)
        (annealWeight_pos M n j hn)).apply φ x := by
  unfold actualStepTree
  rw [rationalMetropolis_expectation _ _ _ _ _ _ (rationalStored_pos n N h hp j)
    (by intro S; have hh := annealWeight_pos M n j hn S; rw [←rationalAnneal_cast] at hh; exact_mod_cast hh)]
  simp_rw [rationalStored_cast,rationalAnneal_cast]
lemma actualTraceTree_matches (h : List (PhaseSample n N)) (hp : HistoryPositive n N h) (j cap : ℕ) :
    DrawTree.Matches (actualTraceTree n hn M N h j cap)
      (actualCappedTrace n hn M j (storedWeights n N h j) (historyPositive_all n N h hp j) cap).P := by
  intro x φ
  exact hittingTree_inside (actualStepTree n hn M N h j) (plainPredicate GS)
    (metropolisChain GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
      (storedWeights n N h j) (annealWeight M n j) (historyPositive_all n N h hp j)
      (annealWeight_pos M n j hn))
    (metropolisKilled GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
      (storedWeights n N h j) (annealWeight M n j) (historyPositive_all n N h hp j)
      (annealWeight_pos M n j hn)) (by intros; rfl)
      (actualStepTree_expectation n hn M N h hp j) cap x φ
lemma actualRestartTree_expectation (h : List (PhaseSample n N)) (hp : HistoryPositive n N h)
    (cap j : ℕ) (φ : PlainIndex GS → ℝ) :
    (actualRestartTree n hn M N L h cap j).expectation (DrawTree.optionValue φ)=
      ∑ x,restartLaw n hn M L cap (storedWeights n N h) (historyPositive_all n N h hp) j x*φ x := by
  induction j generalizing φ with
  | zero =>
    rw [actualRestartTree,DrawTree.expectation_map,DrawTree.uniformChoice_expectation]
    simp only [DrawTree.optionValue,uniformAverage,restartLaw,uniformPlain,plainIndex_card,Nat.cast_pow,Nat.cast_ofNat]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro x _; ring
  | succ j ih =>
    rw [actualRestartTree,DrawTree.expectation_optionBind,ih]
    have hi := DrawTree.iterate_matches _ _ (actualTraceTree_matches n hn M N h hp (j+1) cap) (20*n^4*(n*(L+1)+2))
    unfold DrawTree.Matches at hi
    simp_rw [hi]
    simp only [Finset.mul_sum]
    simp only [restartLaw,FiniteKernel.push,Finset.sum_mul,mul_assoc]
    rw [Finset.sum_comm]
lemma actualStartTree_expectation (h : List (PhaseSample n N)) (hp : HistoryPositive n N h)
    (φ : ChainIndex GS → ℝ) :
    (actualStartTree n hn M N L h).expectation (DrawTree.optionValue φ)=∑ x,phaseStart n hn M N L h hp x*φ x := by
  rw [actualStartTree,DrawTree.expectation_map]
  have hf : (fun a : Option (PlainIndex GS) => DrawTree.optionValue φ (Option.map Subtype.val a))=
      DrawTree.optionValue (fun a => φ a.val) := by funext a; cases a <;> rfl
  rw [hf,actualRestartTree_expectation n hn M N L h hp]
  rw [←Fintype.sum_subtype_add_sum_subtype (plainPredicate GS)]
  simp only [phaseStart,plainLift]
  have hin : (∑ x : PlainIndex GS,(if hx : PlainState GS x.val.val then
      restartLaw n hn M L (restartCap n L) (storedWeights n N h) (historyPositive_all n N h hp) h.length ⟨x.val,hx⟩ else 0)*φ x.val)=
      ∑ x : PlainIndex GS,restartLaw n hn M L (restartCap n L) (storedWeights n N h) (historyPositive_all n N h hp) h.length x*φ x.val := by
    apply Finset.sum_congr rfl; intro x _; rw [dite_eq_left x.property]
  rw [hin]
  have hout : (∑ x : FiniteChain.Outside (plainPredicate GS),
      (if hx : PlainState GS x.val.val then
       restartLaw n hn M L (restartCap n L) (storedWeights n N h) (historyPositive_all n N h hp) h.length ⟨x.val,hx⟩ else 0)*φ x.val)=0 := by
    apply Finset.sum_eq_zero; intro x _; rw [dite_eq_right x.property,zero_mul]
  rw [hout,add_zero]
lemma actualPhaseTree_matches : DrawTree.Matches (actualPhaseTree n hn M N L) (phaseKernel n hn M N L) := by
  intro h φ
  unfold actualPhaseTree phaseKernel
  split_ifs with hp
  · exact DrawTree.sample_start_expectation _ _ _ _
      (actualStartTree_expectation n hn M N L h hp)
      (actualStepTree_expectation n hn M N h hp h.length) (N-1) φ
  · simp [DrawTree.expectation,DrawTree.optionValue]
end DrawActual
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n
lemma rationalEstimate_cast (h : List (PhaseSample n N)) :
    (rationalEstimate n M₁ M₂ N L h:ℝ)=historyEstimate n N L K h := by
  simp only [rationalEstimate,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_prod,rationalRatio_cast,
    rationalRho_cast,historyEstimate]
lemma rationalGuard_cast (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    (rationalGuard n M₁ M₂ N L h x:ℝ)=guardedEstimate n M₁ M₂ N L h x := by
  unfold rationalGuard guardedEstimate
  split_ifs <;> simp [rationalEstimate_cast]
lemma rationalWitnessTree_expectation (h : List (PhaseSample n N)) (φ : PlainIndex GS → ℝ) :
    (rationalWitnessTree n hn M₁ M₂ N L h).expectation (DrawTree.optionValue φ)=
      ∑ x,witnessKernel n hn M₁ M₂ N L h x*φ x := by
  unfold rationalWitnessTree witnessKernel
  split_ifs with hp
  · exact actualRestartTree_expectation n hn K N L h hp (restartCap n L) h.length φ
  · simp [DrawTree.expectation,DrawTree.optionValue]
lemma rationalAlgorithmTree_expectation (F : ℚ → ℝ) :
    (rationalAlgorithmTree n hn M₁ M₂ N L).expectation (DrawTree.optionValue F)=
      FiniteExperiment.expect (phaseKernel n hn K N L) L []
        (fun h => ∑ x,witnessKernel n hn M₁ M₂ N L h x*F (rationalGuard n M₁ M₂ N L h x)) := by
  rw [rationalAlgorithmTree,DrawTree.expectation_optionBind,DrawTree.history_expectation _ _ (actualPhaseTree_matches n hn K N L)]
  congr 1; funext h
  rw [DrawTree.expectation_map]
  have hf : (fun a : Option (PlainIndex GS) => DrawTree.optionValue F
      (Option.map (rationalGuard n M₁ M₂ N L h) a))=
      DrawTree.optionValue (fun x => F (rationalGuard n M₁ M₂ N L h x)) := by
    funext a; cases a <;> rfl
  rw [hf,rationalWitnessTree_expectation]
lemma rationalAlgorithmTree_success_eq (ε : ℚ) :
    (rationalAlgorithmTree n hn M₁ M₂ N L).expectation
      (DrawTree.optionValue (fun z => if relativeAccuracy ε (commonBaseCount M₁ M₂) z then 1 else 0))=
      actualRealSuccess n hn M₁ M₂ N L (ε:ℝ) := by
  rw [rationalAlgorithmTree_expectation]
  unfold actualRealSuccess
  congr 1; funext h
  apply Finset.sum_congr rfl; intro x _
  have he : relativeAccuracy ε (commonBaseCount M₁ M₂) (rationalGuard n M₁ M₂ N L h x) ↔
      (1-(ε:ℝ))*(commonBaseCount M₁ M₂:ℝ)≤guardedEstimate n M₁ M₂ N L h x ∧
      guardedEstimate n M₁ M₂ N L h x≤(1+(ε:ℝ))*(commonBaseCount M₁ M₂:ℝ) := by
    rw [←rationalGuard_cast]
    unfold relativeAccuracy
    constructor <;> intro hh <;> exact_mod_cast hh
  simp only [he,mul_ite,mul_one,mul_zero]
include hn in
theorem rational_algorithm_success_oai (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (hr : M₁.eRank=M₂.eRank) (ε : ℚ) (hε0 : 0<ε) (hε1 : ε<1)
    (b : ℕ) (hb : (1/2:ℝ)^b ≤ (ε:ℝ)/10) (hZ : 0<commonBaseCount M₁ M₂)
    (hN : (10:ℝ)^10*(annealLength n b+1)*n^14/(annealTolerance (ε:ℝ) (annealLength n b))^2 ≤ N) :
    3/4 ≤ (rationalAlgorithmTree n hn M₁ M₂ N (annealLength n b)).expectation
      (DrawTree.optionValue (fun z => if relativeAccuracy ε (commonBaseCount M₁ M₂) z then 1 else 0)) := by
  rw [rationalAlgorithmTree_success_eq]
  exact real_annealing_success n hn M₁ M₂ N hE₁ hE₂ hr (ε:ℝ)
    (by exact_mod_cast hε0) (by exact_mod_cast hε1) b hb hZ hN

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

end

namespace MachineCode


open Expression

open Expression

open Expression

open Expression

open Expression

open Expression
end MachineCode

end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end

theorem solution : type_of% @OAI.CommonBasesFPRAS.rational_algorithm_success_oai := @OAI.CommonBasesFPRAS.rational_algorithm_success_oai
