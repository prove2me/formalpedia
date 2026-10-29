-- Prove2me | solution 1 for OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T02:58:58.030993+00:00
-- url     : https://prove2.me/submissions/16b5922d-c2a9-4404-b825-7d89148de87c

import Mathlib
import Definitions.Def_OAIQ089A003
import Definitions.Def_OAIQ089A004

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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
  all_goals try with_reducible_and_instances rfl
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

omit sectionInstance12 in
lemma slotDirection_nonneg [Fintype ι] (E : Finset ι) (i : ι) : 0 ≤ slotDirection E i := by
  unfold slotDirection
  split_ifs <;> norm_num

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
    Bool.false_eq_true, ite_false, ite_true, if_true]
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
    rootDemand, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, if_true,
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

section DefectTransport
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance48 : Fintype Γ] [sectionInstance49 : DecidableEq Γ]

omit sectionInstance48 sectionInstance49 in
lemma SamePair.full [Fintype Γ] [DecidableEq Γ] {p q : Γ × Γ} (h : SamePair p q) (S : Set Γ) :
    PairFull q S ↔ PairFull p S := by
  rcases h with rfl | rfl <;> simp [PairFull,and_comm]
omit sectionInstance48 sectionInstance49 in
lemma SamePair.empty [Fintype Γ] [DecidableEq Γ] {p q : Γ × Γ} (h : SamePair p q) (S : Set Γ) :
    PairEmpty q S ↔ PairEmpty p S := by
  rcases h with rfl | rfl <;> simp [PairEmpty,and_comm]
omit sectionInstance48 sectionInstance49 in
lemma SamePair.single [Fintype Γ] [DecidableEq Γ] {p q : Γ × Γ} (h : SamePair p q) (S : Set Γ) :
    PairSingle q S ↔ PairSingle p S := by
  rcases h with rfl | rfl <;> simp [PairSingle,or_comm]
omit sectionInstance48 sectionInstance49 in
lemma SamePair.set [Fintype Γ] [DecidableEq Γ] {p q : Γ × Γ} (h : SamePair p q) :
    ({q.1,q.2} : Set Γ) = {p.1,p.2} := by
  rcases h with rfl | rfl <;> simp [Set.pair_comm]
omit sectionInstance48 sectionInstance49 in
lemma SamePair.fresh [Fintype Γ] [DecidableEq Γ] {p q : Γ × Γ} (h : SamePair p q) (ps : List (Γ × Γ)) (A : Set Γ) :
    SlotsFresh (q::ps) A ↔ SlotsFresh (p::ps) A := by
  rcases h with rfl | rfl
  · rfl
  · simp only [SlotsFresh,Prod.fst_swap,Prod.snd_swap,ne_eq]
    rw [Set.insert_comm]
    tauto

lemma slot_energy_le_chain (gs ps : List (Γ × Γ)) (A : Set Γ) (p d : Γ)
    (W : Γ → ℝ) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ)
    (hw : ∀ p r, 0 < w p r) (hf : ∀ S, 0 < f S)
    (hv : ∀ S ∈ slotVertices ps A (rootEmbedding p d),
      ChainState gs S ∧ missingMultiplier ps (rootEmbedding p d) W S = chainMultiplier gs w S) :
    slotGraphEnergy ps f H A (rootEmbedding p d) W ≤
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  unfold slotGraphEnergy restrictedEnergy
  simp only [EdgeRespects,Respects,Set.empty_subset,Set.empty_disjoint,true_and,ite_true, if_true]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hE : slotGraphEdges ps A (rootEmbedding p d) ⊆ chainEdges gs := by
    intro ST hST
    obtain ⟨hp,ha⟩ := Finset.mem_filter.mp hST
    obtain ⟨hs,ht⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hv _ hs).1,(hv _ ht).1,ha⟩
  calc
    _ = ∑ ST ∈ slotGraphEdges ps A (rootEmbedding p d),
        chainConductance gs w f ST*(H ST.1-H ST.2)^2 := by
      apply Finset.sum_congr rfl
      intro ST hST
      obtain ⟨hs,ht⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hST).1
      simp only [slotEdgeEnergy,(hv _ hs).2,(hv _ ht).2,chainConductance]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hE
      intro ST _ _
      exact mul_nonneg (le_min
        (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
        (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)) (sq_nonneg _)

lemma defect_vertex_identification (gs ps : List (Γ × Γ)) (p r u v : Γ × Γ)
    (hperm : gs.Perm (p::r::ps)) (hgs : SlotsFresh gs ∅)
    (hu : SamePair p u) (hv : SamePair r v)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (S : Set Γ) (hS : S ∈ slotVertices ps {v.2} (rootEmbedding v.1 u.1)) :
    ChainState gs S ∧ missingMultiplier ps (rootEmbedding v.1 u.1)
      (pairMultiplier (r::ps) (w p)) S = chainMultiplier gs w S := by
  have hslots := (SlotsFresh.perm hperm ∅).mp hgs
  have horient : SlotsFresh (u::v::ps) ∅ := by
    apply (hu.fresh _ _).mpr
    change _ ∧ _ ∧ _ ∧ SlotsFresh (v::ps) (insert p.1 (insert p.2 ∅))
    exact ⟨hslots.1,hslots.2.1,hslots.2.2.1,(hv.fresh _ _).mpr hslots.2.2.2⟩
  have hfull : insert u.1 (insert u.2 (insert v.1 (insert v.2 (∅ : Set Γ)))) =
      insert v.1 (insert v.2 (insert u.1 (insert u.2 ∅))) := by
    ext x; simp only [Set.mem_insert_iff]; tauto
  have htail := horient.2.2.2.2.2.2
  have hbase : SlotsFresh ps ({v.2} ∪ Set.range (rootEmbedding v.1 u.1)) :=
    htail.mono (by
      intro x hx
      rcases hx with hx | ⟨i,rfl⟩
      · simp only [Set.mem_singleton_iff] at hx; subst x; simp
      · cases i <;> simp [rootEmbedding])
  have hne : v.1 ≠ u.1 := by
    intro he; exact horient.2.2.2.2.1 (Or.inl he)
  have hvu : v.2 ≠ u.1 := by
    intro he; exact horient.2.2.2.2.2.1 (Or.inl he)
  have heA : ∀ j, rootEmbedding v.1 u.1 j ∉ ({v.2} : Set Γ) := by
    intro j; cases j
    · exact horient.2.2.2.1
    · exact hvu.symm
  have hinc : v.2 ∈ S := slotVertices_fixed ps {v.2} _ S hS rfl
  have heB : ∀ j, rootEmbedding v.1 u.1 j ∉ ({u.2} : Set Γ) := by
    intro j; cases j
    · exact fun he => horient.2.2.2.2.1 (Or.inr (Or.inl he))
    · exact horient.1
  have hexc : u.2 ∉ S := by
    have hh := slotVertices_excluded ps {v.2} {u.2} (rootEmbedding v.1 u.1)
      (by simpa only [Set.disjoint_singleton] using (show v.2 ≠ u.2 from fun he =>
        horient.2.2.2.2.2.1 (Or.inr (Or.inl he)))) heB
      (fun t ht => let hh := htail.elements_fresh t ht
                   ⟨fun he => hh.1 (Or.inr (Or.inr (Or.inr (Or.inl he)))),
                    fun he => hh.2 (Or.inr (Or.inr (Or.inr (Or.inl he))))⟩) S hS
    exact fun hx => Set.disjoint_left.mp hh rfl hx
  have hmem (t : Γ × Γ) (ht : t ∈ gs) (hp : t ≠ p) (hr : t ≠ r) : t ∈ ps :=
    ((List.mem_cons.mp (hperm.mem_iff.mp ht)).resolve_left hp |> List.mem_cons.mp).resolve_left hr
  have hp : p ∈ gs := hperm.mem_iff.mpr List.mem_cons_self
  have hr : r ∈ gs := hperm.mem_iff.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpr : p ≠ r := hslots.pair_ne_of_mem List.mem_cons_self
  have hcl := slotVertices_classify ps {v.2} _ (rootEmbedding_injective _ _ hne) heA hbase S hS
  rcases hcl with ⟨j,hj,hrest⟩ | ⟨t,ht,he,hfull,hrest⟩
  · cases j
    · have hdef : DefectState gs p r S := by
        refine ⟨hp,hr,hpr,(hu.empty S).mp ⟨?_,hexc⟩,(hv.full S).mp ⟨?_,hinc⟩,?_⟩
        · exact fun hh => Bool.noConfusion ((hj true).mp hh)
        · exact (hj false).mpr rfl
        · intro t ht htp htr; exact hrest t (hmem t ht htp htr)
      refine ⟨Or.inr ⟨p,r,hdef⟩,?_⟩
      rw [chainMultiplier_defect gs w S hdef,missingMultiplier_old ps _ _ S false hj hrest]
      apply pairMultiplier_on hslots.2.2.2 _ r List.mem_cons_self v.1
      rcases hv with rfl | rfl <;> simp
    · have hplain : PlainState gs S := by
        intro t ht
        by_cases ht₁ : t = p
        · subst t; apply (hu.single S).mp; exact Or.inl ⟨(hj true).mpr rfl,hexc⟩
        by_cases ht₂ : t = r
        · subst t; apply (hv.single S).mp
          exact Or.inr ⟨hinc,fun hh => Bool.noConfusion ((hj false).mp hh)⟩
        exact hrest t (hmem t ht ht₁ ht₂)
      refine ⟨Or.inl hplain,?_⟩
      rw [chainMultiplier_plain gs w S hplain,missingMultiplier_old ps _ _ S true hj hrest]
      apply pairMultiplier_fresh hslots.2.2.2
      rcases hu with rfl | rfl <;> simp [rootEmbedding]
  · have hdef : DefectState gs p t S := by
      refine ⟨hp,hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)),
        hslots.pair_ne_of_mem (List.mem_cons_of_mem _ ht),(hu.empty S).mp ⟨he true,hexc⟩,hfull,?_⟩
      intro z hz hzp hzt
      by_cases hzr : z = r
      · subst z; exact (hv.single S).mp (Or.inr ⟨hinc,he false⟩)
      · exact hrest z (hmem z hz hzp hzr) hzt
    refine ⟨Or.inr ⟨p,t,hdef⟩,?_⟩
    rw [chainMultiplier_defect gs w S hdef,
      missingMultiplier_new ps htail.nodup _ _ S t ht he hfull hrest]
    exact pairMultiplier_on hslots.2.2.2 _ t (List.mem_cons_of_mem _ ht) t.1 (Or.inl rfl)

lemma SamePair.fresh_two {p r u v : Γ × Γ} (hu : SamePair p u) (hv : SamePair r v)
    (ps : List (Γ × Γ)) (A : Set Γ) (h : SlotsFresh (p::r::ps) A) :
    SlotsFresh (u::v::ps) A := by
  apply (hu.fresh _ _).mpr
  exact ⟨h.1,h.2.1,h.2.2.1,(hv.fresh _ _).mpr h.2.2.2⟩

lemma slotDefect_rest (gs ps : List (Γ × Γ)) (p r : Γ × Γ)
    (hperm : gs.Perm (p::r::ps)) (f : Set Γ → ℝ) :
    slotDefect gs f ∅ p r = slotTotal ps f {r.1,r.2} := by
  rw [slotDefect_perm hperm]
  simp [slotDefect]

lemma defect_puncture_le (gs ps : List (Γ × Γ)) (p r u v : Γ × Γ)
    (hperm : gs.Perm (p::r::ps)) (hgs : SlotsFresh gs ∅)
    (hu : SamePair p u) (hv : SamePair r v) (f : Set Γ → ℝ) (hf : ∀ S, 0 < f S)
    (x : (Γ × Γ) × List (Γ × Γ)) (hx : x ∈ slotPunctures ps) :
    slotTotal x.2 f (insert v.1 (insert u.1 {v.2})) ≤ slotDefect gs f ∅ x.1 r := by
  have hxp := slotPunctures_perm ps x hx
  have hxmem : x.1 ∈ ps := hxp.mem_iff.mpr List.mem_cons_self
  have hslots := (SlotsFresh.perm hperm ∅).mp hgs
  have hpt := hslots.pair_ne_of_mem (List.mem_cons_of_mem _ hxmem)
  have hrt := hslots.2.2.2.pair_ne_of_mem hxmem
  have hpr := hslots.pair_ne_of_mem List.mem_cons_self
  have heq : insert v.1 (insert u.1 ({v.2} : Set Γ)) = insert u.1 {r.1,r.2} := by
    rw [Set.insert_comm v.1 u.1,hv.set]
  rw [heq,slotDefect_perm (hperm.trans ((hxp.cons r).cons p))]
  simp only [slotDefect]
  simp [hpt,hrt,hpr,insert_empty_eq]
  have hp₁ : p.1 ∉ ({r.1,r.2} : Set Γ) := by
    rintro (he | he)
    · exact hslots.2.2.2.2.1 (Or.inl he.symm)
    · exact hslots.2.2.2.2.2.1 (Or.inl he.symm)
  have hp₂ : p.2 ∉ ({r.1,r.2} : Set Γ) := by
    rintro (he | he)
    · exact hslots.2.2.2.2.1 (Or.inr (Or.inl he.symm))
    · exact hslots.2.2.2.2.2.1 (Or.inr (Or.inl he.symm))
  rw [slotTotal_cons p x.2 f {r.1,r.2} hslots.1 hp₁ hp₂]
  rcases hu with rfl | rfl
  · exact le_add_of_nonneg_right (slotTotal_nonneg _ f (fun S => (hf S).le) _)
  · exact le_add_of_nonneg_left (slotTotal_nonneg _ f (fun S => (hf S).le) _)

theorem defect_conditional_transport (gs ps : List (Γ × Γ)) (p r u v : Γ × Γ)
    (hperm : gs.Perm (p::r::ps)) (hgs : SlotsFresh gs ∅)
    (hu : SamePair p u) (hv : SamePair r v)
    (f H : Set Γ → ℝ) (hf : ∀ S, 0 < f S) (hsig : HasSlotSignature f)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r) :
    let z := slotTotal gs f ∅
    let sp := slotDefect gs f ∅ p r
    let sd := slotTotal ps f {u.1,v.2}
    sd*(slotDefect gs (fun S => f S*H S) ∅ p r/sp -
      slotTotal ps (fun S => f S*H S) {u.1,v.2}/sd)^2 ≤
      (4*sd/z+1+8*(ps.length:ℝ))*
        restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  let z := slotTotal gs f ∅
  let sp := slotDefect gs f ∅ p r
  let sd := slotTotal ps f {u.1,v.2}
  let W := pairMultiplier (r::ps) (w p)
  let D := restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅
  have hslots := (SlotsFresh.perm hperm ∅).mp hgs
  have horient := hu.fresh_two hv ps ∅ hslots
  have hp : p ∈ gs := hperm.mem_iff.mpr List.mem_cons_self
  have hr : r ∈ gs := hperm.mem_iff.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpr := hslots.pair_ne_of_mem List.mem_cons_self
  have hz : 0 < z := slotTotal_pos gs f hf ∅ hgs
  have hsp : 0 < sp := slotDefect_pos gs f hf ∅ hgs p r hp hr hpr
  have hsd : 0 < sd := slotTotal_pos ps f hf _ (horient.2.2.2.2.2.2.mono (by
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl <;> simp))
  have hbase : SlotsFresh ps ({v.2} ∪ Set.range (rootEmbedding v.1 u.1)) :=
    horient.2.2.2.2.2.2.mono (by
      intro x hx
      rcases hx with hx | ⟨i,rfl⟩
      · simp only [Set.mem_singleton_iff] at hx; subst x; simp
      · cases i <;> simp [rootEmbedding])
  have hne : v.1 ≠ u.1 := fun he => horient.2.2.2.2.1 (Or.inl he)
  have hpA : v.1 ∉ ({v.2} : Set Γ) := horient.2.2.2.1
  have hdA : u.1 ∉ ({v.2} : Set Γ) := fun he => horient.2.2.2.2.2.1 (Or.inl he.symm)
  have hW : ∀ x, 0 < W x := pairMultiplier_pos _ _ (hw p)
  have hws : ∀ t ∈ ps, W t.1 = W t.2 := by
    intro t ht
    dsimp [W]
    rw [pairMultiplier_on hslots.2.2.2 _ t (List.mem_cons_of_mem _ ht) t.1 (Or.inl rfl),
      pairMultiplier_on hslots.2.2.2 _ t (List.mem_cons_of_mem _ ht) t.2 (Or.inr rfl)]
  have hWp : W v.1 = w p r := by
    apply pairMultiplier_on hslots.2.2.2 _ r List.mem_cons_self v.1
    rcases hv with rfl | rfl <;> simp
  have hWd : W u.1 = 1 := by
    apply pairMultiplier_fresh hslots.2.2.2
    rcases hu with rfl | rfl <;> simp
  have heqsp (g : Set Γ → ℝ) : slotTotal ps g (insert v.1 {v.2}) = slotDefect gs g ∅ p r := by
    rw [hv.set,slotDefect_rest gs ps p r hperm g]
  have hgoodpr : z ≤ 4*sp*w p r := by
    have hh := (div_le_iff₀ (by positivity : 0 < 4*sp)).mp (hgood p hp r hr hpr)
    dsimp [z,sp] at *; nlinarith
  have hfirst : 1/(sp*w p r) ≤ 4/z := by
    apply (div_le_div_iff₀ (mul_pos hsp (hw p r)) hz).mpr
    nlinarith
  have hsink : ∀ x ∈ slotPunctures ps,
      slotTotal x.2 f (insert v.1 (insert u.1 {v.2}))/W x.1.1 ≤ 4*sp := by
    intro x hx
    have hxmem : x.1 ∈ ps := (slotPunctures_perm ps x hx).mem_iff.mpr List.mem_cons_self
    have hxg : x.1 ∈ gs := hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hxmem))
    have hpt := hslots.pair_ne_of_mem (List.mem_cons_of_mem _ hxmem)
    have hrt := hslots.2.2.2.pair_ne_of_mem hxmem
    have hcx := slotDefect_pos gs f hf ∅ hgs p x.1 hp hxg hpt
    have htriple := slotDefect_triple_bound gs f hf hsig ∅ hgs p x.1 r hp hxg hr hpt hrt.symm hpr
    have hvle := defect_puncture_le gs ps p r u v hperm hgs hu hv f hf x hx
    have hg := (div_le_iff₀ (by positivity : 0 < 4*slotDefect gs f ∅ p x.1)).mp
      (hgood p hp x.1 hxg hpt)
    have hg' := mul_le_mul_of_nonneg_left hg hsp.le
    have hv' := mul_le_mul_of_nonneg_left hvle hcx.le
    have hb : slotTotal x.2 f (insert v.1 (insert u.1 {v.2})) ≤ 4*sp*w p x.1 := by
      apply (mul_le_mul_iff_of_pos_right hcx).mp
      dsimp [z,sp] at *
      nlinarith
    dsimp [W]
    rw [pairMultiplier_on hslots.2.2.2 _ x.1 (List.mem_cons_of_mem _ hxmem) x.1.1 (Or.inl rfl)]
    exact (div_le_iff₀ (hw p x.1)).mpr hb
  have hsum := list_sum_map_le_const (slotPunctures ps)
    (fun x => slotTotal x.2 f (insert v.1 (insert u.1 {v.2}))/W x.1.1) (4*sp) hsink
  rw [slotPunctures_length] at hsum
  have hcoef : sd*rootCoefficient ps f {v.2} v.1 u.1 W ≤ 4*sd/z+1+8*(ps.length:ℝ) := by
    unfold rootCoefficient
    rw [heqsp f,hWp,hWd]
    dsimp only
    rw [mul_one]
    change sd*(1/(sp*w p r)+1/sd+2/(sp*sd)*_) ≤ _
    have h₁ := mul_le_mul_of_nonneg_left hfirst hsd.le
    have h₂ := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2/sp by positivity)
    have heq (a b : ℝ) : sd*(a+1/sd+2/(sp*sd)*b) = sd*a+1+(2/sp)*b := by
      field_simp

    rw [heq]
    have heq' : 2/sp*((ps.length:ℝ)*(4*sp)) = 8*(ps.length:ℝ) := by
      field_simp
      ; ring
    rw [heq'] at h₂
    calc
      _ ≤ sd*(4/z)+1+8*(ps.length:ℝ) := by linarith only [h₁,h₂]
      _ = _ := by ring
  have he := slot_energy_le_chain gs ps {v.2} v.1 u.1 W w f H hw hf
    (defect_vertex_identification gs ps p r u v hperm hgs hu hv w)
  have ht := transport_graph_bound ps f H {v.2} v.1 u.1 W hf hsig hne hpA hdA hbase hW hws
  have hcp := rootCoefficient_pos ps f hf {v.2} v.1 u.1 W hbase hW
  have hD : 0 ≤ D := restrictedEnergy_nonneg _ _ _ _ _ (by
    intro ST _
    exact le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le))
  have htnew := mul_le_mul_of_nonneg_left ht hsd.le
  rw [← mul_assoc] at htnew
  have hb := htnew.trans
    ((mul_le_mul_of_nonneg_left he (mul_nonneg hsd.le hcp.le)).trans
      (mul_le_mul_of_nonneg_right hcoef hD))
  simpa only [heqsp f,heqsp (fun S => f S*H S),← mul_assoc] using hb

end DefectTransport

section DefectMeans
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance50 : Fintype Γ] [sectionInstance51 : DecidableEq Γ]

omit sectionInstance50 sectionInstance51 in
lemma orientPair_same [Fintype Γ] [DecidableEq Γ] (p : Γ × Γ) (b : Bool) : SamePair p (orientPair p b) := by
  cases b <;> simp [orientPair,SamePair]

lemma slotTotal_four (gs ps : List (Γ × Γ)) (p r : Γ × Γ)
    (hperm : gs.Perm (p::r::ps)) (hgs : SlotsFresh gs ∅) (f : Set Γ → ℝ) :
    ∑ o : Bool × Bool, slotTotal ps f {(orientPair p o.1).1,(orientPair r o.2).2} =
      slotTotal gs f ∅ := by
  have hslots := (SlotsFresh.perm hperm ∅).mp hgs
  have hr₁ : r.1 ∉ (insert p.1 (∅ : Set Γ)) := fun hx => hslots.2.2.2.2.1 (by
    simp only [Set.mem_insert_iff] at hx ⊢; tauto)
  have hr₂ : r.2 ∉ (insert p.1 (∅ : Set Γ)) := fun hx => hslots.2.2.2.2.2.1 (by
    simp only [Set.mem_insert_iff] at hx ⊢; tauto)
  have hr₃ : r.1 ∉ (insert p.2 (∅ : Set Γ)) := fun hx => hslots.2.2.2.2.1 (Or.inr hx)
  have hr₄ : r.2 ∉ (insert p.2 (∅ : Set Γ)) := fun hx => hslots.2.2.2.2.2.1 (Or.inr hx)
  rw [slotTotal_perm hperm f,slotTotal_cons p (r::ps) f ∅ hslots.1 hslots.2.1 hslots.2.2.1,
    slotTotal_cons r ps f _ hslots.2.2.2.1 hr₁ hr₂,
    slotTotal_cons r ps f _ hslots.2.2.2.1 hr₃ hr₄]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,orientPair,Bool.false_eq_true,
    ite_false,ite_true, if_true,Prod.fst_swap,Prod.snd_swap,insert_empty_eq]
  rw [Set.pair_comm r.1 p.1,Set.pair_comm r.2 p.1,Set.pair_comm r.1 p.2,Set.pair_comm r.2 p.2]
  ring

lemma weighted_square_mean {J : Type*} [Fintype J] (w x : J → ℝ) (hw : ∀ j, 0 < w j) :
    (∑ j, w j*x j)^2/(∑ j, w j) ≤ ∑ j, w j*(x j)^2 := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun j => w j*x j) (fun j _ => hw j)
  have heq : (∑ j, (w j*x j)^2/w j) = ∑ j, w j*(x j)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    field_simp [ne_of_gt (hw j)]

  rw [heq] at h
  exact h

theorem defect_mean_bound (gs : List (Γ × Γ)) (p r : Γ × Γ)
    (hgs : SlotsFresh gs ∅) (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r)
    (f H : Set Γ → ℝ) (hf : ∀ S, 0 < f S) (hsig : HasSlotSignature f)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r) :
    slotTotal gs f ∅ *
      (slotDefect gs (fun S => f S*H S) ∅ p r/slotDefect gs f ∅ p r -
        slotTotal gs (fun S => f S*H S) ∅/slotTotal gs f ∅)^2 ≤
      (8+32*(gs.length:ℝ))*restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  let ps := (gs.erase p).erase r
  have hperm : gs.Perm (p::r::ps) := slots_perm_two hp hr hpr
  let z := slotTotal gs f ∅
  let m := slotDefect gs (fun S => f S*H S) ∅ p r/slotDefect gs f ∅ p r
  let s : Bool × Bool → ℝ := fun o => slotTotal ps f {(orientPair p o.1).1,(orientPair r o.2).2}
  let a : Bool × Bool → ℝ := fun o => slotTotal ps (fun S => f S*H S)
    {(orientPair p o.1).1,(orientPair r o.2).2}
  let D := restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅
  have hz : 0 < z := slotTotal_pos gs f hf ∅ hgs
  have hs : ∀ o, 0 < s o := by
    intro o
    have hh := (orientPair_same p o.1).fresh_two (orientPair_same r o.2) ps ∅
      ((SlotsFresh.perm hperm ∅).mp hgs)
    apply slotTotal_pos ps f hf _ (hh.2.2.2.2.2.2.mono _)
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl <;> simp
  have hsum : ∑ o, s o = z := slotTotal_four gs ps p r hperm hgs f
  have hsumA : ∑ o, a o = slotTotal gs (fun S => f S*H S) ∅ :=
    slotTotal_four gs ps p r hperm hgs _
  have ha (o : Bool × Bool) : s o*(m-a o/s o) = s o*m-a o := by
    field_simp [ne_of_gt (hs o)]

  have hmean := weighted_square_mean s (fun o => m-a o/s o) hs
  simp_rw [ha] at hmean
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,hsum,hsumA] at hmean
  have heq : (z*m-slotTotal gs (fun S => f S*H S) ∅)^2/z =
      z*(m-slotTotal gs (fun S => f S*H S) ∅/z)^2 := by
    field_simp

  rw [heq] at hmean
  have hc (o : Bool × Bool) : s o*(m-a o/s o)^2 ≤
      (4*s o/z+1+8*(ps.length:ℝ))*D :=
    defect_conditional_transport gs ps p r (orientPair p o.1) (orientPair r o.2)
      hperm hgs (orientPair_same p o.1) (orientPair_same r o.2) f H hf hsig w hw hgood
  have hsumc := Finset.sum_le_sum (fun o (_ : o ∈ (Finset.univ : Finset (Bool × Bool))) => hc o)
  have hsumcoef : (∑ o : Bool × Bool, (4*s o/z+1+8*(ps.length:ℝ))*D) =
      (8+32*(ps.length:ℝ))*D := by
    rw [← Finset.sum_mul]
    congr 1
    simp only [Finset.sum_add_distrib,← Finset.sum_div,← Finset.mul_sum,hsum]
    simp [ne_of_gt hz]
    ; ring
  rw [hsumcoef] at hsumc
  have hD : 0 ≤ D := restrictedEnergy_nonneg _ _ _ _ _ (by
    intro ST _
    exact le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le))
  have hlen : (ps.length:ℝ) ≤ gs.length := by
    have hh := hperm.length_eq
    simp only [List.length_cons] at hh
    exact_mod_cast (show ps.length ≤ gs.length by omega)
  exact (hmean.trans hsumc).trans (mul_le_mul_of_nonneg_right (by linarith) hD)

end DefectMeans

section Observable
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance52 : Fintype Γ] [DecidableEq Γ]

lemma observableProjection_plain (gs : List (Γ × Γ)) (f H : Set Γ → ℝ) (S : Set Γ)
    (h : PlainState gs S) : observableProjection gs f H S = H S := by
  unfold observableProjection
  rw [dite_eq_right]
  rintro ⟨p,r,hpr⟩
  exact hpr.not_plain h
lemma observableProjection_defect (gs : List (Γ × Γ)) (f H : Set Γ → ℝ) (S : Set Γ)
    {p r : Γ × Γ} (h : DefectState gs p r S) : observableProjection gs f H S = defectMean gs f H p r := by
  have he : ∃ p r, DefectState gs p r S := ⟨p,r,h⟩
  unfold observableProjection
  rw [dite_eq_left he]
  have hh := he.choose_spec.choose_spec.unique h
  exact congrArg₂ (defectMean gs f H) hh.1 hh.2

omit sectionInstance52 in
lemma defectTypes_card_le [Fintype Γ] (gs : List (Γ × Γ)) :
    (defectTypes gs).card ≤ gs.length*gs.length := by
  calc
    _ ≤ gs.toFinset.card*gs.toFinset.card := by simp [defectTypes,Finset.offDiag_card]
    _ ≤ _ := Nat.mul_le_mul (List.toFinset_card_le _) (List.toFinset_card_le _)

lemma plain_center_eq_variance (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f H : Set Γ → ℝ) (hf : ∀ S, 0 < f S) :
    (∑ S ∈ Finset.univ.filter (PlainState gs), f S*(H S-plainMean gs f H)^2) =
      slotVariance gs f H ∅ := by
  have hz := slotTotal_pos gs f hf ∅ hgs
  rw [slotTotal_eq_plain_sum gs hgs hcover] at hz
  unfold plainMean
  rw [slotTotal_eq_plain_sum gs hgs hcover,slotTotal_eq_plain_sum gs hgs hcover,
    finite_center_at_mean _ _ _ (ne_of_gt hz),slotVariance_eq_plain_variance gs hgs hcover]

lemma projection_center_decomposition (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f H : Set Γ → ℝ) (hf : ∀ S, 0 < f S) :
    (∑ S ∈ chainStates gs, chainWeight gs w f S*
      (observableProjection gs f H S-plainMean gs f H)^2) = slotVariance gs f H ∅ +
      ∑ pr ∈ defectTypes gs, w pr.1 pr.2*slotDefect gs f ∅ pr.1 pr.2*
        (defectMean gs f H pr.1 pr.2-plainMean gs f H)^2 := by
  simp only [chainWeight,mul_assoc]
  rw [chain_sum_decomposition]
  congr 1
  · rw [← plain_center_eq_variance gs hgs hcover f H hf]
    apply Finset.sum_congr rfl
    intro S hS
    rw [observableProjection_plain gs f H S (Finset.mem_filter.mp hS).2]
  · apply Finset.sum_congr rfl
    intro pr hm
    obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr).mp hm
    rw [slotDefect_eq_defect_sum gs hgs hcover f pr.1 pr.2 hp hr hpr,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    rw [observableProjection_defect gs f H S (Finset.mem_filter.mp hS).2]

lemma projection_center_bound (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hw : ∀ p r, 0 < w p r) (f H : Set Γ → ℝ) (hf : ∀ S, 0 < f S)
    (hsig : HasSlotSignature f)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    (∑ S ∈ chainStates gs, chainWeight gs w f S*
      (observableProjection gs f H S-plainMean gs f H)^2) ≤
      ((gs.length:ℝ)*(1+8*(gs.length:ℝ))+4*((defectTypes gs).card:ℝ)*(8+32*(gs.length:ℝ)))*
        restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  rw [projection_center_decomposition gs hgs hcover w f H hf]
  have hp := transversal_variance_bound gs f H w hf hsig hgs hw hlower
  let D := restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅
  have hd : ∀ pr ∈ defectTypes gs,
      w pr.1 pr.2*slotDefect gs f ∅ pr.1 pr.2*(defectMean gs f H pr.1 pr.2-plainMean gs f H)^2 ≤
        4*(8+32*(gs.length:ℝ))*D := by
    intro pr hm
    obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr).mp hm
    have hu := (le_div_iff₀ (slotDefect_pos gs f hf ∅ hgs pr.1 pr.2 hp hr hpr)).mp
      (hupper pr.1 hp pr.2 hr hpr)
    have ht := defect_mean_bound gs pr.1 pr.2 hgs hp hr hpr f H hf hsig w hw hlower
    change slotTotal gs f ∅*(defectMean gs f H pr.1 pr.2-plainMean gs f H)^2 ≤ _ at ht
    have hh := mul_le_mul_of_nonneg_right hu
      (sq_nonneg (defectMean gs f H pr.1 pr.2-plainMean gs f H))
    dsimp only [D]
    linarith
  have hs := Finset.sum_le_sum (fun pr hpr => hd pr hpr)
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  dsimp only [D] at hs
  nlinarith

end Observable

open scoped BigOperators Classical

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
      · simp only [hs,true_and,ite_true, if_true]
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
  simp only [EdgeRespects,Respects,Set.empty_subset,Set.empty_disjoint,and_self,ite_true, if_true]
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

lemma centered_mean (f : X → ℝ) : C.mean (fun x => f x-C.mean f) = 0 := by
  unfold mean
  simp [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,C.normalized]

lemma inner_center_right (f g : X → ℝ) (hf : C.mean f = 0) (a : ℝ) :
    C.inner f (fun x => g x-a) = C.inner f g := by
  rw [C.inner_sub_right]
  have hz : C.inner f (fun _ => a) = 0 := by
    change (∑ x,C.π x*f x*a) = 0
    rw [← Finset.sum_mul]
    change C.mean f*a = 0
    rw [hf,zero_mul]
  rw [hz,sub_zero]

end FiniteChain
section ProjectionBridge
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance61 : Fintype Γ] [sectionInstance62 : DecidableEq Γ]

omit sectionInstance61 sectionInstance62 in
lemma ClassObservable.sub_const [Fintype Γ] [DecidableEq Γ] {gs : List (Γ × Γ)} {G : Set Γ → ℝ}
    (hG : ClassObservable gs G) (a : ℝ) : ClassObservable gs (fun S => G S-a) := by
  intro p r S T hS hT
  dsimp only
  rw [hG p r S T hS hT]

lemma defect_pairing_projection (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f G H : Set Γ → ℝ)
    (hf : ∀ S,0 < f S) (hG : ClassObservable gs G)
    (p r : Γ × Γ) (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r) :
    (∑ S ∈ Finset.univ.filter (DefectState gs p r), f S*G S*H S) =
    ∑ S ∈ Finset.univ.filter (DefectState gs p r), f S*G S*observableProjection gs f H S := by
  let t := Finset.univ.filter (DefectState gs p r)
  have hz := slotDefect_pos gs f hf ∅ hgs p r hp hr hpr
  rw [slotDefect_eq_defect_sum gs hgs hcover f p r hp hr hpr] at hz
  have ht : t.Nonempty := by
    by_contra h
    have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    change 0 < ∑ S ∈ t,f S at hz
    rw [he,Finset.sum_empty] at hz
    exact lt_irrefl _ hz
  obtain ⟨T,hT⟩ := ht
  have hTp : DefectState gs p r T := (Finset.mem_filter.mp hT).2
  have hc (S : Set Γ) (hS : S ∈ t) : G S = G T :=
    hG p r S T (Finset.mem_filter.mp hS).2 hTp
  change (∑ S ∈ t,f S*G S*H S) = ∑ S ∈ t,f S*G S*observableProjection gs f H S
  calc
    _ = G T*(∑ S ∈ t,f S*H S) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [hc S hS]; ring
    _ = G T*((∑ S ∈ t,f S)*defectMean gs f H p r) := by
      congr 1
      unfold defectMean
      rw [slotDefect_eq_defect_sum gs hgs hcover f p r hp hr hpr,
        slotDefect_eq_defect_sum gs hgs hcover (fun S => f S*H S) p r hp hr hpr]
      change _ = (∑ S ∈ t,f S)*((∑ S ∈ t,f S*H S)/(∑ S ∈ t,f S))
      have hzt : (∑ S ∈ t,f S) ≠ 0 := hz.ne'
      field_simp [hzt]
    _ = _ := by
      rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [hc S hS,observableProjection_defect gs f H S (Finset.mem_filter.mp hS).2]
      ring

lemma chain_pairing_projection (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G H : Set Γ → ℝ) (hf : ∀ S,0 < f S) (hG : ClassObservable gs G) :
    (∑ S ∈ chainStates gs,chainWeight gs w f S*G S*H S) =
      ∑ S ∈ chainStates gs,chainWeight gs w f S*G S*observableProjection gs f H S := by
  simp only [chainWeight,mul_assoc]
  rw [chain_sum_decomposition,chain_sum_decomposition]
  congr 1
  · apply Finset.sum_congr rfl
    intro S hS
    rw [observableProjection_plain gs f H S (Finset.mem_filter.mp hS).2]
  · apply Finset.sum_congr rfl
    intro pr hpr
    obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr).mp hpr
    congr 1
    simpa only [mul_assoc] using defect_pairing_projection gs hgs hcover f G H hf hG pr.1 pr.2 hp hr hpr

omit sectionInstance61 sectionInstance62 in
lemma extendChainFun_apply [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (H : ChainIndex gs → ℝ) (S : ChainIndex gs) :
    extendChainFun gs H S.val = H S := by simp [extendChainFun,S.property]

end ProjectionBridge

section ObservableMSE
open scoped BigOperators Classical
variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma metropolisChain_inner (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G H : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) :
    (metropolisChain gs hgs hne hcover w f hw hf).inner (fun S => G S.val) (fun S => H S.val) =
    (∑ S ∈ chainStates gs,chainWeight gs w f S*G S*H S)/chainTotal gs w f := by
  change (∑ S : ChainIndex gs,(chainWeight gs w f S.val/chainTotal gs w f)*G S.val*H S.val) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,chain_sum_subtype]

lemma metropolisChain_mean (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) :
    (metropolisChain gs hgs hne hcover w f hw hf).mean (fun S => G S.val) = chainMean gs w f G := by
  change (∑ S : ChainIndex gs,(chainWeight gs w f S.val/chainTotal gs w f)*G S.val) = _
  simp_rw [div_mul_eq_mul_div]
  unfold chainMean
  rw [← Finset.sum_div,chain_sum_subtype]

lemma metropolisChain_variance (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) :
    (metropolisChain gs hgs hne hcover w f hw hf).variance (fun S => G S.val) = chainVariance gs w f G := by
  rw [FiniteChain.variance,metropolisChain_mean]
  rw [metropolisChain_inner gs hgs hne hcover w f (fun S => G S-chainMean gs w f G) (fun S => G S-chainMean gs w f G) hw hf]
  unfold chainVariance
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  ring

end ObservableMSE

open Set

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

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

end CommonBasesFPRAS

open CommonBasesFPRAS

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryContraction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-degree binary cubic contraction

The full-matrix cubic contraction in paper 200-02,
Lemma `lem:binary-contraction`, follows from the generic spectral theorem
`CommonBasesFPRAS.cubic_signature` and its closed-limit lemma. A symmetric
cubic tensor is positive on distinct triples and zero on repetitions;
its coordinate slices have the quadratic signature; contraction by an
arbitrary nonnegative vector, in particular a pair indicator, preserves
that signature on the full remaining index set.

There is no assumption of positivity on unrelated subset cardinalities.
-/

namespace ContingencyTables.BinaryContraction

open scoped BigOperators Topology Classical
open LinearMap (BilinForm)
open CommonBasesFPRAS

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma complement_degreePositive (f : Set I → ℝ) (k : ℕ) (hk : k ≤ Fintype.card I)
    (hpos : DegreePositive f k) : DegreePositive (complementWeight f) (Fintype.card I - k) := by
  classical
  intro U hU
  apply hpos
  have hc := U.ncard_add_ncard_compl
  simp only [Nat.card_eq_fintype_card] at hc
  omega

end ContingencyTables.BinaryContraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LaminarSignature
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-level laminar kernel in contingency-table weights

The factor groups in the sampling paper's laminar-signature lemma are line
coordinate sets, with one nested small-slot subset in each line. Row and
column coordinates belong to separate lines. The normalized kernel
decomposition gives the quadratic one-positive-direction property.
-/

namespace ContingencyTables

open scoped BigOperators
open LinearMap (BilinForm)

section TwoLevel

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- The line/inner two-removal kernel has positive inertia at most one in
quadratic-form language. Its proof uses the actual matrix decomposition. -/
theorem twoLevelKernel_onePositive (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (hγ0 : ∀ g, 0 ≤ γ g) (hγ1 : ∀ g, γ g ≤ 1) (hδ1 : ∀ g, δ g ≤ 1) :
    OnePositiveDirection (twoLevelKernel line inner γ δ).toBilin' := by
  refine onePositiveDirection_of_kernel _ ?_ (vectorSum (fun _ : I => 1)) ?_
  · intro x y
    rw [twoLevelKernel_form, twoLevelKernel_form]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro g _
      ring
  · intro v hv
    rw [twoLevelKernel_form, hv, zero_mul, zero_sub]
    apply neg_nonpos.mpr
    apply Finset.sum_nonneg
    intro g _
    apply add_nonneg
    · exact mul_nonneg (sub_nonneg.mpr (hγ1 g)) (mul_self_nonneg _)
    · exact mul_nonneg (mul_nonneg (hγ0 g) (sub_nonneg.mpr (hδ1 g))) (mul_self_nonneg _)

end TwoLevel

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DegreeCompletion
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive completion of a single valid degree

A fixed-degree weight is extended by the constant weight one on every
other degree. All off-degree signatures are proved, and all coefficient
sums at the original degree are unchanged. This lets the existing general
nonnegative-derivative theorem retain contracted coordinates without
assuming positivity or signatures of the original weight at other degrees.
-/

namespace ContingencyTables.DegreeCompletion

open scoped BigOperators Classical Topology
open CommonBasesFPRAS BinaryContraction

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma constant_face_signature (A : Set Γ) :
    CommonBasesFPRAS.OnePositive (faceHessian (fun _ : Set Γ => (1 : ℝ)) A).toBilin' := by
  let K := twoLevelKernel (fun i : {i // i ∉ A} => i) (fun _ => false)
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
  have heq : faceHessian (fun _ : Set Γ => (1 : ℝ)) A = K := by
    ext i j
    simp [faceHessian, K, twoLevelKernel]
  rw [heq]
  apply (signature_iff _ (matrix_bilin_symm _ (by intro i j; simp [K, twoLevelKernel, eq_comm]))).mp
  exact twoLevelKernel_onePositive _ _ _ _ (by intro i; norm_num)
    (by intro i; norm_num) (by intro i; norm_num)

lemma completeDegree_face_signature (f : Set Γ → ℝ) (k : ℕ)
    (hsig : AdditionProperty f k) (A : Set Γ) :
    CommonBasesFPRAS.OnePositive (faceHessian (completeDegree f k) A).toBilin' := by
  by_cases hA : A.ncard + 2 = k
  · have heq : faceHessian (completeDegree f k) A = faceHessian f A := by
      ext i j
      by_cases hij : i = j
      · simp [faceHessian, hij]
      simp only [faceHessian, hij, ite_false, completeDegree]
      rw [ite_eq_left ((ncard_union_pair A i j hij).trans hA)]
    rw [heq]
    exact hsig A hA
  · have heq : faceHessian (completeDegree f k) A = faceHessian (fun _ => (1 : ℝ)) A := by
      ext i j
      by_cases hij : i = j
      · simp [faceHessian, hij]
      simp only [faceHessian, hij, ite_false, completeDegree]
      rw [ite_eq_right (by rw [ncard_union_pair A i j hij]; exact hA)]
    rw [heq]
    exact constant_face_signature A

/-- Positive directions are handled by the existing cubic spectral theorem.
The cardinality cutoff of a repeated derivative is established at each step. -/
lemma positive_derivatives_signature (f : Set Γ → ℝ) (hf : ∀ A, 0 < f A)
    (hsig : ∀ A, CommonBasesFPRAS.OnePositive (faceHessian f A).toBilin')
    (ds : List (Γ → ℝ)) (hds : ∀ a ∈ ds, ∀ i, 0 < a i) :
    FullPositive (coeffDerivs ds f) ds.length ∧
      ∀ A, CommonBasesFPRAS.OnePositive (faceHessian (coeffDerivs ds f) A).toBilin' := by
  induction ds with
  | nil =>
    refine ⟨⟨fun A _ => hf A, ?_⟩, hsig⟩
    intro A hA
    have hcard : A.ncard ≤ Fintype.card Γ := by simpa using Set.ncard_le_card A
    simp only [List.length_nil, Nat.add_zero] at hA
    omega
  | cons a ds ih =>
    have ha := hds a List.mem_cons_self
    obtain ⟨hp, hs⟩ := ih (fun b hb => hds b (List.mem_cons_of_mem _ hb))
    exact ⟨hp.deriv a ha, derivative_face_signature hp hs a ha⟩

/-- The zero coordinates of a direction are reached by an actual positive
perturbation and the proved closedness of the quadratic signature. -/
lemma nonnegative_derivatives_signature (f : Set Γ → ℝ) (hf : ∀ A, 0 < f A)
    (hsig : ∀ A, CommonBasesFPRAS.OnePositive (faceHessian f A).toBilin')
    (ds : List (Γ → ℝ)) (hds : ∀ a ∈ ds, ∀ i, 0 ≤ a i) (A : Set Γ) :
    CommonBasesFPRAS.OnePositive (faceHessian (coeffDerivs ds f) A).toBilin' := by
  let F : ℝ → Matrix {i // i ∉ A} {i // i ∉ A} ℝ := fun t =>
    faceHessian (coeffDerivs (ds.map (fun a i => a i + t)) f) A
  have hzero : F 0 = faceHessian (coeffDerivs ds f) A := by simp [F]
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
        exact continuous_coeffDerivs_perturb ds f _
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact fun t => faceHessian_symm _ A
  · have hpos : ∀ᶠ t in l, 0 < t := self_mem_nhdsWithin
    filter_upwards [hpos] with t ht
    apply (positive_derivatives_signature f hf hsig _ _).2 A
    intro b hb i
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact add_pos_of_nonneg_of_pos (hds a ha i) ht

/-- All retained-coordinate slot signatures of the completion are proved.
The original input is only the single valid-degree addition property. -/
theorem completeDegree_hasSlotSignature (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k) :
    HasSlotSignature (completeDegree f k) := by
  intro ps A
  apply nonnegative_derivatives_signature _ (completeDegree_positive f k hf)
    (completeDegree_face_signature f k hsig) _ _ A
  intro a ha i
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
  exact slotDirection_nonneg _ i

/-- Every nonzero derivative term adds precisely one new element; no
fresh-pair or disjointness assumption is needed for this congruence. -/
lemma coeffDerivs_degree_congr (ds : List (Γ → ℝ)) (f g : Set Γ → ℝ) (k : ℕ)
    (heq : ∀ S, S.ncard = k → f S = g S) (A : Set Γ)
    (hdegree : A.ncard + ds.length = k) : coeffDerivs ds f A = coeffDerivs ds g A := by
  induction ds generalizing A with
  | nil => exact heq A (by simpa using hdegree)
  | cons a ds ih =>
    change coeffDeriv a (coeffDerivs ds f) A = coeffDeriv a (coeffDerivs ds g) A
    unfold coeffDeriv
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ A
    · simp only [ite_eq_left hi]
    · simp only [ite_eq_right hi]
      congr 1
      apply ih (insert i A)
      rw [ncard_insert_eq A i hi]
      simp only [List.length_cons] at hdegree
      omega

lemma slotTotal_completeDegree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) :
    slotTotal ps (completeDegree f k) A = slotTotal ps f A := by
  apply coeffDerivs_degree_congr _ _ _ k
  · intro S hS
    simp [completeDegree, hS]
  · simpa only [List.length_map] using hdegree

lemma slotDefect_completeDegree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) (hps : SlotsFresh ps A)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    slotDefect ps (completeDegree f k) A p r = slotDefect ps f A p r := by
  have hperm := slots_perm_two hp hr hpr
  have hh := (SlotsFresh.perm hperm A).mp hps
  have hrA : r.1 ∉ A := fun h => hh.2.2.2.2.1 (Or.inr (Or.inr h))
  have hrB : r.2 ∉ A := fun h => hh.2.2.2.2.2.1 (Or.inr (Or.inr h))
  unfold slotDefect
  apply slotTotal_completeDegree
  rw [ncard_insert_eq _ r.1 (by simp only [Set.mem_insert_iff, not_or]; exact ⟨hh.2.2.2.1, hrA⟩),
    ncard_insert_eq A r.2 hrB]
  have hlen := hperm.length_eq
  simp only [List.length_cons] at hlen
  omega

end ContingencyTables.DegreeCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PairedComplement
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complementation of paired conditional masses

Complementing a transversal assignment swaps its fixed inclusions and
exclusions and reverses the empty/full defect labels. These are identities
of the actual finite coefficient sums, used to keep the omission and
addition roles of the two factorial lifts separate.
-/

namespace ContingencyTables.PairedComplement

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma paired_children (ps : List (Γ × Γ)) (A B : Set Γ) (p : Γ × Γ)
    (hAB : Disjoint A B) (hps : SlotsFresh (p::ps) (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport (p::ps) = Set.univ) :
    Disjoint (insert p.1 A) (insert p.2 B) ∧
      SlotsFresh ps (insert p.1 A ∪ insert p.2 B) ∧
      insert p.1 A ∪ insert p.2 B ∪ pairSupport ps = Set.univ := by
  obtain ⟨hp, ha, hb, ht⟩ := hps
  refine ⟨?_, ht.mono ?_, ?_⟩
  · simp only [Set.disjoint_insert_left, Set.disjoint_insert_right, Set.mem_insert_iff,
      not_or]
    exact ⟨⟨hp.symm, fun h => hb (Or.inl h)⟩, fun h => ha (Or.inr h), hAB⟩
  · intro x hx
    simp only [Set.mem_union, Set.mem_insert_iff] at hx ⊢
    tauto
  · rw [← hcover, pairSupport_cons]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto

/-- Exact complement identity for a residual paired choice sum. -/
theorem slotTotal_complement (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ) :
    slotTotal ps (complementWeight f) A = slotTotal ps f B := by
  induction ps generalizing A B with
  | nil =>
    have hcompl : Aᶜ = B := by
      ext x
      have hx : x ∈ A ∪ B := by
        have h := Set.mem_univ x
        rw [← hcover] at h
        simpa using h
      constructor
      · intro ha
        exact hx.resolve_left ha
      · intro hb ha
        exact Set.disjoint_left.mp hAB ha hb
    simp only [slotTotal_nil, complementWeight, hcompl]
  | cons p ps ih =>
    have hA := hps.mono Set.subset_union_left
    have hB := hps.mono Set.subset_union_right
    obtain ⟨hd₁, hf₁, hc₁⟩ := paired_children ps A B p hAB hps hcover
    have hswap : SlotsFresh ((p.2,p.1)::ps) (A ∪ B) := by
      refine ⟨hps.1.symm, hps.2.2.1, hps.2.1, ?_⟩
      convert hps.2.2.2 using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      simp only [Set.mem_insert_iff]
      tauto
    have hcovswap : A ∪ B ∪ pairSupport ((p.2,p.1)::ps) = Set.univ := by
      rw [← hcover, pairSupport_cons, pairSupport_cons]
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff]
      tauto
    obtain ⟨hd₂, hf₂, hc₂⟩ := paired_children ps A B (p.2,p.1) hAB hswap hcovswap
    rw [slotTotal_cons p ps _ A hA.1 hA.2.1 hA.2.2.1,
      slotTotal_cons p ps _ B hB.1 hB.2.1 hB.2.2.1,
      ih _ _ hd₁ hf₁ hc₁, ih _ _ hd₂ hf₂ hc₂, add_comm]

/-- Complementation reverses the two distinguished defect labels. -/
theorem slotDefect_complement (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    slotDefect ps (complementWeight f) A p r = slotDefect ps f B r p := by
  let qs := (ps.erase p).erase r
  have hperm : ps.Perm (p::r::qs) := slots_perm_two hp hr hpr
  have hh := (SlotsFresh.perm hperm (A ∪ B)).mp hps
  have hcov : A ∪ B ∪ pairSupport (p::r::qs) = Set.univ := by
    rwa [← pairSupport_perm hperm]
  have hfr : SlotsFresh qs ((insert r.1 (insert r.2 A)) ∪ insert p.1 (insert p.2 B)) := by
    apply hh.2.2.2.2.2.2.mono
    intro x hx
    simp only [Set.mem_union, Set.mem_insert_iff] at hx ⊢
    tauto
  have hab : Disjoint (insert r.1 (insert r.2 A)) (insert p.1 (insert p.2 B)) := by
    have hp₁ : p.1 ∉ A ∪ B := hh.2.1
    have hp₂ : p.2 ∉ A ∪ B := hh.2.2.1
    have hr₁ := hh.2.2.2.2.1
    have hr₂ := hh.2.2.2.2.2.1
    simp only [Set.mem_insert_iff, Set.mem_union, not_or] at hp₁ hp₂ hr₁ hr₂
    apply Set.disjoint_left.mpr
    intro x hx hy
    simp only [Set.mem_insert_iff] at hx hy
    rcases hx with rfl | rfl | hx
    · tauto
    · tauto
    · rcases hy with rfl | rfl | hy
      · tauto
      · tauto
      · exact Set.disjoint_left.mp hAB hx hy
  have hc : insert r.1 (insert r.2 A) ∪ insert p.1 (insert p.2 B) ∪ pairSupport qs = Set.univ := by
    rw [← hcov, pairSupport_cons, pairSupport_cons]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto
  unfold slotDefect
  rw [List.erase_comm r p]
  exact slotTotal_complement qs f _ _ hab hfr hc

end ContingencyTables.PairedComplement

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ObservableVariance
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two-lift transversal variance

The adaptive signed-transport proof from paper 200-02, with its comparison
factor q². The transport weight has addition signatures in complementary
coordinates; the other lift has addition signatures in the original
coordinates. Complement identities, rather than an interchange of those
two signature roles, supply the defect score inequalities.
-/

namespace ContingencyTables.ObservableVariance

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion PairedComplement

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma restrictedEnergy_completeDegree (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (A B : Set Γ) :
    restrictedEnergy (chainEdges gs) (chainConductance gs w (completeDegree f gs.length)) H A B =
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H A B := by
  unfold restrictedEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro ST hST
  have hh := (Finset.mem_filter.mp hST).2
  have hs := hh.1.ncard hgs hcover
  have ht := hh.2.1.ncard hgs hcover
  simp only [chainConductance, completeDegree, hs, ht, ite_true, if_true]

end ContingencyTables.ObservableVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ObservableBounds
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Observable and trace bounds on the actual valid-degree chain

Positive completion is used only to instantiate the existing finite-chain
constructor. All its state weights, conductances, and conditional projections
are proved equal to the original valid-degree quantities.
-/

namespace ContingencyTables.ObservableBounds

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion ObservableVariance

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma observableConstant_lower (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    338*p^5 ≤ observableConstant p q := by
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hq2 : 1 ≤ q^2 := by nlinarith
  have hprod : 1 ≤ p*q^2 := hp.trans (by nlinarith [mul_le_mul_of_nonneg_left hq2 hp0])
  have hbig : 81*p ≤ 9*(p*(1+8*p*q^2)) := by nlinarith
  have htail : 0 ≤ 2*(8+32*p*q^3) := by positivity
  have hi : (338/10 : ℝ)*p ≤ 9*(p*(1+8*p*q^2))+2*(8+32*p*q^3) := by nlinarith
  calc
    338*p^5 = 10*p^4*((338/10 : ℝ)*p) := by ring
    _ ≤ observableConstant p q := mul_le_mul_of_nonneg_left hi (by positivity)

/-- A sharper direct consequence of the existing proved projection bound.
The finite defect-type count is retained until its last numerical estimate. -/
theorem observable_poincare_sharp (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hw : ∀ p r, 0 < w p r) (f H : Set Γ → ℝ) (hf : ∀ S, 0 < f S)
    (hsig : HasSlotSignature f)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    chainVariance gs w f (observableProjection gs f H) ≤
      338*(gs.length:ℝ)^5*chainDirichlet gs w f H := by
  have hΛ := chainTotal_pos gs hgs hcover w f hf hw
  have hm := finite_center_min (chainStates gs) (chainWeight gs w f)
    (observableProjection gs f H) (plainMean gs f H) hΛ
  have hb := projection_center_bound gs hgs hcover w hw f H hf hsig hlower hupper
  let n : ℝ := gs.length
  let D := restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅
  have hD : 0 ≤ D := restrictedEnergy_nonneg _ _ _ _ _ (by
    intro ST _
    exact le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le))
  have hn : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast List.length_pos_iff.mpr hne
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcard : ((defectTypes gs).card:ℝ) ≤ n^2 := by
    dsimp only [n]
    exact_mod_cast (show (defectTypes gs).card ≤ gs.length^2 by simpa [pow_two] using defectTypes_card_le gs)
  have hc : n*(1+8*n)+4*((defectTypes gs).card:ℝ)*(8+32*n) ≤ 169*n^3 := by
    have hn2 : n ≤ n^2 := by nlinarith
    have hn3 : n^2 ≤ n^3 := by nlinarith [mul_le_mul_of_nonneg_left hn2 hn0.le]
    have hh := mul_le_mul_of_nonneg_right hcard (show 0 ≤ 4*(8+32*n) by positivity)
    nlinarith
  have hbound := (hm.trans hb).trans (mul_le_mul_of_nonneg_right hc hD)
  change chainVariance gs w f (observableProjection gs f H) ≤ 338*n^5*(D/(2*n^2*chainTotal gs w f))
  unfold chainVariance chainMean
  apply (div_le_iff₀ hΛ).mpr
  have he : 338*n^5*(D/(2*n^2*chainTotal gs w f))*chainTotal gs w f = 169*n^3*D := by
    field_simp
    ; ring
  rw [he]
  exact hbound

lemma slotDefect_completion_mul (ps : List (Γ × Γ)) (f H : Set Γ → ℝ) (k : ℕ)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) (hps : SlotsFresh ps A)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    slotDefect ps (fun S => completeDegree f k S * H S) A p r =
      slotDefect ps (fun S => f S * H S) A p r := by
  have heq : completeDegree (fun S => completeDegree f k S * H S) k =
      completeDegree (fun S => f S * H S) k := by
    funext S
    unfold completeDegree
    split_ifs with h
    · simp [h]
    · rfl
  rw [← slotDefect_completeDegree ps (fun S => completeDegree f k S * H S) k A hdegree hps p r hp hr hpr,
    heq, slotDefect_completeDegree ps (fun S => f S * H S) k A hdegree hps p r hp hr hpr]

lemma observableProjection_completion (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (hgs : SlotsFresh gs ∅) (S : Set Γ) :
    observableProjection gs (completeDegree f gs.length) H S = observableProjection gs f H S := by
  by_cases he : ∃ p r, DefectState gs p r S
  · obtain ⟨p,r,hpr⟩ := he
    rw [observableProjection_defect gs _ H S hpr, observableProjection_defect gs f H S hpr]
    unfold defectMean
    rw [slotDefect_completion_mul gs f H gs.length ∅ (by simp) hgs p r hpr.1 hpr.2.1 hpr.2.2.1,
      slotDefect_completeDegree gs f gs.length ∅ (by simp) hgs p r hpr.1 hpr.2.1 hpr.2.2.1]
  · simp only [observableProjection, dite_eq_right he]

lemma chainTotal_completion (gs : List (Γ × Γ)) (f : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : chainTotal gs w (completeDegree f gs.length) = chainTotal gs w f := by
  unfold chainTotal chainWeight
  apply Finset.sum_congr rfl
  intro S hS
  have hd := ((Finset.mem_filter.mp hS).2).ncard hgs hcover
  simp only [completeDegree, hd, ite_true, if_true]

lemma chainMean_completion (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : chainMean gs w (completeDegree f gs.length) H = chainMean gs w f H := by
  unfold chainMean
  rw [chainTotal_completion gs f w hgs hcover]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have hd := ((Finset.mem_filter.mp hS).2).ncard hgs hcover
  simp only [chainWeight, completeDegree, hd, ite_true, if_true]

lemma chainVariance_completion (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) :
    chainVariance gs w (completeDegree f gs.length) H = chainVariance gs w f H := by
  unfold chainVariance
  rw [chainTotal_completion gs f w hgs hcover, chainMean_completion gs f H w hgs hcover]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have hd := ((Finset.mem_filter.mp hS).2).ncard hgs hcover
  simp only [chainWeight, completeDegree, hd, ite_true, if_true]

lemma chainDirichlet_completion (gs : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) :
    chainDirichlet gs w (completeDegree f gs.length) H = chainDirichlet gs w f H := by
  unfold chainDirichlet
  rw [chainTotal_completion gs f w hgs hcover, restrictedEnergy_completeDegree gs f H w hgs hcover ∅ ∅]

/-- Observable Poincaré on the original valid-degree weights, with the exact
manuscript constant. Off-degree positivity is absent from its assumptions. -/
theorem validDegree_observable_poincare (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hw : ∀ p r, 0 < w p r) (f H : Set Γ → ℝ)
    (hf : DegreePositive f gs.length) (hsig : AdditionProperty f gs.length)
    (q : ℝ) (hq : 1 ≤ q)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    chainVariance gs w f (observableProjection gs f H) ≤
      observableConstant gs.length q * chainDirichlet gs w f H := by
  let F := completeDegree f gs.length
  have hF := completeDegree_positive f gs.length hf
  have hsF := completeDegree_hasSlotSignature f gs.length hf hsig
  have hlower' : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs F ∅/(4*slotDefect gs F ∅ p r) ≤ w p r := by
    intro p hp r hr hpr
    dsimp [F]
    rw [slotTotal_completeDegree gs f gs.length ∅ (by simp),
      slotDefect_completeDegree gs f gs.length ∅ (by simp) hgs p r hp hr hpr]
    exact hlower p hp r hr hpr
  have hupper' : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs F ∅/slotDefect gs F ∅ p r := by
    intro p hp r hr hpr
    dsimp [F]
    rw [slotTotal_completeDegree gs f gs.length ∅ (by simp),
      slotDefect_completeDegree gs f gs.length ∅ (by simp) hgs p r hp hr hpr]
    exact hupper p hp r hr hpr
  have ht := observable_poincare_sharp gs hgs hne hcover w hw F H hF hsF hlower' hupper'
  have hproj : observableProjection gs F H = observableProjection gs f H :=
    funext (observableProjection_completion gs f H hgs)
  rw [hproj, chainVariance_completion gs f _ w hgs hcover,
    chainDirichlet_completion gs f H w hgs hcover] at ht
  have hD : 0 ≤ chainDirichlet gs w f H := by
    rw [← chainDirichlet_completion gs f H w hgs hcover]
    unfold chainDirichlet
    apply div_nonneg
    · exact restrictedEnergy_nonneg _ _ _ _ _ (by
        intro ST _
        exact le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hF _).le)
          (mul_nonneg (chainMultiplier_pos gs w hw _).le (hF _).le))
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (chainTotal_pos gs hgs hcover w F hF hw).le
  exact ht.trans (mul_le_mul_of_nonneg_right
    (observableConstant_lower gs.length q (by exact_mod_cast List.length_pos_iff.mpr hne) hq) hD)

end ContingencyTables.ObservableBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ComplementChain
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The manuscript's original omission coordinates

Complementation reverses defect labels and their multipliers. We prove the
actual chain energy, conditional projection, and variance identities before
transferring the variance and observable inequalities back to the original
factorial lift f. The final theorems assume its omission property.
-/

namespace ContingencyTables.ComplementChain

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion PairedComplement ObservableVariance ObservableBounds

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

omit [Fintype Γ] [DecidableEq Γ] in
lemma plain_complement (gs : List (Γ × Γ)) (S : Set Γ) :
    PlainState gs Sᶜ ↔ PlainState gs S := by
  unfold PlainState PairSingle
  simp only [Set.mem_compl_iff]
  constructor <;> intro h p hp <;> have hh := h p hp <;> tauto

omit [Fintype Γ] [DecidableEq Γ] in
lemma defect_complement (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) :
    DefectState gs p r Sᶜ ↔ DefectState gs r p S := by
  unfold DefectState PairEmpty PairFull PairSingle
  simp only [Set.mem_compl_iff, not_not]
  constructor
  · rintro ⟨hp,hr,hpr,hep,hfr,hs⟩
    refine ⟨hr,hp,hpr.symm,hfr,hep,?_⟩
    intro t ht htr htp
    have h := hs t ht htp htr
    tauto
  · rintro ⟨hr,hp,hrp,her,hfp,hs⟩
    refine ⟨hp,hr,hrp.symm,hfp,her,?_⟩
    intro t ht htp htr
    have h := hs t ht htr htp
    tauto

omit [Fintype Γ] [DecidableEq Γ] in
lemma state_complement (gs : List (Γ × Γ)) (S : Set Γ) :
    ChainState gs Sᶜ ↔ ChainState gs S := by
  unfold ChainState
  rw [plain_complement]
  constructor
  · rintro (h | ⟨p,r,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r,p,(defect_complement gs p r S).mp h⟩
  · rintro (h | ⟨p,r,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r,p,(defect_complement gs r p S).mpr h⟩

omit [Fintype Γ] [DecidableEq Γ] in
lemma adjacent_complement (S T : Set Γ) : ExchangeAdjacent Sᶜ Tᶜ ↔ ExchangeAdjacent S T := by
  have hf (S T : Set Γ) (h : ExchangeAdjacent S T) : ExchangeAdjacent Sᶜ Tᶜ := by
    obtain ⟨A,a,b,hab,ha,hb,rfl,rfl⟩ := h
    let B := (insert a (insert b A))ᶜ
    refine ⟨B,b,a,hab.symm,?_,?_,?_,?_⟩
    · simp [B]
    · simp [B]
    · ext x
      simp only [B, Set.mem_compl_iff, Set.mem_insert_iff]
      constructor
      · intro hx
        by_cases hxb : x = b
        · exact Or.inl hxb
        · exact Or.inr (by tauto)
      · intro hx
        rcases hx with rfl | hx
        · exact not_or.mpr ⟨hab.symm, hb⟩
        · tauto
    · ext x
      simp only [B, Set.mem_compl_iff, Set.mem_insert_iff]
      constructor
      · intro hx
        by_cases hxa : x = a
        · exact Or.inl hxa
        · exact Or.inr (by tauto)
      · intro hx
        rcases hx with rfl | hx
        · exact not_or.mpr ⟨hab, ha⟩
        · tauto
  exact ⟨fun h => by simpa using hf Sᶜ Tᶜ h, hf S T⟩

lemma multiplier_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (S : Set Γ) :
    chainMultiplier gs (reverseMultiplier w) Sᶜ = chainMultiplier gs w S := by
  by_cases he : ∃ p r, DefectState gs p r S
  · obtain ⟨p,r,h⟩ := he
    rw [chainMultiplier_defect gs _ Sᶜ ((defect_complement gs r p S).mpr h),
      chainMultiplier_defect gs w S h]
    rfl
  · have hec : ¬ ∃ p r, DefectState gs p r Sᶜ := by
      rintro ⟨p,r,h⟩
      exact he ⟨r,p,(defect_complement gs p r S).mp h⟩
    simp only [chainMultiplier, dite_eq_right he, dite_eq_right hec]

lemma weight_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (S : Set Γ) :
    chainWeight gs (reverseMultiplier w) (complementWeight f) Sᶜ = chainWeight gs w f S := by
  simp only [chainWeight, multiplier_complement, complementWeight, compl_compl]

lemma chain_sum_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f J : Set Γ → ℝ) :
    (∑ S ∈ chainStates gs, chainWeight gs (reverseMultiplier w) (complementWeight f) S * J S) =
      ∑ S ∈ chainStates gs, chainWeight gs w f S * J Sᶜ := by
  simp only [chainStates, Finset.sum_filter]
  apply Fintype.sum_equiv complementEquiv
  intro S
  change (if ChainState gs S then _ else 0) = (if ChainState gs Sᶜ then _ else 0)
  rw [state_complement]
  by_cases h : ChainState gs S
  · simp only [ite_eq_left h]
    have hw := weight_complement gs w f Sᶜ
    simp only [compl_compl] at hw
    rw [hw]
    simp only [complementEquiv, Equiv.coe_fn_mk, compl_compl]
  · simp only [ite_eq_right h]

lemma total_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) :
    chainTotal gs (reverseMultiplier w) (complementWeight f) = chainTotal gs w f := by
  simpa only [chainTotal, mul_one] using chain_sum_complement gs w f (fun _ => 1)

lemma mean_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ) :
    chainMean gs (reverseMultiplier w) (complementWeight f) (complementWeight H) = chainMean gs w f H := by
  unfold chainMean
  rw [total_complement, chain_sum_complement]
  simp only [complementWeight, compl_compl]

lemma variance_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ) :
    chainVariance gs (reverseMultiplier w) (complementWeight f) (complementWeight H) =
      chainVariance gs w f H := by
  unfold chainVariance
  rw [total_complement, mean_complement, chain_sum_complement]
  simp only [complementWeight, compl_compl]

lemma conductance_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (ST : Set Γ × Set Γ) :
    chainConductance gs (reverseMultiplier w) (complementWeight f) (ST.1ᶜ,ST.2ᶜ) =
      chainConductance gs w f ST := by
  simp only [chainConductance, multiplier_complement, complementWeight, compl_compl]

lemma energy_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ) :
    restrictedEnergy (chainEdges gs) (chainConductance gs (reverseMultiplier w) (complementWeight f))
        (complementWeight H) ∅ ∅ =
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  have hr (ST : Set Γ × Set Γ) : EdgeRespects ∅ ∅ ST := by simp [EdgeRespects, Respects]
  unfold restrictedEnergy
  simp only [hr, ite_true, if_true, chainEdges, Finset.sum_filter]
  congr 1
  let E : (Set Γ × Set Γ) ≃ (Set Γ × Set Γ) := Equiv.prodCongr complementEquiv complementEquiv
  apply Fintype.sum_equiv E
  intro ST
  change (if ChainState gs ST.1 ∧ ChainState gs ST.2 ∧ ExchangeAdjacent ST.1 ST.2 then _ else 0) =
    (if ChainState gs ST.1ᶜ ∧ ChainState gs ST.2ᶜ ∧ ExchangeAdjacent ST.1ᶜ ST.2ᶜ then _ else 0)
  rw [state_complement, state_complement, adjacent_complement]
  by_cases h : ChainState gs ST.1 ∧ ChainState gs ST.2 ∧ ExchangeAdjacent ST.1 ST.2
  · simp only [ite_eq_left h]
    have hc := conductance_complement gs w f (ST.1ᶜ,ST.2ᶜ)
    simp only [compl_compl] at hc
    rw [hc]
    rfl
  · simp only [ite_eq_right h]

lemma dirichlet_complement (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f H : Set Γ → ℝ) :
    chainDirichlet gs (reverseMultiplier w) (complementWeight f) (complementWeight H) =
      chainDirichlet gs w f H := by
  unfold chainDirichlet
  rw [total_complement, energy_complement]

lemma plain_mass_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ) :
    slotTotal gs (complementWeight f) ∅ = slotTotal gs f ∅ := by
  exact slotTotal_complement gs f ∅ ∅ (by simp) (by simpa using hgs) (by simpa using hcover)

lemma defect_mass_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ)
    (p r : Γ × Γ) (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r) :
    slotDefect gs (complementWeight f) ∅ p r = slotDefect gs f ∅ r p := by
  exact slotDefect_complement gs f ∅ ∅ (by simp) (by simpa using hgs) (by simpa using hcover) p r hp hr hpr

lemma projection_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f H : Set Γ → ℝ) :
    observableProjection gs (complementWeight f) (complementWeight H) =
      complementWeight (observableProjection gs f H) := by
  have hmul : (fun S => complementWeight f S * complementWeight H S) =
      complementWeight (fun S => f S * H S) := rfl
  funext S
  change observableProjection gs (complementWeight f) (complementWeight H) S =
    observableProjection gs f H Sᶜ
  by_cases he : ∃ p r, DefectState gs p r S
  · obtain ⟨p,r,h⟩ := he
    have hc : DefectState gs r p Sᶜ := (defect_complement gs r p S).mpr h
    rw [observableProjection_defect gs _ _ S h, observableProjection_defect gs f H Sᶜ hc]
    unfold defectMean
    rw [hmul, defect_mass_complement gs hgs hcover _ p r h.1 h.2.1 h.2.2.1,
      defect_mass_complement gs hgs hcover f p r h.1 h.2.1 h.2.2.1]
  · have hec : ¬ ∃ p r, DefectState gs p r Sᶜ := by
      rintro ⟨p,r,h⟩
      exact he ⟨r,p,(defect_complement gs p r S).mp h⟩
    simp only [observableProjection, dite_eq_right he, dite_eq_right hec, complementWeight]

/-- The paper's observable Poincaré theorem for the literal first factorial
lift, assuming its omission property only at the actual subset degree. -/
theorem omission_observable_poincare (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hw : ∀ p r, 0 < w p r) (f H : Set Γ → ℝ)
    (hf : DegreePositive f gs.length) (hsig : OmissionProperty f gs.length)
    (q : ℝ) (hq : 1 ≤ q)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    chainVariance gs w f (observableProjection gs f H) ≤
      observableConstant gs.length q * chainDirichlet gs w f H := by
  have hcard := slots_ground_card gs hgs hcover
  have hhalf : Fintype.card Γ - gs.length = gs.length := by omega
  have hfc : DegreePositive (complementWeight f) gs.length := by
    simpa only [hhalf] using complement_degreePositive f gs.length (by omega) hf
  have hsf : AdditionProperty (complementWeight f) gs.length := by
    simpa only [OmissionProperty, hhalf] using hsig
  have hl : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs (complementWeight f) ∅/(4*slotDefect gs (complementWeight f) ∅ p r) ≤ reverseMultiplier w p r := by
    intro p hp r hr hpr
    rw [plain_mass_complement gs hgs hcover, defect_mass_complement gs hgs hcover f p r hp hr hpr]
    exact hlower r hr p hp hpr.symm
  have hu : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      reverseMultiplier w p r ≤ 4*slotTotal gs (complementWeight f) ∅/slotDefect gs (complementWeight f) ∅ p r := by
    intro p hp r hr hpr
    rw [plain_mass_complement gs hgs hcover, defect_mass_complement gs hgs hcover f p r hp hr hpr]
    exact hupper r hr p hp hpr.symm
  have ht := validDegree_observable_poincare gs hgs hne hcover (reverseMultiplier w)
    (fun p r => hw r p) (complementWeight f) (complementWeight H) hfc hsf q hq hl hu
  rwa [projection_complement gs hgs hcover, variance_complement, dirichlet_complement] at ht

end ContingencyTables.ComplementChain

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ObservableTrajectory
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Warm trajectory averages of the paper's class observables

The dual estimate is derived from the proved original-coordinate observable
Poincaré inequality. The existing finite-chain covariance and warm moment
lemmas then give the paper's 2UKobs Var/N mean-square bound. Completion is
absent from the observable mean, variance, and warm-start law.
-/

namespace ContingencyTables.ObservableTrajectory

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion ObservableVariance ObservableBounds ComplementChain

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Dual observable bound for the genuine omission-lift chain. -/
theorem omission_chain_dual_oai (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r)
    (hf : DegreePositive f gs.length) (hsig : OmissionProperty f gs.length)
    (q : ℝ) (hq : 1 ≤ q) (hG : ClassObservable gs G)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r)
    (H : ChainIndex gs → ℝ) :
    let C := metropolisChain gs hgs hne hcover w (completeDegree f gs.length) hw
      (completeDegree_positive f gs.length hf)
    let g := fun S : ChainIndex gs => G S.val-chainMean gs w f G
    (C.inner g H)^2 ≤ observableConstant gs.length q*C.inner g g*C.energy H := by
  let F := completeDegree f gs.length
  have hF := completeDegree_positive f gs.length hf
  let C := metropolisChain gs hgs hne hcover w F hw hF
  let a := chainMean gs w f G
  let g := fun S : ChainIndex gs => G S.val-a
  let H' := extendChainFun gs H
  let QH := fun S : ChainIndex gs => observableProjection gs F H' S.val
  have hext : (fun S : ChainIndex gs => H' S.val) = H := by
    funext S
    exact extendChainFun_apply gs H S
  have hmean : C.mean g = 0 := by
    have hm := metropolisChain_mean gs hgs hne hcover w F G hw hF
    rw [chainMean_completion gs f G w hgs hcover] at hm
    change C.mean (fun S => G S.val-a) = 0
    change C.mean (fun S : ChainIndex gs => G S.val) = a at hm
    rw [← hm]
    exact C.centered_mean _
  have hpair : C.inner g H = C.inner g QH := by
    rw [← hext]
    change C.inner (fun S => G S.val-a) (fun S => H' S.val) =
      C.inner (fun S => G S.val-a) (fun S => observableProjection gs F H' S.val)
    dsimp only [C]
    rw [metropolisChain_inner gs hgs hne hcover w F (fun S => G S-a) H' hw hF,
      metropolisChain_inner gs hgs hne hcover w F (fun S => G S-a) (observableProjection gs F H') hw hF]
    exact congrArg (fun t => t/chainTotal gs w F)
      (chain_pairing_projection gs hgs hcover w F (fun S => G S-a) H' hF (hG.sub_const a))
  have hbound : C.variance QH ≤ observableConstant gs.length q*C.energy H := by
    change (metropolisChain gs hgs hne hcover w F hw hF).variance
      (fun S => observableProjection gs F H' S.val) ≤ _
    rw [metropolisChain_variance]
    have hb := omission_observable_poincare gs hgs hne hcover w hw f H' hf hsig q hq hlower hupper
    have hproj : observableProjection gs F H' = observableProjection gs f H' :=
      funext (observableProjection_completion gs f H' hgs)
    rw [hproj, chainVariance_completion gs f _ w hgs hcover]
    rw [← chainDirichlet_completion gs f H' w hgs hcover,
      ← metropolisChain_energy gs hgs hne hcover w F H' hw hF, hext] at hb
    exact hb
  dsimp only
  rw [hpair, ← C.inner_center_right g QH hmean (C.mean QH)]
  calc
    _ ≤ C.inner g g*C.variance QH := C.inner_cauchy _ _
    _ ≤ C.inner g g*(observableConstant gs.length q*C.energy H) :=
      mul_le_mul_of_nonneg_left hbound (C.inner_nonneg g)
    _ = _ := by ring

end ContingencyTables.ObservableTrajectory

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual_oai.{u_1} := @OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual_oai.{u_1}
