-- Prove2me | solution 1 for OAI.ContingencyTables.RootedTargetMixing.targetTrace_poincare
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:16:44.360255+00:00
-- url     : https://prove2.me/submissions/c5cd246b-9bc5-430d-865f-39c431a8dc98

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

section ProjectionBridge
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance61 : Fintype Γ] [sectionInstance62 : DecidableEq Γ]

omit sectionInstance61 sectionInstance62 in
lemma extendChainFun_apply [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (H : ChainIndex gs → ℝ) (S : ChainIndex gs) :
    extendChainFun gs H S.val = H S := by simp [extendChainFun,S.property]

end ProjectionBridge

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

end
open scoped Classical BigOperators
variable {X : Type*} [Fintype X] (C : FiniteChain X)

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

end TracePoincare

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FactorialSignatures
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorial congruence for the two binary lifts

The integer-to-binary signature transfer in paper 200-02,
Lemma `lem:binary-signatures`. Coordinates with zero remaining copies
are allowed; a single remaining copy gives an invalid repeated removal.
The copy matrix is proved to be dominated by the integer form compressed
to group means. The difference is the nonnegative within-group variance.
-/

namespace ContingencyTables.FactorialSignatures

open scoped BigOperators Classical Matrix
open LinearMap (BilinForm)
open CommonBasesFPRAS

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- The actual addition matrix of the complementary factorial lift uses
remaining-capacity factorials, and hence exactly the same congruence. -/
theorem additionLift_onePositive (h : (G → ℕ) → ℝ) (r n : G → ℕ) (D : ℝ)
    (hD : 0 < D) (hh : ∀ a, 0 ≤ h a)
    (hsig : OnePositiveDirection (integerAdditionMatrix h r n).toBilin') :
    OnePositiveDirection (additionLiftMatrix h r n D).toBilin' := by
  have heq : additionLiftMatrix h r n D = factorialMatrix n (integerAdditionMatrix h r n) D := by
    ext i j
    by_cases hij : i = j
    · simp [additionLiftMatrix, factorialMatrix, hij]
    have hv := distinct_copy_counts n i j hij
    simp [additionLiftMatrix, factorialMatrix, hij, integerAdditionMatrix, ValidPair, hv]
  rw [heq]
  apply factorialMatrix_onePositive n _ D hD
  · intro u v
    have heq : addTwo r u v = addTwo r v u := by funext w; dsimp [addTwo]; omega
    simp only [integerAdditionMatrix, validPair_symm n u v, heq]
  · exact hsig
  · intro u
    unfold integerAdditionMatrix
    split_ifs <;> simp [hh]
  · intro u hu
    have hn : ¬ValidPair n u u := by simp [ValidPair]; omega
    simp [integerAdditionMatrix, hn]


omit [Fintype G] [DecidableEq G] in
lemma cellFactor_positive (b x y : ℕ) : 0 < cellFactor b x y := by
  exact div_pos (mul_pos (by exact_mod_cast Nat.factorial_pos x)
    (by exact_mod_cast Nat.factorial_pos y)) (by exact_mod_cast Nat.factorial_pos b)

omit [Fintype G] [DecidableEq G] in
/-- On transversals, the two cell multipliers agree exactly. -/
lemma balanced_cell_factors (b x y : ℕ) (h : x + y = b) :
    complementCellFactor b x y = cellFactor b x y := by
  have hx : b - x = y := by omega
  have hy : b - y = x := by omega
  simp only [complementCellFactor, cellFactor, hx, hy]
  ring

omit [Fintype G] [DecidableEq G] in
/-- The empty-pair cell contributes `(x+1)(y+1)` to the lift ratio. -/
lemma empty_cell_factors (b x y : ℕ) (h : x + y + 1 = b) :
    complementCellFactor b x y = ((x : ℝ) + 1) * ((y : ℝ) + 1) * cellFactor b x y := by
  have hx : b - x = y + 1 := by omega
  have hy : b - y = x + 1 := by omega
  simp only [complementCellFactor, cellFactor, hx, hy, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  ring

omit [Fintype G] [DecidableEq G] in
/-- The full-pair cell contributes the reciprocal product `1/(xy)`. -/
lemma full_cell_factors (b x y : ℕ) (hx : x ≤ b) (hy : y ≤ b) (h : x + y = b + 1) :
    complementCellFactor b x y * ((x : ℝ) * y) = cellFactor b x y := by
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  have hbx : b - x = y - 1 := by omega
  have hby : b - y = x - 1 := by omega
  have hxf : (x : ℝ) * ((x - 1).factorial : ℝ) = x.factorial := by
    exact_mod_cast Nat.mul_factorial_pred hx0
  have hyf : (y : ℝ) * ((y - 1).factorial : ℝ) = y.factorial := by
    exact_mod_cast Nat.mul_factorial_pred hy0
  simp only [complementCellFactor, cellFactor, hbx, hby]
  calc
    _ = ((x : ℝ) * ((x - 1).factorial : ℝ)) *
        ((y : ℝ) * ((y - 1).factorial : ℝ)) / b.factorial := by ring
    _ = _ := by rw [hxf, hyf]

omit [Fintype G] [DecidableEq G] in
lemma quotient_square_bounds (W A B : ℝ) (hW : 0 < W)
    (hA0 : 1 ≤ A) (hB0 : 1 ≤ B) (hA : A ≤ W ^ 2) (hB : B ≤ W ^ 2) :
    1 / W ^ 2 ≤ A / B ∧ A / B ≤ W ^ 2 := by
  have hWp : 0 < W ^ 2 := sq_pos_of_pos hW
  have hBp : 0 < B := by linarith
  constructor
  · apply (div_le_div_iff₀ hWp hBp).mpr
    nlinarith
  · apply (div_le_iff₀ hBp).mpr
    nlinarith

/-- The product ratio when one cell contains the hole, one contains the
full pair, and all remaining cells are balanced. -/
lemma defect_product_identity (F T : G → ℝ) (a b : G) (hab : a ≠ b) (A B : ℝ)
    (ha : T a = A * F a) (hb : T b = F b / B)
    (hrest : ∀ u, u ≠ a → u ≠ b → T u = F u) :
    (∏ u, T u) = (A / B) * ∏ u, F u := by
  have heq : T = fun u =>
      (if u = a then A else 1) * (if u = b then 1 / B else 1) * F u := by
    funext u
    by_cases hua : u = a
    · subst u
      simp [hab, ha]
    by_cases hub : u = b
    · subst u
      simp [Ne.symm hab, hb, div_eq_mul_inv, mul_comm]
    · simp [hua, hub, hrest u hua hub]
  rw [heq]
  simp only [Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq', div_eq_mul_inv, mul_assoc]

/-- The exact `q = W²` comparison between the two factorial lifts on a
single-hole/single-full defect, after their common positive base weight. -/
theorem defect_lift_comparison (b x y : G → ℕ) (a d : G) (had : a ≠ d)
    (W : ℕ) (hW : 0 < W) (hbW : ∀ u, b u < W)
    (hx : ∀ u, x u ≤ b u) (hy : ∀ u, y u ≤ b u)
    (ha : x a + y a + 1 = b a) (hd : x d + y d = b d + 1)
    (hrest : ∀ u, u ≠ a → u ≠ d → x u + y u = b u)
    (h : ℝ) (hh : 0 ≤ h) :
    (1 / (W : ℝ) ^ 2) * (h * ∏ u, cellFactor (b u) (x u) (y u)) ≤
      h * ∏ u, complementCellFactor (b u) (x u) (y u) ∧
    (h * ∏ u, complementCellFactor (b u) (x u) (y u)) ≤
      (W : ℝ) ^ 2 * (h * ∏ u, cellFactor (b u) (x u) (y u)) := by
  let A : ℝ := ((x a : ℝ) + 1) * ((y a : ℝ) + 1)
  let B : ℝ := (x d : ℝ) * y d
  have hxd : 1 ≤ x d := by have := hy d; omega
  have hyd : 1 ≤ y d := by have := hx d; omega
  have hBpos : 0 < B := by
    dsimp [B]
    exact mul_pos (by exact_mod_cast hxd) (by exact_mod_cast hyd)
  have hprod : (∏ u, complementCellFactor (b u) (x u) (y u)) =
      (A / B) * ∏ u, cellFactor (b u) (x u) (y u) := by
    apply defect_product_identity _ _ a d had A B
    · exact empty_cell_factors _ _ _ ha
    · exact (eq_div_iff (ne_of_gt hBpos)).mpr (full_cell_factors _ _ _ (hx d) (hy d) hd)
    · intro u hua hud
      exact balanced_cell_factors _ _ _ (hrest u hua hud)
  have hbounds : 1 / (W : ℝ) ^ 2 ≤ A / B ∧ A / B ≤ (W : ℝ) ^ 2 := by
    apply quotient_square_bounds _ A B (by exact_mod_cast hW)
    · dsimp [A]
      have hxa : (0 : ℝ) ≤ x a := Nat.cast_nonneg _
      have hya : (0 : ℝ) ≤ y a := Nat.cast_nonneg _
      nlinarith
    · dsimp [B]
      have hxd' : (1 : ℝ) ≤ x d := by exact_mod_cast hxd
      have hyd' : (1 : ℝ) ≤ y d := by exact_mod_cast hyd
      nlinarith
    · dsimp [A]
      have hxa : (x a : ℝ) + 1 ≤ W := by exact_mod_cast (by have := hx a; have := hbW a; omega : x a + 1 ≤ W)
      have hya : (y a : ℝ) + 1 ≤ W := by exact_mod_cast (by have := hy a; have := hbW a; omega : y a + 1 ≤ W)
      have hxa0 : 0 ≤ (x a : ℝ) + 1 := by positivity
      have hya0 : 0 ≤ (y a : ℝ) + 1 := by positivity
      nlinarith
    · dsimp [B]
      have hxdW : (x d : ℝ) ≤ W := by exact_mod_cast (by have := hx d; have := hbW d; omega : x d ≤ W)
      have hydW : (y d : ℝ) ≤ W := by exact_mod_cast (by have := hy d; have := hbW d; omega : y d ≤ W)
      have hxd0 : (0 : ℝ) ≤ x d := Nat.cast_nonneg _
      have hyd0 : (0 : ℝ) ≤ y d := Nat.cast_nonneg _
      nlinarith
  have hF : 0 ≤ h * ∏ u, cellFactor (b u) (x u) (y u) :=
    mul_nonneg hh (Finset.prod_nonneg (fun u _ => (cellFactor_positive _ _ _).le))
  rw [hprod]
  constructor
  · convert mul_le_mul_of_nonneg_right hbounds.1 hF using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · convert mul_le_mul_of_nonneg_right hbounds.2 hF using 1
    all_goals try with_reducible_and_instances rfl
    ring


omit [DecidableEq G] in
/-- Agreement of the actual full factorial multipliers on every balanced profile. -/
theorem balanced_lift_agreement (b x y : G → ℕ)
    (hbalanced : ∀ u, x u + y u = b u) (h : ℝ) :
    h * (∏ u, complementCellFactor (b u) (x u) (y u)) =
      h * ∏ u, cellFactor (b u) (x u) (y u) := by
  congr 1
  apply Finset.prod_congr rfl
  intro u _
  exact balanced_cell_factors _ _ _ (hbalanced u)

end ContingencyTables.FactorialSignatures

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerReflection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual box reflection and integer addition signatures

Reflection of every coordinate converts a valid two-addition entry into a
two-removal entry. A balanced summed pair is reflected by reversing its
finite index, so the same marginal closure applies to additions.
-/

namespace ContingencyTables.IntegerReflection

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
lemma reflect_removeTwo (N r n : I → ℕ) (hr : ∀ i, r i+n i=N i)
    (i j : I) (hv : ValidPair n i j) :
    reflect N (removeTwo n i j) = addTwo r i j := by
  funext k
  have hk := hr k
  have hi := hv.1
  have hj := hv.2
  by_cases hij : i=j
  · subst j
    have hn : 2 ≤ n i := by simp at hj; omega
    by_cases hki : k=i
    · subst k
      simp only [reflect,removeTwo,removeOne,addTwo,ite_true, if_true]
      omega
    · simp [reflect,removeTwo,removeOne,addTwo,hki]
      omega
  · have hj0 : 0 < n j := by simpa [Ne.symm hij] using hj
    by_cases hki : k=i
    · subst k
      simp only [reflect,removeTwo,removeOne,addTwo,ite_true, if_true,hij,ite_false]
      omega
    · by_cases hkj : k=j
      · subst k
        simp only [reflect,removeTwo,removeOne,addTwo,ite_true, if_true,Ne.symm hij,ite_false]
        omega
      · simp only [reflect,removeTwo,removeOne,addTwo,hki,hkj,ite_false,Nat.sub_zero,add_zero]
        omega

omit [Fintype I] in
/-- Exact matrix identity, including all invalid pair entries. -/
theorem addition_eq_reflected_removal (h : (I → ℕ) → ℝ) (N r n : I → ℕ)
    (hr : ∀ i, r i+n i=N i) :
    integerAdditionMatrix h r n = integerRemovalMatrix (fun z => h (reflect N z)) n := by
  ext i j
  unfold integerAdditionMatrix integerRemovalMatrix
  split_ifs with hv
  · dsimp only
    rw [reflect_removeTwo N r n hr i j hv]
  · rfl

/-- The addition signature follows from the raw removal signature of
its globally reflected weight, without a binary-lift assumption. -/
theorem addition_onePositive_of_reflection (h : (I → ℕ) → ℝ) (N r n : I → ℕ)
    (hr : ∀ i, r i+n i=N i)
    (hsig : OnePositiveDirection (integerRemovalMatrix (fun z => h (reflect N z)) n).toBilin') :
    OnePositiveDirection (integerAdditionMatrix h r n).toBilin' := by
  rw [addition_eq_reflected_removal h N r n hr]
  exact hsig

omit [Fintype I] [DecidableEq I] in
lemma reflect_profile (N z : I → ℕ) (M j : ℕ) (hj : j ≤ M) :
    reflect (profile N M M) (profile z j (M-j)) = profile (reflect N z) (M-j) j := by
  funext t
  rcases t with i | (_ | _) <;> simp [reflect,profile]
  omega

omit [Fintype I] [DecidableEq I] in
/-- Reflection commutes with actual balanced marginalization by reversal
of the finite summation index. -/
theorem marginal_reflect (F : ((I ⊕ Bool) → ℕ) → ℝ) (N z : I → ℕ) (M : ℕ) :
    marginal (fun x => F (reflect (profile N M M) x)) M z =
      marginal F M (reflect N z) := by
  unfold marginal
  calc
    _ = ∑ j ∈ Finset.range (M+1), F (profile (reflect N z) (M-j) j) := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only
      rw [reflect_profile N z M j (by simpa using Finset.mem_range.mp hj)]
    _ = _ := by
      have hh := Finset.sum_range_reflect
        (fun j => F (profile (reflect N z) j (M-j))) (M+1)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro j hj
      have hjM : j ≤ M := by simpa using Finset.mem_range.mp hj
      congr 1
      congr 1; omega

end ContingencyTables.IntegerReflection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedFamily
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All finite balanced-pair eliminations

The coordinates are the retained small coordinates followed by the actual
finite list of large-cell pairs. The recursion performs their finite
balanced sums and proves the total-slice positivity and removal signature
at every step.
-/

namespace ContingencyTables.BalancedFamily

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal BalancedBox

universe u

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- Reflection reverses the finite index in every summed large pair and
also reflects every retained coordinate. -/
theorem eliminate_reflect (Ms : List ℕ) (m : I → ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    eliminate Ms (fun x => F (IntegerReflection.reflect (bounds m Ms) x)) z =
      eliminate Ms F (IntegerReflection.reflect m z) := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
    have he : marginal (fun x => F (IntegerReflection.reflect (bounds m (M::Ms)) x)) M =
        fun x => marginal F M (IntegerReflection.reflect (bounds m Ms) x) := by
      funext x
      exact IntegerReflection.marginal_reflect F (bounds m Ms) x M
    change eliminate Ms (marginal (fun x => F (IntegerReflection.reflect (bounds m (M::Ms)) x)) M) z = _
    rw [he]
    exact ih (marginal F M)

end ContingencyTables.BalancedFamily

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RecursiveSignedTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recursive signed transport for fixed-degree weights

The recursive transport construction of the bounded-table counting paper
uses positivity at the valid subset degree. Signatures after pair summation
follow from that degree's addition property and full cubic contraction.
-/

namespace ContingencyTables.RecursiveSignedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS BinaryContraction

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma slotTotal_degree_positive (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (A : Set Γ)
    (hdegree : A.ncard + ps.length = k) (hslots : SlotsFresh ps A) :
    0 < slotTotal ps f A := by
  induction ps generalizing A with
  | nil => exact hf A (by simpa using hdegree)
  | cons p ps ih =>
    obtain ⟨hp, ha, hb, ht⟩ := hslots
    rw [slotTotal_cons p ps f A hp ha hb]
    apply add_pos
    · apply ih (insert p.1 A)
      · rw [ncard_insert_eq A p.1 ha]
        simp only [List.length_cons] at hdegree
        omega
      · exact ht.mono (by intro x hx; rcases hx with rfl | hx <;> simp_all)
    · apply ih (insert p.2 A)
      · rw [ncard_insert_eq A p.2 hb]
        simp only [List.length_cons] at hdegree
        omega
      · exact ht.mono (Set.subset_insert _ _)

end ContingencyTables.RecursiveSignedTransport

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LabelledFactorial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal subset factorial lifts and their conditioned copy displays

A display is the actual subtype of available labelled elements. Its group
fibres are reindexed by Fin of their exact cardinalities. Removing or adding
actual labels changes the group counts by the exact integer updates, so the
conditioned subset matrices are congruent to the proved factorial copy
matrices. No binary-lift signature is assumed.
-/

namespace ContingencyTables.LabelledFactorial

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS BinaryContraction FactorialSignatures

variable {I G : Type*} [Fintype I] [Fintype G]

omit [Fintype G] in
lemma groupCount_insert (group : I → G) (S : Set I) (i : I) (hi : i ∉ S) :
    groupCount group (insert i S) = fun u => groupCount group S u + if u = group i then 1 else 0 := by
  funext u
  have heq : Finset.univ.filter (fun j => j ∈ insert i S ∧ group j = u) =
      if group i = u then insert i (Finset.univ.filter (fun j => j ∈ S ∧ group j = u))
      else Finset.univ.filter (fun j => j ∈ S ∧ group j = u) := by
    ext j
    by_cases h : group i = u
    · simp only [h, ite_true, if_true, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_insert_iff, Finset.mem_insert]
      constructor
      · rintro ⟨hji | hjS, hjg⟩
        · exact Or.inl hji
        · exact Or.inr ⟨hjS,hjg⟩
      · rintro (rfl | ⟨hjS,hjg⟩)
        · exact ⟨Or.inl rfl,h⟩
        · exact ⟨Or.inr hjS,hjg⟩
    · simp only [h, ite_false, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_insert_iff]
      constructor
      · rintro ⟨rfl | hjS,hjg⟩
        · exact (h hjg).elim
        · exact ⟨hjS,hjg⟩
      · rintro ⟨hjS,hjg⟩; exact ⟨Or.inr hjS,hjg⟩
  unfold groupCount
  have hc := congrArg Finset.card heq
  convert hc.trans ?_ using 1
  · congr 1; ext j; simp
  · by_cases h : group i = u
    · simp only [h, ite_true, if_true]
      apply Finset.card_insert_of_notMem
      simp [hi]
    · simp [h, Ne.symm h]

omit [Fintype G] in
lemma groupCount_addTwo (group : I → G) (S : Set I) (i j : I)
    (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    groupCount group (S ∪ {i,j}) = addTwo (groupCount group S) (group i) (group j) := by
  have heq : S ∪ {i,j} = insert j (insert i S) := by ext x; simp; tauto
  rw [heq, groupCount_insert group _ j (by simp [hj,hij.symm]), groupCount_insert group S i hi]
  funext u
  rfl

/-- The literal second-lift addition matrix has the exact remaining-capacity
factorials of the canonical copy matrix. -/
theorem secondLift_addition_matrix (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (A : Set I) :
    faceHessian (secondLift group h D) A =
      (additionLiftMatrix h (groupCount group A) (groupCount group Aᶜ) D).submatrix
        (displayCopyEquiv group Aᶜ) (displayCopyEquiv group Aᶜ) := by
  ext i j
  by_cases hij : i = j
  · simp [faceHessian, additionLiftMatrix, Matrix.submatrix_apply, hij]
  have he : displayCopyEquiv group Aᶜ i ≠ displayCopyEquiv group Aᶜ j :=
    fun h => hij ((displayCopyEquiv group Aᶜ).injective h)
  have hs : (A ∪ {i.val,j.val})ᶜ = Aᶜ \ {i.val,j.val} := by ext x; simp; tauto
  have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  simp only [faceHessian, hij, ite_false, Matrix.submatrix_apply, additionLiftMatrix, he,
    secondLift, displayCopyEquiv_group]
  rw [hs, groupCount_removeTwo group Aᶜ i.val j.val i.property j.property hval,
    groupCount_addTwo group A i.val j.val i.property j.property hval]

/-- Integer addition signatures imply the addition property of the literal
complementary-factorial lift. -/
theorem secondLift_addition (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (k : ℕ)
    (hD : 0 < D) (hh : ∀ n, 0 ≤ h n)
    (hsig : ∀ A : Set I, A.ncard + 2 = k →
      OnePositiveDirection (integerAdditionMatrix h (groupCount group A) (groupCount group Aᶜ)).toBilin') :
    AdditionProperty (secondLift group h D) k := by
  intro A hA
  rw [secondLift_addition_matrix]
  apply onePositive_reindex (displayCopyEquiv group Aᶜ)
  have hs := additionLift_onePositive h (groupCount group A) (groupCount group Aᶜ) D hD hh (hsig A hA)
  have hsymm : ∀ i j, additionLiftMatrix h (groupCount group A) (groupCount group Aᶜ) D i j =
      additionLiftMatrix h (groupCount group A) (groupCount group Aᶜ) D j i := by
    intro i j
    have ha : addTwo (groupCount group A) i.1 j.1 = addTwo (groupCount group A) j.1 i.1 := by
      funext u
      unfold addTwo
      omega
    simp only [additionLiftMatrix, eq_comm, removeTwo_comm, ha]
  have hm := (signature_iff _ (matrix_bilin_symm _ hsymm)).mp hs
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  congr 2; exact Subsingleton.elim _ _

end ContingencyTables.LabelledFactorial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReflectedSlices
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reflected actual penalties and the complementary factorial lift

Reflecting a physical box changes affine offsets and reverses their
slopes. The root/equality and unary interval factors therefore have the
same proved scalar signatures. All finite balanced pairs are reflected
as well, before transferring the resulting addition signature to labels.
-/

namespace ContingencyTables.ReflectedSlices

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures ProductIntegerSignature
open IntegerReflection EqualitySoftening BalancedBox BalancedFamily LabelledFactorial

variable {C G : Type*} [Fintype C] [Fintype G]

omit [Fintype G] in
lemma lineTotal_reflect_add (line : C → G) (m z : C → ℕ) (hz : InBox m z) (g : G) :
    lineTotal line (reflect m z) g+lineTotal line z g=lineTotal line m g := by
  unfold lineTotal reflect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : line i=g
  · simp only [hi,ite_true, if_true]
    exact Nat.sub_add_cancel (hz i)
  · simp only [hi,ite_false,add_zero]

lemma affine_reflect (a slope : ℝ) (M r n : ℕ) (h : r+n=M) :
    a+(r:ℝ)*slope=(a+(M:ℝ)*slope)+(n:ℝ)*(-slope) := by
  have hh : (r:ℝ)+(n:ℝ)=M := by exact_mod_cast h
  rw [← hh]
  ring

theorem softenedWeight_reflect (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ)
    (m z : C → ℕ) (hz : InBox m z) :
    softenedWeight line root rate offset slope urate ell uslope cap L (reflect m z) =
      softenedWeight line root rate
        (fun g => offset g+(lineTotal line m g:ℝ)*slope g) (fun g => -slope g)
        urate (fun i => ell i+(m i:ℝ)*uslope i) (fun i => -uslope i) cap L z := by
  unfold softenedWeight productWeight
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    unfold lineFactor ScalarPenalty.factor
    dsimp only
    rw [affine_reflect (offset g) (slope g) _ _ _ (lineTotal_reflect_add line m z hz g)]
  · apply Finset.prod_congr rfl
    intro i _
    unfold unaryFactor ScalarPenalty.factor affineDistance reflect
    dsimp only
    rw [affine_reflect (ell i) (uslope i) (m i) (m i-z i) (z i) (Nat.sub_add_cancel (hz i))]

omit [Fintype G] [Fintype C] in
lemma removal_congr_box (f h : (C → ℕ) → ℝ) (m z : C → ℕ) (hz : InBox m z)
    (heq : ∀ x, InBox m x → f x=h x) : integerRemovalMatrix f z=integerRemovalMatrix h z := by
  ext i j
  unfold integerRemovalMatrix
  split_ifs with hv
  · exact heq _ (IntegerBoxTruncation.removal_inBox m z hz i j)
  · rfl

/-- The original globally reflected positive weight has its raw removal
signature throughout the physical box, from explicit reflected factors. -/
theorem reflected_softened_removal (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ)
    (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ i, 0 ≤ urate i) (hL : 0 ≤ L)
    (m z : C → ℕ) (hz : InBox m z) :
    OnePositiveDirection (integerRemovalMatrix
      (fun x => softenedWeight line root rate offset slope urate ell uslope cap L (reflect m x)) z).toBilin' := by
  rw [removal_congr_box _ _ m z hz (fun x hx => softenedWeight_reflect line root rate offset slope
    urate ell uslope cap L m x hx)]
  exact softenedWeight_removal line root rate
    (fun g => offset g+(lineTotal line m g:ℝ)*slope g) (fun g => -slope g)
    urate (fun i => ell i+(m i:ℝ)*uslope i) (fun i => -uslope i) cap L hrate hu hL z

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The companion's actual positive finite marginal has the reflected
removal signature needed for its two-addition matrix. -/
theorem reflected_softened_marginal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (root : G → Bool) (rate offset slope : G → ℝ)
    (urate ell uslope cap : Coordinates I Ms → ℝ) (L : ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) (hrate : ∀ g, 0 ≤ rate g)
    (hu : ∀ i, 0 ≤ urate i) (hL : 0 ≤ L) :
    RemovalSlice
      (fun z => eliminate Ms (softenedWeight line root rate offset slope urate ell uslope cap L)
        (reflect m z)) m R := by
  let F := softenedWeight line root rate offset slope urate ell uslope cap L
  have hp : PositiveSlice (fun x => F (reflect (bounds m Ms) x)) (bounds m Ms) (R+Ms.sum) := by
    intro x _ _
    exact softenedWeight_positive line root rate offset slope urate ell uslope cap L _
  have hs : RemovalSlice (fun x => F (reflect (bounds m Ms) x)) (bounds m Ms) (R+Ms.sum) := by
    intro x hx _
    convert reflected_softened_removal line root rate offset slope urate ell uslope cap L
      hrate hu hL (bounds m Ms) x hx using 1
    all_goals try with_reducible_and_instances rfl
    congr 2 <;> exact Subsingleton.elim _ _
  have h := (eliminate_slices Ms m R _ hwidth hp hs).2
  have he : eliminate Ms (fun x => F (reflect (bounds m Ms) x)) =
      fun z => eliminate Ms F (reflect m z) := by
    funext z
    exact eliminate_reflect Ms m F z
  rwa [he] at h

/-- The reflected addition input survives the nonroot-equality limit
after all balanced large-cell sums, exactly as the removal input does. -/
theorem reflected_exact_marginal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (root : G → Bool) (rate offset slope : G → ℝ)
    (urate ell uslope cap : Coordinates I Ms → ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ i, 0 ≤ urate i) :
    RemovalSlice
      (fun z => eliminate Ms (exactWeight line root rate offset slope urate ell uslope cap)
        (reflect m z)) m R := by
  intro z hz ht
  apply IntegerMarginal.removal_signature_limit (l := (Filter.atTop : Filter ℝ))
    (fun L x => eliminate Ms (softenedWeight line root rate offset slope urate ell uslope cap L)
      (reflect m x))
    (fun x => eliminate Ms (exactWeight line root rate offset slope urate ell uslope cap)
      (reflect m x)) z
  · intro x
    exact eliminate_tendsto Ms _ _
      (softenedWeight_tendsto line root rate offset slope urate ell uslope cap) (reflect m x)
  · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with L hL
    exact reflected_softened_marginal Ms m R line root rate offset slope urate ell uslope cap L
      hwidth hrate hu hL z hz ht

variable {A : Type*} [Fintype A]

omit [Fintype I] [DecidableEq I] [Fintype G] [Fintype C] in
lemma groupCount_complement (group : A → C) (S : Set A) (c : C) :
    groupCount group S c+groupCount group Sᶜ c=groupCount group Set.univ c := by
  unfold groupCount
  simp_rw [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : group a=c <;> by_cases hs : a∈S <;> simp [hg,hs]

omit [Fintype I] [DecidableEq I] [Fintype G] in
/-- The actual reflected raw slice proves the addition property of the
literal complementary-factorial lift in the original coordinates. -/
theorem secondLift_addition_reflected_slice (group : A → C) (h : (C → ℕ) → ℝ)
    (D : ℝ) (R : ℕ) (hR : R ≤ Fintype.card A) (hD : 0 < D) (hh : ∀ z, 0 ≤ h z)
    (hsig : RemovalSlice (fun z => h (reflect (groupCount group Set.univ) z))
      (groupCount group Set.univ) (Fintype.card A-R)) :
    BinaryContraction.AdditionProperty (secondLift group h D) R := by
  apply secondLift_addition group h D R hD hh
  intro S hS
  apply addition_onePositive_of_reflection h (groupCount group Set.univ)
    (groupCount group S) (groupCount group Sᶜ) (groupCount_complement group S)
  apply hsig _ (SliceFactorial.groupCount_inBox group Sᶜ)
  rw [groupCount_total]
  have hc := Set.ncard_add_ncard_compl S
  simp only [Nat.card_eq_fintype_card] at hc
  omega

end ContingencyTables.ReflectedSlices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EqualityReindex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Equality factors under the actual physical coordinate bijection

A bijection of coordinates preserves the line totals and unary products.
Consequently the balanced marginal signature applies to the literal
physical factor family after all cell-index bookkeeping has been proved.
-/

namespace ContingencyTables.EqualityReindex

open scoped BigOperators Classical
open ProductIntegerSignature EqualitySoftening BalancedFamily BalancedBox

variable {C D G : Type*} [Fintype C] [Fintype D] [Fintype G]

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Global physical reflection also preserves the proved marginal
signature, and all balanced pairs are reflected along with small views. -/
theorem physical_marginal_reflected (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : D → ℝ)
    (hwidth : ∀ M ∈ Ms, 2≤M) (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ d, 0≤urate d) :
    RemovalSlice (fun z => eliminate Ms (fun q =>
      exactWeight line root rate offset slope urate ell uslope cap (q ∘ e.symm))
      (IntegerReflection.reflect m z)) m R := by
  have heq : (fun z => exactWeight line root rate offset slope urate ell uslope cap
      (z ∘ e.symm))=
      exactWeight (line ∘ e) root rate offset slope (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) := by
    funext z
    exact (exactWeight_reindex e line root rate offset slope urate ell uslope cap z).symm
  rw [heq]
  exact ReflectedSlices.reflected_exact_marginal Ms m R (line ∘ e) root rate offset slope
    (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) hwidth hrate (fun i => hu (e i))

end ContingencyTables.EqualityReindex

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TwoLiftStates
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual paired states and the two factorial weights

Every physical cell contains an arbitrary finite bundle of paired labels.
The plain and one-hole/one-full predicates imply the exact cell count
identities. Thus the literal subset lifts agree on plain states and obey
the manuscript's W² comparison on every actual chain state.
-/

namespace ContingencyTables.TwoLiftStates

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures LabelledFactorial

variable {P C : Type*} [Fintype P] [Fintype C]

omit [Fintype C] in
lemma viewCount_compl (cell : P → C) (S : Set (P × Bool)) (c : C) (t : Bool) :
    viewCount cell S c t + viewCount cell Sᶜ c t = width cell c := by
  rw [width_eq_sum]
  unfold viewCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : cell p=c <;> by_cases hs : (p,t) ∈ S <;> simp [hc,hs]

omit [Fintype C] in
lemma viewCount_le_width (cell : P → C) (S : Set (P × Bool)) (c : C) (t : Bool) :
    viewCount cell S c t ≤ width cell c := by
  have := viewCount_compl cell S c t
  omega

omit [Fintype C] in
lemma viewCounts_eq_occupancy (cell : P → C) (S : Set (P × Bool)) (c : C) :
    viewCount cell S c false + viewCount cell S c true =
      ∑ p, if cell p=c then occupancy S p else 0 := by
  unfold viewCount occupancy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : cell p=c <;> simp [hc]

omit [Fintype P] in
lemma occupancy_single (S : Set (P × Bool)) (p : P) (h : PairSingle (pair p) S) :
    occupancy S p = 1 := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [occupancy,pair] at ha hb ⊢ <;> simp [ha,hb]

omit [Fintype P] in
lemma occupancy_empty (S : Set (P × Bool)) (p : P) (h : PairEmpty (pair p) S) :
    occupancy S p = 0 := by
  rcases h with ⟨ha,hb⟩
  simp [pair] at ha hb
  simp [occupancy,ha,hb]

omit [Fintype P] in
lemma occupancy_full (S : Set (P × Bool)) (p : P) (h : PairFull (pair p) S) :
    occupancy S p = 2 := by
  rcases h with ⟨ha,hb⟩
  simp [pair] at ha hb
  simp [occupancy,ha,hb]

omit [Fintype C] in
/-- Every actual plain state is balanced in every physical cell. -/
theorem plain_counts (cell : P → C) (S : Set (P × Bool))
    (hS : PlainState pairs S) (c : C) :
    viewCount cell S c false + viewCount cell S c true = width cell c := by
  rw [viewCounts_eq_occupancy,width_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [occupancy_single S p (hS _ (pair_mem p))]

lemma defect_occupancy (S : Set (P × Bool)) (p q : P)
    (hS : DefectState pairs (pair p) (pair q) S) (k : P) :
    occupancy S k + (if k=p then 1 else 0) = 1 + (if k=q then 1 else 0) := by
  have hpq : p ≠ q := fun h => hS.2.2.1 (congrArg pair h)
  by_cases hkp : k=p
  · subst k
    rw [occupancy_empty S p hS.2.2.2.1]
    simp [hpq]
  · by_cases hkq : k=q
    · subst k
      rw [occupancy_full S q hS.2.2.2.2.1]
      simp [hkp]
    · rw [occupancy_single S k (hS.2.2.2.2.2 _ (pair_mem k)
        (fun h => hkp (pair_injective h)) (fun h => hkq (pair_injective h)))]
      simp [hkp,hkq]

omit [Fintype C] in
/-- Cell occupancies of an actual defect have exactly one unit missing at
its hole and one unit extra at its full pair, including coinciding cells. -/
theorem defect_counts (cell : P → C) (S : Set (P × Bool)) (p q : P)
    (hS : DefectState pairs (pair p) (pair q) S) (c : C) :
    viewCount cell S c false + viewCount cell S c true + (if cell p=c then 1 else 0) =
      width cell c + (if cell q=c then 1 else 0) := by
  have hs : (∑ k, if cell k=c then occupancy S k + (if k=p then 1 else 0) else 0) =
      ∑ k, if cell k=c then 1 + (if k=q then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [defect_occupancy S p q hS k]
  have hd (u v : P → ℕ) : (∑ k, if cell k=c then u k+v k else 0) =
      (∑ k, if cell k=c then u k else 0)+(∑ k, if cell k=c then v k else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> rfl
  rw [hd,hd] at hs
  have he (a : P) : (∑ k, if cell k=c then (if k=a then (1:ℕ) else 0) else 0) =
      if cell a=c then 1 else 0 := by
    calc
      _ = ∑ k, if k=a then (if cell k=c then 1 else 0) else 0 := by
        apply Finset.sum_congr rfl; intro k _; split_ifs <;> rfl
      _ = _ := by simp
  rw [he p,he q,← width_eq_sum,← viewCounts_eq_occupancy] at hs
  exact hs

lemma firstLift_eq_cells (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ) (S : Set (P × Bool)) :
    firstLift (group cell) h (denominator cell) S =
      h (groupCount (group cell) S) *
        ∏ c, cellFactor (width cell c) (viewCount cell S c false) (viewCount cell S c true) := by
  unfold firstLift factorialProduct denominator cellFactor
  simp only [Fintype.prod_prod_type,Fintype.prod_bool,groupCount_eq_viewCount]
  simp only [Finset.prod_div_distrib,Finset.prod_mul_distrib]
  ring

lemma secondLift_eq_cells (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ) (S : Set (P × Bool)) :
    secondLift (group cell) h (denominator cell) S =
      h (groupCount (group cell) S) *
        ∏ c, complementCellFactor (width cell c) (viewCount cell S c false) (viewCount cell S c true) := by
  have he (c : C) (t : Bool) : groupCount (group cell) Sᶜ (c,t) =
      width cell c - viewCount cell S c t := by
    rw [groupCount_eq_viewCount]
    have := viewCount_compl cell S c t
    omega
  unfold secondLift factorialProduct denominator complementCellFactor
  simp only [Fintype.prod_prod_type,Fintype.prod_bool,he]
  simp only [Finset.prod_div_distrib,Finset.prod_mul_distrib]
  ring

/-- Exact agreement of the two literal subset lifts on every plain state. -/
theorem plain_lifts_agree (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hS : PlainState pairs S) :
    secondLift (group cell) h (denominator cell) S = firstLift (group cell) h (denominator cell) S := by
  rw [firstLift_eq_cells,secondLift_eq_cells]
  exact balanced_lift_agreement _ _ _ (plain_counts cell S hS) _

/-- The paper's exact W² comparison on every actual defect state. -/
theorem defect_lifts_compare (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hS : ∃ p q, DefectState pairs (pair p) (pair q) S)
    (W : ℕ) (hW : 0 < W) (hbW : ∀ c, width cell c < W)
    (hh : 0 ≤ h (groupCount (group cell) S)) :
    (1/(W:ℝ)^2) * firstLift (group cell) h (denominator cell) S ≤
        secondLift (group cell) h (denominator cell) S ∧
    secondLift (group cell) h (denominator cell) S ≤
        (W:ℝ)^2 * firstLift (group cell) h (denominator cell) S := by
  obtain ⟨p,q,hS⟩ := hS
  rw [firstLift_eq_cells,secondLift_eq_cells]
  by_cases hpq : cell p=cell q
  · have hbal (c : C) : viewCount cell S c false + viewCount cell S c true = width cell c := by
      have ht := defect_counts cell S p q hS c
      rw [hpq] at ht
      omega
    rw [balanced_lift_agreement _ _ _ hbal]
    have hf : 0 ≤ h (groupCount (group cell) S) *
        ∏ c, cellFactor (width cell c) (viewCount cell S c false) (viewCount cell S c true) :=
      mul_nonneg hh (Finset.prod_nonneg fun _ _ => (cellFactor_positive _ _ _).le)
    have hWr : (1:ℝ) ≤ W := by exact_mod_cast hW
    have hsq : (1:ℝ) ≤ (W:ℝ)^2 := by nlinarith
    constructor
    · exact mul_le_of_le_one_left hf ((div_le_one (by positivity)).mpr hsq)
    · exact le_mul_of_one_le_left hf hsq
  · apply defect_lift_comparison _ _ _ (cell p) (cell q) hpq W hW hbW
      (fun c => viewCount_le_width cell S c false) (fun c => viewCount_le_width cell S c true)
    · have ht := defect_counts cell S p q hS (cell p)
      simpa [hpq,Ne.symm hpq] using ht
    · have ht := defect_counts cell S p q hS (cell q)
      simpa [hpq] using ht
    · intro c hcp hcq
      have ht := defect_counts cell S p q hS c
      simpa [Ne.symm hcp,Ne.symm hcq] using ht
    · exact hh

lemma firstLift_nonnegative (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hh : 0 ≤ h (groupCount (group cell) S)) :
    0 ≤ firstLift (group cell) h (denominator cell) S := by
  rw [firstLift_eq_cells]
  exact mul_nonneg hh (Finset.prod_nonneg fun _ _ => (cellFactor_positive _ _ _).le)

/-- Both inequalities hold on every actual chain state, with no extra
assumption about which cells contain the hole and full pair. -/
theorem chain_lifts_compare (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hS : ChainState pairs S)
    (W : ℕ) (hW : 0 < W) (hbW : ∀ c, width cell c < W)
    (hh : 0 ≤ h (groupCount (group cell) S)) :
    (1/(W:ℝ)^2) * firstLift (group cell) h (denominator cell) S ≤
        secondLift (group cell) h (denominator cell) S ∧
    secondLift (group cell) h (denominator cell) S ≤
        (W:ℝ)^2 * firstLift (group cell) h (denominator cell) S := by
  rcases hS with hS | ⟨p,q,hS⟩
  · rw [plain_lifts_agree cell h S hS]
    have hf := firstLift_nonnegative cell h S hh
    have hWr : (1:ℝ) ≤ W := by exact_mod_cast hW
    have hsq : (1:ℝ) ≤ (W:ℝ)^2 := by nlinarith
    constructor
    · exact mul_le_of_le_one_left hf ((div_le_one (by positivity)).mpr hsq)
    · exact le_mul_of_one_le_left hf hsq
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp (show p ∈ Finset.univ.toList.map pair from hS.1)
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp (show q ∈ Finset.univ.toList.map pair from hS.2.1)
    exact defect_lifts_compare cell h S ⟨a,b,hS⟩ W hW hbW hh

/-- The pointwise comparison used by the actual original-chain variance
argument is supplied by the factorial state counts. -/
theorem firstLift_le_square_secondLift (cell : P → C) (h : ((C × Bool) → ℕ) → ℝ)
    (S : Set (P × Bool)) (hS : ChainState pairs S)
    (W : ℕ) (hW : 0 < W) (hbW : ∀ c, width cell c < W)
    (hh : 0 ≤ h (groupCount (group cell) S)) :
    firstLift (group cell) h (denominator cell) S ≤
        (W:ℝ)^2 * secondLift (group cell) h (denominator cell) S := by
  have hl := (chain_lifts_compare cell h S hS W hW hbW hh).1
  have hp : (0:ℝ) < (W:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hW)
  have hdiv : firstLift (group cell) h (denominator cell) S/(W:ℝ)^2 ≤
      secondLift (group cell) h (denominator cell) S := by
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using hl
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hdiv

end ContingencyTables.TwoLiftStates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DegreeCompletion
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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
open CommonBasesFPRAS BinaryContraction RecursiveSignedTransport

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

/-- Actual two-pair masses satisfy the determinant bound on their valid
cardinality layer; completion disappears from the conclusion. -/
theorem slotDefect_pair_bound_degree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) (hps : SlotsFresh ps A)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    4 * slotDefect ps f A p r * slotDefect ps f A r p ≤ (slotTotal ps f A)^2 := by
  have h := slotDefect_pair_bound ps (completeDegree f k) (completeDegree_positive f k hf)
    (completeDegree_hasSlotSignature f k hf hsig) A hps p r hp hr hpr
  rwa [slotDefect_completeDegree ps f k A hdegree hps p r hp hr hpr,
    slotDefect_completeDegree ps f k A hdegree hps r p hr hp hpr.symm,
    slotTotal_completeDegree ps f k A hdegree] at h

/-- Actual three-pair masses satisfy the cross-entry bound, obtained from
full cubic contraction while retaining the contracted pair coordinates. -/
theorem slotDefect_triple_bound_degree (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) (hps : SlotsFresh ps A)
    (p r t : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (ht : t ∈ ps)
    (hpr : p ≠ r) (hrt : r ≠ t) (hpt : p ≠ t) :
    slotDefect ps f A p r * slotDefect ps f A r t ≤
      slotTotal ps f A * slotDefect ps f A p t := by
  have h := slotDefect_triple_bound ps (completeDegree f k) (completeDegree_positive f k hf)
    (completeDegree_hasSlotSignature f k hf hsig) A hps p r t hp hr ht hpr hrt hpt
  rwa [slotDefect_completeDegree ps f k A hdegree hps p r hp hr hpr,
    slotDefect_completeDegree ps f k A hdegree hps r t hr ht hrt,
    slotDefect_completeDegree ps f k A hdegree hps p t hp ht hpt,
    slotTotal_completeDegree ps f k A hdegree] at h

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

omit [Fintype Γ] in
lemma VarianceNode.cover {gs ps : List (Γ × Γ)} {A B : Set Γ}
    (hnode : VarianceNode gs ps A B) (hcover : pairSupport gs = Set.univ) :
    A ∪ B ∪ pairSupport ps = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ pairSupport gs := hcover ▸ Set.mem_univ x
  obtain ⟨r, hr, hx⟩ := hx
  by_cases hm : r ∈ ps
  · exact Or.inr ⟨r, hm, hx⟩
  · rcases hnode.2.2.2 r hr hm with h | h
    · rcases hx with rfl | rfl
      · exact Or.inl (Or.inl h.1)
      · exact Or.inl (Or.inr h.2)
    · rcases hx with rfl | rfl
      · exact Or.inl (Or.inr h.2)
      · exact Or.inl (Or.inl h.1)

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

/-- The complementary second lift satisfies the same oriented defect
inequalities, although its raw signature role is omission rather than addition. -/
theorem complement_defect_pair (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k)
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (hdegree : B.ncard + ps.length = k)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    4 * slotDefect ps (complementWeight f) A p r *
      slotDefect ps (complementWeight f) A r p ≤ (slotTotal ps (complementWeight f) A)^2 := by
  rw [slotDefect_complement ps f A B hAB hps hcover p r hp hr hpr,
    slotDefect_complement ps f A B hAB hps hcover r p hr hp hpr.symm,
    slotTotal_complement ps f A B hAB hps hcover]
  exact slotDefect_pair_bound_degree ps f k hf hsig B hdegree
    (hps.mono Set.subset_union_right) r p hr hp hpr.symm

/-- Reversing all defect labels preserves the three-pair cross-entry bound. -/
theorem complement_defect_triple (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k)
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (hdegree : B.ncard + ps.length = k)
    (p r t : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (ht : t ∈ ps)
    (hpr : p ≠ r) (hrt : r ≠ t) (hpt : p ≠ t) :
    slotDefect ps (complementWeight f) A p r * slotDefect ps (complementWeight f) A r t ≤
      slotTotal ps (complementWeight f) A * slotDefect ps (complementWeight f) A p t := by
  rw [slotDefect_complement ps f A B hAB hps hcover p r hp hr hpr,
    slotDefect_complement ps f A B hAB hps hcover r t hr ht hrt,
    slotDefect_complement ps f A B hAB hps hcover p t hp ht hpt,
    slotTotal_complement ps f A B hAB hps hcover]
  simpa only [mul_comm] using slotDefect_triple_bound_degree ps f k hf hsig B hdegree
    (hps.mono Set.subset_union_right) t r p ht hr hp hrt.symm hpr.symm hpt.symm

end ContingencyTables.PairedComplement

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ObservableVariance
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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
open CommonBasesFPRAS BinaryContraction RecursiveSignedTransport DegreeCompletion PairedComplement

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma choiceVertices_plain_node (gs ps : List (Γ × Γ)) (A B : Set Γ)
    (hnode : VarianceNode gs ps A B) (S : Set Γ) (hS : S ∈ choiceVertices ps A) :
    PlainState gs S := by
  have hfresh := hnode.2.1.mono Set.subset_union_left
  have hs := (mem_choiceVertices_iff ps A S hfresh).mp hS
  have hdis : Disjoint B S := choiceVertices_excluded ps A B S hnode.1
    (fun r hr => by
      have h := hnode.2.1.elements_fresh r hr
      exact ⟨fun hx => h.1 (Or.inr hx), fun hx => h.2 (Or.inr hx)⟩) hS
  intro r hr
  by_cases hm : r ∈ ps
  · exact hs.2.2 r hm
  · exact hnode.2.2.2.single ⟨hs.1, hdis⟩ r hr hm

lemma choiceVertices_defect_node (gs ps : List (Γ × Γ)) (A B : Set Γ)
    (hnode : VarianceNode gs ps A B) (p r : Γ × Γ)
    (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r)
    (S : Set Γ) (hS : S ∈ choiceVertices ((ps.erase p).erase r) (insert r.1 (insert r.2 A))) :
    DefectState gs p r S := by
  let qs := (ps.erase p).erase r
  have hperm : ps.Perm (p::r::qs) := slots_perm_two hp hr hpr
  have hh := (SlotsFresh.perm hperm (A ∪ B)).mp hnode.2.1
  have hq : SlotsFresh qs (insert r.1 (insert r.2 A)) := by
    apply hh.2.2.2.2.2.2.mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_union] at hx ⊢
    tauto
  have hs := (mem_choiceVertices_iff qs _ S hq).mp hS
  have hB : Disjoint B S := choiceVertices_excluded qs _ B S
    (by
      apply Set.disjoint_insert_left.mpr
      refine ⟨fun hx => hh.2.2.2.2.1 (Or.inr (Or.inr (Or.inr hx))), ?_⟩
      apply Set.disjoint_insert_left.mpr
      exact ⟨fun hx => hh.2.2.2.2.2.1 (Or.inr (Or.inr (Or.inr hx))), hnode.1⟩)
    (fun t ht => by
      have h := hh.2.2.2.2.2.2.elements_fresh t ht
      exact ⟨fun hx => h.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))),
        fun hx => h.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx)))))⟩) hS
  have hep : PairEmpty p S := by
    have hn (x : Γ) (hxA : x ∉ A) (hxr₁ : x ≠ r.1) (hxr₂ : x ≠ r.2)
        (hxq : x ∉ pairSupport qs) : x ∉ S := by
      intro hx
      have := hs.2.1 hx
      simp only [Set.mem_union, Set.mem_insert_iff] at this
      tauto
    have hr₁ := hh.2.2.2.2.1
    have hr₂ := hh.2.2.2.2.2.1
    have hqd := hh.2.2.2.2.2.2.support_disjoint
    constructor
    · apply hn p.1 (fun h => hh.2.1 (Or.inl h))
      · intro h; exact hr₁ (Or.inl h.symm)
      · intro h; exact hr₂ (Or.inl h.symm)
      · intro h; exact Set.disjoint_left.mp hqd h (Or.inr (Or.inr (Or.inl rfl)))
    · apply hn p.2 (fun h => hh.2.2.1 (Or.inl h))
      · intro h; exact hr₁ (Or.inr (Or.inl h.symm))
      · intro h; exact hr₂ (Or.inr (Or.inl h.symm))
      · intro h; exact Set.disjoint_left.mp hqd h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  refine ⟨hnode.2.2.1 p hp, hnode.2.2.1 r hr, hpr, hep,
    ⟨hs.1 (Or.inl rfl), hs.1 (Or.inr (Or.inl rfl))⟩, ?_⟩
  intro t ht htp htr
  by_cases hm : t ∈ ps
  · exact hs.2.2 t ((List.mem_erase_of_ne htr).mpr ((List.mem_erase_of_ne htp).mpr hm))
  · exact hnode.2.2.2.single ⟨fun x hx => hs.1 (Or.inr (Or.inr hx)), hB⟩ t ht hm

lemma slotTotal_node_agreement (gs ps : List (Γ × Γ)) (f g : Set Γ → ℝ)
    (hagree : ∀ S, PlainState gs S → f S = g S) (A B : Set Γ)
    (hnode : VarianceNode gs ps A B) : slotTotal ps f A = slotTotal ps g A := by
  have hfr := hnode.2.1.mono Set.subset_union_left
  rw [slotTotal_eq_choice_sum ps A f hfr, slotTotal_eq_choice_sum ps A g hfr]
  exact Finset.sum_congr rfl (fun S hS => hagree S (choiceVertices_plain_node gs ps A B hnode S hS))

lemma slotDefect_node_comparison (gs ps : List (Γ × Γ)) (f g : Set Γ → ℝ) (q : ℝ)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S) (A B : Set Γ)
    (hnode : VarianceNode gs ps A B) (p r : Γ × Γ)
    (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    slotDefect ps f A p r ≤ q*slotDefect ps g A p r := by
  let qs := (ps.erase p).erase r
  have hh := (SlotsFresh.perm (slots_perm_two hp hr hpr) (A ∪ B)).mp hnode.2.1
  have hq : SlotsFresh qs (insert r.1 (insert r.2 A)) := by
    apply hh.2.2.2.2.2.2.mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_union] at hx ⊢
    tauto
  unfold slotDefect
  rw [slotTotal_eq_choice_sum qs _ f hq, slotTotal_eq_choice_sum qs _ g hq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  exact hcompare S (Or.inr ⟨p, r, choiceVertices_defect_node gs ps A B hnode p r hp hr hpr S hS⟩)

lemma complement_global_pair_bound (ps : List (Γ × Γ)) (g : Set Γ → ℝ)
    (hg : ∀ S, 0 < g S) (hsig : HasSlotSignature (complementWeight g))
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    4 * slotDefect ps g A p r * slotDefect ps g A r p ≤ (slotTotal ps g A)^2 := by
  have hh := complement_defect_pair ps (complementWeight g) (B.ncard + ps.length)
    (fun S _ => hg Sᶜ) (fun S _ => hsig [] S) A B hAB hps hcover rfl p r hp hr hpr
  have hcc : complementWeight (complementWeight g) = g := by
    funext S
    simp [complementWeight]
  rwa [hcc] at hh

lemma complement_global_triple_bound (ps : List (Γ × Γ)) (g : Set Γ → ℝ)
    (hg : ∀ S, 0 < g S) (hsig : HasSlotSignature (complementWeight g))
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (p r t : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (ht : t ∈ ps)
    (hpr : p ≠ r) (hrt : r ≠ t) (hpt : p ≠ t) :
    slotDefect ps g A p r * slotDefect ps g A r t ≤ slotTotal ps g A * slotDefect ps g A p t := by
  have hh := complement_defect_triple ps (complementWeight g) (B.ncard + ps.length)
    (fun S _ => hg Sᶜ) (fun S _ => hsig [] S) A B hAB hps hcover rfl p r t hp hr ht hpr hrt hpt
  have hcc : complementWeight (complementWeight g) = g := by
    funext S
    simp [complementWeight]
  rwa [hcc] at hh

/-- The sink is proved from the second lift's two- and three-pair inequalities;
its raw signature is in the complementary coordinates. -/
lemma twoLift_scores_sink (gs ps : List (Γ × Γ)) (g : Set Γ → ℝ)
    (hg : ∀ S, 0 < g S) (hsig : HasSlotSignature (complementWeight g))
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (A B : Set Γ) (hnode : VarianceNode gs ps A B) (hne : ps ≠ []) :
    ∃ p ∈ ps, ∀ r ∈ ps, p ≠ r →
      slotDefect ps g A r p * slotDefect gs g ∅ p r ≤ slotTotal ps g A * slotTotal gs g ∅ := by
  let J := {p : Γ × Γ // p ∈ ps}
  have : Nonempty J := by
    obtain ⟨p,hp⟩ := List.exists_mem_of_ne_nil ps hne
    exact ⟨⟨p,hp⟩⟩
  have hne' : ∀ p r : J, p ≠ r → p.val ≠ r.val := fun p r h he => h (Subtype.ext he)
  have hglobal : VarianceNode gs gs ∅ ∅ := ⟨by simp, by simpa using hgs,
    fun _ => id, fun r hr hn => False.elim (hn hr)⟩
  have hpfr := hnode.2.1.mono Set.subset_union_left
  obtain ⟨p,hp⟩ := coefficient_scores_sink
    (fun p r : J => slotDefect ps g A r.val p.val)
    (fun p r : J => slotDefect gs g ∅ r.val p.val)
    (slotTotal ps g A) (slotTotal gs g ∅)
    (slotTotal_pos ps g hg A hpfr) (slotTotal_pos gs g hg ∅ hgs)
    (fun p r h => (slotDefect_pos ps g hg A hpfr r p r.property p.property (hne' r p h.symm)).le)
    (fun p r h => (slotDefect_pos gs g hg ∅ hgs r p (hnode.2.2.1 r r.property)
      (hnode.2.2.1 p p.property) (hne' r p h.symm)).le)
    (fun p r h => complement_global_pair_bound ps g hg hsig A B hnode.1 hnode.2.1
      (PairedComplement.VarianceNode.cover hnode hcover) r p r.property p.property (hne' r p h.symm))
    (fun p r h => complement_global_pair_bound gs g hg hsig ∅ ∅ hglobal.1 hglobal.2.1
      (PairedComplement.VarianceNode.cover hglobal hcover) r p (hnode.2.2.1 r r.property) (hnode.2.2.1 p p.property) (hne' r p h.symm))
    (fun p r t h₁ h₂ h₃ => by
      simpa only [mul_comm] using complement_global_triple_bound ps g hg hsig A B hnode.1 hnode.2.1
        (PairedComplement.VarianceNode.cover hnode hcover) t r p t.property r.property p.property
        (hne' t r h₂.symm) (hne' r p h₁.symm) (hne' t p h₃.symm))
    (fun p r t h₁ h₂ h₃ => by
      simpa only [mul_comm] using complement_global_triple_bound gs g hg hsig ∅ ∅ hglobal.1 hglobal.2.1
        (PairedComplement.VarianceNode.cover hglobal hcover) t r p (hnode.2.2.1 t t.property) (hnode.2.2.1 r r.property)
        (hnode.2.2.1 p p.property) (hne' t r h₂.symm) (hne' r p h₁.symm) (hne' t p h₃.symm))
  refine ⟨p.val,p.property,?_⟩
  intro r hr hpr
  exact hp ⟨r,hr⟩ (fun h => hpr (congrArg Subtype.val h))

/-- One transport split costs at most 1+8s q². -/
theorem transport_node_variance_twoLift (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) (q : ℝ)
    (hf : ∀ S, 0 < f S) (hSig : HasSlotSignature f)
    (hpd : p ≠ d) (hpA : p ∉ A) (hdA : d ∉ A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p ∈ ps, W p.1 = W p.2)
    (hWp : W p = 1) (hWd : W d = 1)
    (hsink : ∀ x ∈ slotPunctures ps,
      slotTotal x.2 f (insert p (insert d A))/W x.1.1 ≤
        4*q^2*(slotTotal ps f (insert p A)+slotTotal ps f (insert d A))) :
    let sp := slotTotal ps f (insert p A)
    let sd := slotTotal ps f (insert d A)
    sp*sd/(sp+sd) *
      (slotTotal ps (fun S => f S*H S) (insert p A)/sp -
        slotTotal ps (fun S => f S*H S) (insert d A)/sd)^2 ≤
      (1+8*(ps.length : ℝ)*q^2)*slotGraphEnergy ps f H A (rootEmbedding p d) W := by
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
    (fun x => slotTotal x.2 f (insert p (insert d A))/W x.1.1) (4*q^2*(sp+sd)) hsink
  rw [slotPunctures_length] at hsum
  have hcoef : sp*sd/(sp+sd)*rootCoefficient ps f A p d W ≤ 1+8*(ps.length : ℝ)*q^2 := by
    unfold rootCoefficient
    change sp*sd/(sp+sd)*(1/(sp*W p)+1/(sd*W d)+2/(sp*sd)*_) ≤ _
    rw [hWp,hWd,mul_one,mul_one]
    have heq (s : ℝ) : sp*sd/(sp+sd)*(1/sp+1/sd+2/(sp*sd)*s) = 1+2/(sp+sd)*s := by
      field_simp
      ; ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2/(sp+sd) by positivity)
    have heq' : 2/(sp+sd)*((ps.length : ℝ)*(4*q^2*(sp+sd))) = 8*(ps.length : ℝ)*q^2 := by
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

lemma twoLift_variance_node (gs ps : List (Γ × Γ)) (f g H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hf : ∀ S, 0 < f S) (hg : ∀ S, 0 < g S)
    (hsigf : HasSlotSignature f) (hsigg : HasSlotSignature (complementWeight g))
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅ / (4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S)
    (A B : Set Γ) (hnode : VarianceNode gs ps A B) (hne : ps ≠ []) :
    ∃ p qs, ps.Perm (p::qs) ∧ SlotsFresh (p::qs) A ∧
      VarianceNode gs qs (insert p.1 A) (insert p.2 B) ∧
      VarianceNode gs qs (insert p.2 A) (insert p.1 B) ∧
      slotVariance (p::qs) f H A - slotVariance qs f H (insert p.1 A) -
        slotVariance qs f H (insert p.2 A) ≤
        (1+8*(gs.length : ℝ)*q^2)*restrictedEnergy (chainEdges gs) (chainConductance gs w f) H A B := by
  obtain ⟨p,hp,hsink⟩ := twoLift_scores_sink gs ps g hg hsigg hgs hcover A B hnode hne
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
    rw [pairMultiplier_on hps _ r hr r.1 (Or.inl rfl), pairMultiplier_on hps _ r hr r.2 (Or.inr rfl)]
  have hWp : W p.1 = 1 := pairMultiplier_fresh hps _ _ (Or.inr ⟨false,rfl⟩)
  have hWd : W p.2 = 1 := pairMultiplier_fresh hps _ _ (Or.inr ⟨true,rfl⟩)
  have hglobal : VarianceNode gs gs ∅ ∅ := ⟨by simp, by simpa using hgs,
    fun _ => id, fun r hr hn => False.elim (hn hr)⟩
  have hz : slotTotal ps g A = slotTotal ps f A := (slotTotal_node_agreement gs ps f g hagree A B hnode).symm
  have hC : slotTotal gs g ∅ = slotTotal gs f ∅ := (slotTotal_node_agreement gs gs f g hagree ∅ ∅ hglobal).symm
  have hsink' : ∀ x ∈ slotPunctures qs,
      slotTotal x.2 f (insert p.1 (insert p.2 A))/W x.1.1 ≤
        4*q^2*(slotTotal qs f (insert p.1 A)+slotTotal qs f (insert p.2 A)) := by
    intro x hx
    have hxq : x.1 ∈ qs := (slotPunctures_perm qs x hx).mem_iff.mpr List.mem_cons_self
    have hxp : p ≠ x.1 := hfr.pair_ne_of_mem hxq
    have hxps : x.1 ∈ ps := hperm.mem_iff.mpr (List.mem_cons_of_mem _ hxq)
    have hpG := hnode.2.2.1 p hp
    have hxG := hnode.2.2.1 x.1 hxps
    have hcpos := slotDefect_pos gs f hf ∅ hgs p x.1 hpG hxG hxp
    have hzpos := slotTotal_pos ps f hf A (hnode.2.1.mono Set.subset_union_left)
    have hs := hsink x.1 hxps hxp
    rw [hz,hC] at hs
    have hm := mul_le_mul
      (slotDefect_node_comparison gs ps f g q hcompare A B hnode x.1 p hxps hp hxp.symm)
      (slotDefect_node_comparison gs gs f g q hcompare ∅ ∅ hglobal p x.1 hpG hxG hxp)
      hcpos.le (mul_nonneg hq (slotDefect_pos ps g hg A (hnode.2.1.mono Set.subset_union_left)
        x.1 p hxps hp hxp.symm).le)
    have hs' : slotDefect ps f A x.1 p * slotDefect gs f ∅ p x.1 ≤
        q^2*(slotTotal ps f A * slotTotal gs f ∅) := by
      calc
        _ ≤ (q*slotDefect ps g A x.1 p)*(q*slotDefect gs g ∅ p x.1) := hm
        _ = q^2*(slotDefect ps g A x.1 p*slotDefect gs g ∅ p x.1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg q)
    rw [slotDefect_perm hperm,slotDefect_puncture qs p A f hfrA x hx] at hs'
    have hg := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hcpos)).mp (hgood p hpG x.1 hxG hxp)
    have hgz := mul_le_mul_of_nonneg_left hg (mul_nonneg (sq_nonneg q) hzpos.le)
    have hbound : slotTotal x.2 f (insert p.1 (insert p.2 A)) ≤
        4*q^2*slotTotal ps f A*w p x.1 := by
      apply (mul_le_mul_iff_of_pos_right hcpos).mp
      nlinarith
    change slotTotal x.2 f (insert p.1 (insert p.2 A))/pairMultiplier qs (w p) x.1.1 ≤ _
    rw [pairMultiplier_on hps _ x.1 hxq x.1.1 (Or.inl rfl)]
    apply (div_le_iff₀ (hw p x.1)).mpr
    rw [slotTotal_perm hperm f,slotTotal_cons p qs f A hfrA.1 hfrA.2.1 hfrA.2.2.1] at hbound
    exact hbound
  have ht := transport_node_variance_twoLift qs f H A p.1 p.2 W q hf hsigf
    hfrA.1 hfrA.2.1 hfrA.2.2.1 hps hW hws hWp hWd hsink'
  have he := variance_energy_identification gs qs A B p w f H hw hf
    hnode'.2.2.1 hnode'.1 hfr hnode'.2.2.2
  have hqle : qs.length ≤ gs.length := by
    have hnodup := (hnode.2.1.nodup).erase p
    exact List.Subperm.length_le (List.subperm_of_subset hnodup (fun r hr => hnode'.2.2.1 r (List.mem_cons_of_mem _ hr)))
  have hqleR : (qs.length : ℝ) ≤ gs.length := by exact_mod_cast hqle
  have hcoef : 1+8*(qs.length:ℝ)*q^2 ≤ 1+8*(gs.length:ℝ)*q^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hqleR (sq_nonneg q)]
  have hepos : 0 ≤ restrictedEnergy (chainEdges gs) (chainConductance gs w f) H A B := by
    apply restrictedEnergy_nonneg
    intro ST _
    exact le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
  have hfinal := ht.trans ((mul_le_mul_of_nonneg_left he
    (by positivity : (0:ℝ) ≤ 1+8*(qs.length:ℝ)*q^2)).trans
    (mul_le_mul_of_nonneg_right hcoef hepos))
  refine ⟨p,qs,hperm,hfrA,hnode'.children.1,hnode'.children.2,?_⟩
  rw [slotVariance_split qs f H hf A p hfrA,slotTotal_cons p qs f A hfrA.1 hfrA.2.1 hfrA.2.2.1]
  linarith

/-- Actual adaptive variance bound with the paper's Cp=p(1+8p q²).
No variance, sink, or transport estimate is an input to this theorem. -/
theorem twoLift_transversal_variance (gs : List (Γ × Γ)) (f g H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hf : ∀ S, 0 < f S) (hg : ∀ S, 0 < g S)
    (hsigf : HasSlotSignature f) (hsigg : HasSlotSignature (complementWeight g))
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅ / (4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S) :
    slotVariance gs f H ∅ ≤ (gs.length : ℝ)*(1+8*(gs.length : ℝ)*q^2)*
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  apply adaptive_variance_bound f H hf (chainEdges gs) (chainConductance gs w f)
    (fun ST _ => le_min (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le)
      (mul_nonneg (chainMultiplier_pos gs w hw _).le (hf _).le))
    (1+8*(gs.length:ℝ)*q^2) (by positivity) (VarianceNode gs)
    (fun ps A B hnode hne => twoLift_variance_node gs ps f g H w q hq hf hg hsigf hsigg
      hgs hcover hw hgood hagree hcompare A B hnode hne)
  exact ⟨by simp,by simpa using hgs,fun _ => id,fun r hr hn => False.elim (hn hr)⟩

lemma slotVariance_completeDegree (ps : List (Γ × Γ)) (f H : Set Γ → ℝ) (k : ℕ)
    (A : Set Γ) (hdegree : A.ncard + ps.length = k) :
    slotVariance ps (completeDegree f k) H A = slotVariance ps f H A := by
  have hs (h : Set Γ → ℝ) : slotTotal ps (fun S => completeDegree f k S * h S) A =
      slotTotal ps (fun S => f S * h S) A := by
    apply coeffDerivs_degree_congr _ _ _ k
    · intro S hS
      simp [completeDegree, hS]
    · simpa only [List.length_map] using hdegree
  unfold slotVariance
  rw [hs, hs, slotTotal_completeDegree ps f k A hdegree]

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

/-- Completion is eliminated from the genuine fixed-degree variance bound.
Only the transport lift's addition signature and the other lift's omission
signature in these encoded coordinates are assumed. -/
theorem validDegree_twoLift_transversal_variance (gs : List (Γ × Γ)) (f g H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hf : DegreePositive f gs.length) (hg : DegreePositive g gs.length)
    (hsigf : AdditionProperty f gs.length) (hsigg : OmissionProperty g gs.length)
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅ / (4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S) :
    slotVariance gs f H ∅ ≤ (gs.length : ℝ)*(1+8*(gs.length : ℝ)*q^2)*
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  let F := completeDegree f gs.length
  let G := complementWeight (completeDegree (complementWeight g) (Fintype.card Γ - gs.length))
  have hk : gs.length ≤ Fintype.card Γ := by
    have hc := slots_ground_card gs hgs hcover
    omega
  have hgc := complement_degreePositive g gs.length hk hg
  have hF : ∀ S, 0 < F S := completeDegree_positive f gs.length hf
  have hG : ∀ S, 0 < G S := fun S => completeDegree_positive _ _ hgc Sᶜ
  have hFsig := completeDegree_hasSlotSignature f gs.length hf hsigf
  have hGsig : HasSlotSignature (complementWeight G) := by
    have heq : complementWeight G = completeDegree (complementWeight g) (Fintype.card Γ - gs.length) := by
      funext S
      simp [G, complementWeight]
    rw [heq]
    exact completeDegree_hasSlotSignature _ _ hgc hsigg
  have hF_eq (S : Set Γ) (hS : S.ncard = gs.length) : F S = f S := by
    simp [F, completeDegree, hS]
  have hG_eq (S : Set Γ) (hS : S.ncard = gs.length) : G S = g S := by
    have hc := S.ncard_add_ncard_compl
    simp only [Nat.card_eq_fintype_card] at hc
    have hSc : Sᶜ.ncard = Fintype.card Γ - gs.length := by omega
    simp [G, complementWeight, completeDegree, hSc]
  have hgood' : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs F ∅ / (4*slotDefect gs F ∅ p r) ≤ w p r := by
    intro p hp r hr hpr
    dsimp only [F]
    rw [slotTotal_completeDegree gs f gs.length ∅ (by simp),
      slotDefect_completeDegree gs f gs.length ∅ (by simp) hgs p r hp hr hpr]
    exact hgood p hp r hr hpr
  have hagree' : ∀ S, PlainState gs S → F S = G S := by
    intro S hS
    rw [hF_eq S (hS.ncard hgs hcover), hG_eq S (hS.ncard hgs hcover)]
    exact hagree S hS
  have hcompare' : ∀ S, ChainState gs S → F S ≤ q*G S := by
    intro S hS
    rw [hF_eq S (hS.ncard hgs hcover), hG_eq S (hS.ncard hgs hcover)]
    exact hcompare S hS
  have ht := twoLift_transversal_variance gs F G H w q hq hF hG hFsig hGsig
    hgs hcover hw hgood' hagree' hcompare'
  rwa [slotVariance_completeDegree gs f H gs.length ∅ (by simp),
    restrictedEnergy_completeDegree gs f H w hgs hcover ∅ ∅] at ht

end ContingencyTables.ObservableVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ObservableBounds
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma chainTotal_completion (gs : List (Γ × Γ)) (f : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : chainTotal gs w (completeDegree f gs.length) = chainTotal gs w f := by
  unfold chainTotal chainWeight
  apply Finset.sum_congr rfl
  intro S hS
  have hd := ((Finset.mem_filter.mp hS).2).ncard hgs hcover
  simp only [completeDegree, hd, ite_true, if_true]

end ContingencyTables.ObservableBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ComplementChain
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma plain_mass_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ) :
    slotTotal gs (complementWeight f) ∅ = slotTotal gs f ∅ := by
  exact slotTotal_complement gs f ∅ ∅ (by simp) (by simpa using hgs) (by simpa using hcover)

lemma defect_mass_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ)
    (p r : Γ × Γ) (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r) :
    slotDefect gs (complementWeight f) ∅ p r = slotDefect gs f ∅ r p := by
  exact slotDefect_complement gs f ∅ ∅ (by simp) (by simpa using hgs) (by simpa using hcover) p r hp hr hpr

lemma slotVariance_complement (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f H : Set Γ → ℝ) :
    slotVariance gs (complementWeight f) (complementWeight H) ∅ = slotVariance gs f H ∅ := by
  unfold slotVariance
  change slotTotal gs (complementWeight (fun S => f S*(H S)^2)) ∅ -
    (slotTotal gs (complementWeight (fun S => f S*H S)) ∅)^2/slotTotal gs (complementWeight f) ∅ = _
  rw [plain_mass_complement gs hgs hcover, plain_mass_complement gs hgs hcover,
    plain_mass_complement gs hgs hcover]

/-- The actual manuscript variance theorem in original omission coordinates. -/
theorem omission_twoLift_transversal_variance (gs : List (Γ × Γ)) (f g H : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hf : DegreePositive f gs.length) (hg : DegreePositive g gs.length)
    (hsigf : OmissionProperty f gs.length) (hsigg : AdditionProperty g gs.length)
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs = Set.univ)
    (hw : ∀ p r, 0 < w p r)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S) :
    slotVariance gs f H ∅ ≤ (gs.length : ℝ)*(1+8*(gs.length : ℝ)*q^2)*
      restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅ := by
  have hcard := slots_ground_card gs hgs hcover
  have hhalf : Fintype.card Γ - gs.length = gs.length := by omega
  have hfc : DegreePositive (complementWeight f) gs.length := by
    simpa only [hhalf] using complement_degreePositive f gs.length (by omega) hf
  have hgc : DegreePositive (complementWeight g) gs.length := by
    simpa only [hhalf] using complement_degreePositive g gs.length (by omega) hg
  have hsf : AdditionProperty (complementWeight f) gs.length := by
    simpa only [OmissionProperty, hhalf] using hsigf
  have hsg : OmissionProperty (complementWeight g) gs.length := by
    have hcc : complementWeight (complementWeight g) = g := by funext S; simp [complementWeight]
    simpa only [OmissionProperty, hhalf, hcc] using hsigg
  have hgood' : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r →
      slotTotal gs (complementWeight f) ∅/(4*slotDefect gs (complementWeight f) ∅ p r) ≤ reverseMultiplier w p r := by
    intro p hp r hr hpr
    rw [plain_mass_complement gs hgs hcover, defect_mass_complement gs hgs hcover f p r hp hr hpr]
    exact hgood r hr p hp hpr.symm
  have ht := validDegree_twoLift_transversal_variance gs (complementWeight f) (complementWeight g)
    (complementWeight H) (reverseMultiplier w) q hq hfc hgc hsf hsg hgs hcover
    (fun p r => hw r p) hgood'
    (fun S hS => hagree Sᶜ ((plain_complement gs S).mpr hS))
    (fun S hS => hcompare Sᶜ ((state_complement gs S).mpr hS))
  rwa [slotVariance_complement gs hgs hcover f H, energy_complement gs w f H] at ht

end ContingencyTables.ComplementChain

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TraceBounds
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Trace mixing for the actual omission-lift Metropolis chain

The finite-chain constructor receives the proved positive completion.
Its state weights equal the original valid-degree weights, and the
transversal trace has the original normalized factorial-lift law.
The trace Poincaré bound uses the proved manuscript-coordinate variance
bound, followed by the existing harmonic-extension and spectral arguments.
-/

namespace ContingencyTables.TraceBounds

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion ObservableVariance ObservableBounds ComplementChain RecursiveSignedTransport

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Exact inverse-gap bound 2p²Cp from the actual two-lift variance theorem. -/
theorem omission_trace_poincare (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r)
    (hf : DegreePositive f gs.length) (hg : DegreePositive g gs.length)
    (hsigf : OmissionProperty f gs.length) (hsigg : AdditionProperty g gs.length)
    (q : ℝ) (hq : 0 ≤ q)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S)
    (h : PlainIndex gs → ℝ) :
    let T := metropolisTrace gs hgs hne hcover w (completeDegree f gs.length) hw
      (completeDegree_positive f gs.length hf)
    T.variance h ≤ (2*(gs.length:ℝ)^2*((gs.length:ℝ)*(1+8*(gs.length:ℝ)*q^2)))*T.energy h := by
  let F := completeDegree f gs.length
  have hF := completeDegree_positive f gs.length hf
  let := plainIndex_nonempty gs hgs hcover
  let C := metropolisChain gs hgs hne hcover w F hw hF
  let Q := metropolisKilled gs hgs hne hcover w F hw hF
  let H := C.harmonicExtension (plainPredicate gs) Q h
  let J := extendChainFun gs H
  have hJ (S : ChainIndex gs) : J S.val = H S := extendChainFun_apply gs H S
  have hh (S : PlainIndex gs) : J S.val.val = h S := by
    rw [hJ]
    exact C.harmonicExtension_inside (plainPredicate gs) Q h S
  have hvar := metropolisTrace_variance gs hgs hne hcover w F hw hF J
  have hefun : (fun S : PlainIndex gs => J S.val.val) = h := funext hh
  rw [hefun, slotVariance_completeDegree gs f J gs.length ∅ (by simp),
    slotTotal_completeDegree gs f gs.length ∅ (by simp)] at hvar
  have hv := omission_twoLift_transversal_variance gs f g J w q hq hf hg hsigf hsigg
    hgs hcover hw hgood hagree hcompare
  have hz : 0 < slotTotal gs f ∅ := slotTotal_degree_positive gs f gs.length hf ∅ (by simp) hgs
  have henergy : restrictedEnergy (chainEdges gs) (chainConductance gs w f) J ∅ ∅ =
      (2*(gs.length:ℝ)^2*slotTotal gs f ∅)*(metropolisTrace gs hgs hne hcover w F hw hF).energy h := by
    have hc := metropolisChain_energy gs hgs hne hcover w F J hw hF
    have hfJn : (fun S : ChainIndex gs => J S.val) = H := funext hJ
    rw [hfJn] at hc
    change C.energy (C.harmonicExtension (plainPredicate gs) Q h) = _ at hc
    rw [C.traceChain_energy (plainPredicate gs) Q (by intro _ _; rfl)] at hc
    change C.insideMass (plainPredicate gs)*(metropolisTrace gs hgs hne hcover w F hw hF).energy h = _ at hc
    rw [metropolis_insideMass gs hgs hne hcover w F hw hF] at hc
    unfold chainDirichlet at hc
    rw [restrictedEnergy_completeDegree gs f J w hgs hcover ∅ ∅,
      slotTotal_completeDegree gs f gs.length ∅ (by simp)] at hc
    have hΛ := chainTotal_pos gs hgs hcover w F hF hw
    have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
    field_simp [ne_of_gt hn] at hc
    nlinarith
  rw [henergy] at hv
  dsimp only
  rw [hvar]
  apply (div_le_iff₀ hz).mpr
  nlinarith

lemma trace_constant_le_observable (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    2*p^2*(p*(1+8*p*q^2)) ≤ observableConstant p q := by
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hcoef : 2*p^2 ≤ 90*p^4 := by
    have hp2 : 1 ≤ p^2 := by nlinarith
    have hp4 : p^2 ≤ p^4 := by nlinarith [sq_nonneg (p^2-1)]
    nlinarith
  have hc : 0 ≤ p*(1+8*p*q^2) := by positivity
  have ht : 0 ≤ 10*p^4*(2*(8+32*p*q^3)) := by positivity
  calc
    _ ≤ 90*p^4*(p*(1+8*p*q^2)) := mul_le_mul_of_nonneg_right hcoef hc
    _ ≤ observableConstant p q := by unfold observableConstant; nlinarith

end ContingencyTables.TraceBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionConcentration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of the literal companion phase observables -/

namespace ContingencyTables.CompanionConcentration

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing
open TwoLiftStates BinaryContraction DegreeCompletion ObservableBounds

variable {I J : Type*} [Fintype I] [Fintype J]

lemma square_width_one_le (A : Instance I J) : (1:ℝ)≤(A.W:ℝ)^2 := by
  have hW : (2:ℝ)≤ A.W := by exact_mod_cast A.hW
  nlinarith

end ContingencyTables.CompanionConcentration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteTraceSlowdown
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace transition matrices under an exact holding slowdown -/

namespace ContingencyTables.FiniteChainSlowdown

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {Y : Type*} [Fintype Y]

lemma slowKilled_apply (Q : KilledKernel Y) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (f : Y → ℝ) (x : Y) :
    (slowKilled Q a ha0 ha1).apply f x=a*Q.apply f x+(1-a)*f x := by
  unfold KilledKernel.apply
  change (∑ y,(a*Q.Q x y+if x=y then 1-a else 0)*f y)=_
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,mul_assoc]
  rw [←Finset.mul_sum]
  simp

variable {X : Type*} [Fintype X]

/-- A holding step changes when the chain hits the selected set, but
not where it first hits. The equality follows from the Green residual
identity, without manipulating an infinite series term by term. -/
theorem hitKernel (C : FiniteChain X) (A : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside A))
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (x : FiniteChain.Outside A) (y : FiniteChain.Inside A) :
    (slow C a ha0.le ha1).hitKernel A (slowKilled Q a ha0 ha1) x y=C.hitKernel A Q x y := by
  let h : FiniteChain.Outside A → ℝ := fun z => C.hitKernel A Q z y
  have hh (z : FiniteChain.Outside A) : h z=C.P z.val y.val+Q.apply h z := by
    exact Q.green_firstStep (fun z => C.P z.val y.val) z
  have he (z : FiniteChain.Outside A) :
      (slow C a ha0.le ha1).P z.val y.val=h z-(slowKilled Q a ha0 ha1).apply h z := by
    have hzy : z.val≠y.val := fun he => z.property (he.symm ▸ y.property)
    change a*C.P z.val y.val+(if z.val=y.val then 1-a else 0)=_
    rw [ite_eq_right hzy,add_zero,slowKilled_apply]
    nlinarith [hh z]
  unfold FiniteChain.hitKernel
  simp_rw [he]
  exact (slowKilled Q a ha0 ha1).green_residual h x

/-- The trace itself acquires exactly the same holding factor. -/
theorem traceMatrix (C : FiniteChain X) (A : X → Prop)
    (Q : KilledKernel (FiniteChain.Outside A))
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (x y : FiniteChain.Inside A) :
    (slow C a ha0.le ha1).traceMatrix A (slowKilled Q a ha0 ha1) x y=
      a*C.traceMatrix A Q x y+if x=y then 1-a else 0 := by
  unfold FiniteChain.traceMatrix
  simp_rw [hitKernel C A Q a ha0 ha1]
  have he (z : FiniteChain.Outside A) : (slow C a ha0.le ha1).P x.val z.val=a*C.P x.val z.val := by
    have hxz : x.val≠z.val := fun he => z.property (he ▸ x.property)
    change a*C.P x.val z.val+(if x.val=z.val then 1-a else 0)=_
    rw [ite_eq_right hxz,add_zero]
  simp_rw [he,mul_assoc,←Finset.mul_sum]
  change (a*C.P x.val y.val+if x.val=y.val then 1-a else 0)+
    a*(∑ z : FiniteChain.Outside A,C.P x.val z.val*C.hitKernel A Q z y)=_
  have hiff : x.val=y.val ↔ x=y := ⟨Subtype.ext,congrArg Subtype.val⟩
  simp only [hiff]
  ring

theorem trace_energy (C : FiniteChain X) (A : X → Prop)
    [Nonempty (FiniteChain.Inside A)] (Q : KilledKernel (FiniteChain.Outside A))
    (hQ : ∀ x y : FiniteChain.Outside A,Q.Q x y=C.P x.val y.val)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (f : FiniteChain.Inside A → ℝ) :
    ((slow C a ha0.le ha1).traceChain A (slowKilled Q a ha0 ha1)
      (slowKilled_matches C A Q hQ a ha0 ha1)).energy f=
        a*(C.traceChain A Q hQ).energy f := by
  rw [FiniteChain.energy_eq,FiniteChain.energy_eq,←mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  change (C.π x.val/C.insideMass A)*
    (slow C a ha0.le ha1).traceMatrix A (slowKilled Q a ha0 ha1) x y*(f x-f y)^2=
      a*((C.π x.val/C.insideMass A)*C.traceMatrix A Q x y*(f x-f y)^2)
  rw [traceMatrix C A Q a ha0 ha1]
  by_cases h : x=y
  · subst y
    simp
  · simp only [h,ite_false,add_zero]
    ring

/-- This transfers the accepted trace Poincaré estimate to the actual
dyadic holding chain, rather than merely to a separately defined trace. -/
theorem trace_variance_bound (C : FiniteChain X) (A : X → Prop)
    [Nonempty (FiniteChain.Inside A)] (Q : KilledKernel (FiniteChain.Outside A))
    (hQ : ∀ x y : FiniteChain.Outside A,Q.Q x y=C.P x.val y.val)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (ha : 1/2 ≤ a)
    (K : ℝ) (hK : 0 ≤ K) (f : FiniteChain.Inside A → ℝ)
    (h : (C.traceChain A Q hQ).variance f ≤ K*(C.traceChain A Q hQ).energy f) :
    ((slow C a ha0.le ha1).traceChain A (slowKilled Q a ha0 ha1)
      (slowKilled_matches C A Q hQ a ha0 ha1)).variance f ≤
        (2*K)*((slow C a ha0.le ha1).traceChain A (slowKilled Q a ha0 ha1)
          (slowKilled_matches C A Q hQ a ha0 ha1)).energy f := by
  have hv : ((slow C a ha0.le ha1).traceChain A (slowKilled Q a ha0 ha1)
      (slowKilled_matches C A Q hQ a ha0 ha1)).variance f=(C.traceChain A Q hQ).variance f := rfl
  rw [hv,trace_energy C A Q hQ a ha0 ha1]
  have hm := mul_le_mul_of_nonneg_right ha ((C.traceChain A Q hQ).energy_nonneg f)
  have hh := mul_le_mul_of_nonneg_left hm hK
  nlinarith

end

end ContingencyTables.FiniteChainSlowdown

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLargeMarginal
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual balanced large-cell marginal for the explicit root selector

The raw removal and reflected signatures are derived from the physical
line/unary factors. No signature of the marginal is postulated.
-/

namespace ContingencyTables.RootedLargeMarginal

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty
open LargePairEnumeration BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

theorem largeMarginal_reflected (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (ha : 0≤ alpha) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) (R : ℕ) :
    RemovalSlice (fun z => largeMarginal A S alpha e
      (IntegerReflection.reflect (bounds A) z)) (bounds A) R := by
  let N : Fin n → ℕ := fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2
  have hu : ∀ a,0≤ ForestPenaltyApplication.unaryRate A.T A.b alpha a := by
    intro a
    unfold ForestPenaltyApplication.unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_rfl
  rw [largeMarginal_eq_eliminate]
  exact EqualityReindex.physical_marginal_reflected (LargePairEnumeration.widths N)
    (bounds A) R (physicalCoordinateEquiv (fun a : I×J => A.small a.1 a.2) e N)
    RowColumnPenalties.cellLine (rootFlag S) (fun _ => alpha)
    (ForestPenaltyApplication.lineOffset (ell A) (RootedPenalty.widths A) A.r A.c)
    RowColumnPenalties.viewSlope (ForestPenaltyApplication.unaryRate A.T A.b alpha)
    (ForestPenaltyApplication.unaryEll (ell A)) ForestPenaltyApplication.unarySlope
    (ForestPenaltyApplication.unaryCap A.b)
    (widths_lower N (large_width A e)) (fun _ => ha) hu

end ContingencyTables.RootedLargeMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root physical marginal is its literal completion count -/

namespace ContingencyTables.RootedCountIdentification

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty RootedLiteralCount
open ForestCountIdentification ForestAssignmentSplit ForestLiteralCount
open PhysicalLargeProfiles LargePairEnumeration BalancedBox GraphCompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

theorem h_reflected (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (ha : 0≤ alpha) (R : ℕ) :
    RemovalSlice (fun z => h A S alpha (IntegerReflection.reflect (bounds A) z)) (bounds A) R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => A.small a.1 a.2))).symm
  have hs := RootedLargeMarginal.largeMarginal_reflected A S alpha ha e R
  intro z hz ht
  rw [NestedReindex.removal_congr_box _ _ (bounds A) z hz (by
    intro x _
    apply h_eq_largeMarginal A S alpha e
    intro u
    exact Nat.sub_le _ _)]
  convert hs z hz ht using 1
  all_goals try with_reducible_and_instances rfl

end ContingencyTables.RootedCountIdentification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedFactorialApplication
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual factorial lifts of the selected-root completion count -/

namespace ContingencyTables.RootedFactorialApplication

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS CompanionFactorialApplication
open LargePairEnumeration BalancedBox LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The dual factorial lift retains positivity and has its actual
addition signature from the globally reflected raw count. -/
theorem second_properties (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (ha : 0≤alpha) :
    BinaryContraction.DegreePositive (g A R alpha) (Fintype.card (Labels A)) ∧
      BinaryContraction.AdditionProperty (g A R alpha) (Fintype.card (Labels A)) := by
  change BinaryContraction.DegreePositive
      (secondLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)) _ ∧
    BinaryContraction.AdditionProperty
      (secondLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)) _
  constructor
  · intro S _
    exact div_pos
      (mul_pos (RootedCountIdentification.h_positive A R alpha _) (FactorialSignatures.factorialProduct_positive _))
      (denominator_positive A)
  · have hs : @RemovalSlice (View A) _ (Classical.decEq _)
        (fun z => RootedCountIdentification.h A R alpha (IntegerReflection.reflect
          (groupCount (TwoLiftStates.group (labelCell A)) Set.univ) z))
        (groupCount (TwoLiftStates.group (labelCell A)) Set.univ)
        (Fintype.card (Labels A×Bool)-Fintype.card (Labels A)) := by
      rw [label_capacity]
      convert RootedCountIdentification.h_reflected A R alpha ha _ using 1
      all_goals try with_reducible_and_instances rfl
    convert ReflectedSlices.secondLift_addition_reflected_slice (TwoLiftStates.group (labelCell A))
      (RootedCountIdentification.h A R alpha) (denominator A) (Fintype.card (Labels A))
      (by simp only [Fintype.card_prod,Fintype.card_bool]; omega)
      (denominator_positive A) (fun z => (RootedCountIdentification.h_positive A R alpha z).le) hs using 1
    all_goals try with_reducible_and_instances rfl

end ContingencyTables.RootedFactorialApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBooleanKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root Boolean row law and full-history perturbation -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates RootedOracleAcceptance
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open FiniteLawMoments RealKernelApproximation
open CompanionBooleanPhase (State proposal proposalBits proposal_codes stepBits stepWordEquiv
  slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma chain_eq {X : Type*} [Fintype X] (C D : FiniteChain X)
    (hP : C.P=D.P) (hpi : C.π=D.π) : C=D := by
  cases C
  cases D
  dsimp only at hP hpi
  cases hP
  cases hpi
  rfl

/-- The degree completion used to prove the signature and concentration
theorems leaves every state and transition of the literal chain intact. -/
theorem referenceChain_eq_completed (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) :
    referenceChain A R j hp w hw=
      metropolisChain pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
        (fun p q => (w p q:ℝ))
        (DegreeCompletion.completeDegree (RootedAnnealing.weight A R j)
          (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length)
        (fun p q => by exact_mod_cast hw p q)
        (DegreeCompletion.completeDegree_positive _ _ (RootedWarmStart.actual_degree A R j).1) := by
  have he (U : State A) :
      chainWeight pairs (fun p q => (w p q:ℝ))
          (DegreeCompletion.completeDegree (RootedAnnealing.weight A R j)
            (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length) U.val=
        chainWeight pairs (fun p q => (w p q:ℝ)) (RootedAnnealing.weight A R j) U.val := by
    simp only [chainWeight,DegreeCompletion.completeDegree,
      U.property.ncard PairedLabels.fresh PairedLabels.cover,ite_true, if_true]
  apply chain_eq
  · funext S T
    dsimp only [referenceChain,metropolisChain,FiniteChain.ofMoves]
    simp only [metropolisMove,he]
  · funext S
    dsimp only [referenceChain,metropolisChain,FiniteChain.ofMoves]
    rw [ObservableBounds.chainTotal_completion _ _ _ PairedLabels.fresh PairedLabels.cover,he]

end
end ContingencyTables.RootedBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTrace
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace restart bounds for the selected-root companion weights

The actual factorial lifts supply the trace inverse gap, and exact
binomial cancellation supplies its minimum mass. The restart stage
therefore has a two-warm endpoint from every initial subprobability law.
-/

namespace ContingencyTables.RootedTrace

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing TwoLiftStates
open CompanionAnnealing (scale scale_positive)
open CompanionTrace (integerConstant time minimumMass )
open BinaryContraction DegreeCompletion TraceBounds ObservableBounds
open RootedWarmStart (actual_degree)
open CompanionConcentration (pairs_ne_nil square_width_one_le)

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma actual_dual_degree (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) :
    DegreePositive (RootedFactorialApplication.g A R ((j:ℝ)/scale A)) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length ∧
      AdditionProperty (RootedFactorialApplication.g A R ((j:ℝ)/scale A)) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length := by
  have hg := RootedFactorialApplication.second_properties A R ((j:ℝ)/scale A)
    (div_nonneg (Nat.cast_nonneg j) (scale_positive A).le)
  simpa only [PairedLabels.length] using hg

private lemma actual_plain_agreement (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (S : Set (Labels A×Bool)) (hS : PlainState pairs S) :
    weight A R j S=RootedFactorialApplication.g A R ((j:ℝ)/scale A) S := by
  exact (plain_lifts_agree (labelCell A) (RootedCountIdentification.h A R ((j:ℝ)/scale A)) S hS).symm

private lemma actual_lift_comparison (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (S : Set (Labels A×Bool)) (hS : ChainState pairs S) :
    weight A R j S≤(A.W:ℝ)^2*RootedFactorialApplication.g A R ((j:ℝ)/scale A) S := by
  apply firstLift_le_square_secondLift (labelCell A) (RootedCountIdentification.h A R ((j:ℝ)/scale A)) S hS A.W
    (by have hW := A.hW; omega)
  · intro s
    rw [label_width]
    exact A.hsmall _ _ s.property
  · exact (RootedCountIdentification.h_positive A R _ _).le

private lemma omission_instance {X : Type*} [Fintype X]
    (d e : DecidableEq X) (f : Set X → ℝ) (k : ℕ)
    (h : @OmissionProperty X _ d f k) : @OmissionProperty X _ e f k := by
  cases Subsingleton.elim d e
  exact h

private lemma addition_instance {X : Type*} [Fintype X]
    (d e : DecidableEq X) (f : Set X → ℝ) (k : ℕ)
    (h : @AdditionProperty X _ d f k) : @AdditionProperty X _ e f k := by
  cases Subsingleton.elim d e
  exact h

private lemma trace_poincare_raw (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : GoodMultipliers pairs (weight A R j) w)
    (H : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) → ℝ) :
    (trace A R j hp w hw.positive).variance H ≤
      (2*(Fintype.card (Labels A):ℝ)^2*((Fintype.card (Labels A):ℝ)*
        (1+8*(Fintype.card (Labels A):ℝ)*((A.W:ℝ)^2)^2)))*
        (trace A R j hp w hw.positive).energy H := by
  let d : DecidableEq (Labels A×Bool) := inferInstance
  have hsigf := omission_instance (inferInstance : DecidableEq (Labels A×Bool)) d
    (weight A R j) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length (actual_degree A R j).2
  have hsigg := addition_instance (inferInstance : DecidableEq (Labels A×Bool)) d
    (RootedFactorialApplication.g A R ((j:ℝ)/scale A)) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length
    (actual_dual_degree A R j).2
  have hh := @omission_trace_poincare (Labels A×Bool) inferInstance d
    pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover w (weight A R j) (RootedFactorialApplication.g A R ((j:ℝ)/scale A)) hw.positive
    (actual_degree A R j).1 (actual_dual_degree A R j).1
    hsigf hsigg
    ((A.W:ℝ)^2) (sq_nonneg _) hw.lower
    (actual_plain_agreement A R j) (actual_lift_comparison A R j) H
  change (trace A R j hp w hw.positive).variance H ≤
    (2*((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)^2)*
      (((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)*
        (1+8*((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)*((A.W:ℝ)^2)^2))*
      (trace A R j hp w hw.positive).energy H at hh
  have hcoef : (2*((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)^2)*
      (((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)*
        (1+8*((pairs : List ((Labels A×Bool)×(Labels A×Bool))).length:ℝ)*((A.W:ℝ)^2)^2))=
      2*(Fintype.card (Labels A):ℝ)^2*((Fintype.card (Labels A):ℝ)*
        (1+8*(Fintype.card (Labels A):ℝ)*((A.W:ℝ)^2)^2)) := by
    rw [PairedLabels.length]
  exact hh.trans_eq (congrArg (fun k : ℝ => k*(trace A R j hp w hw.positive).energy H) hcoef)

theorem trace_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : GoodMultipliers pairs (weight A R j) w)
    (H : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) → ℝ) :
    (trace A R j hp w hw.positive).variance H ≤
      observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)*
        (trace A R j hp w hw.positive).energy H := by
  have hpR : (1:ℝ) ≤ Fintype.card (Labels A) := by exact_mod_cast hp
  have hcoef := trace_constant_le_observable (Fintype.card (Labels A)) ((A.W:ℝ)^2)
    hpR (square_width_one_le A)
  exact (trace_poincare_raw A R j hp w hw H).trans
    (mul_le_mul_of_nonneg_right hcoef ((trace A R j hp w hw.positive).energy_nonneg H))

end ContingencyTables.RootedTrace

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTargetMixing
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root dyadic trace mixing and warm restart schedule -/

namespace ContingencyTables.RootedTargetMixing

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase RootedTargetTrace
open RootedTraceWords RootedAnnealing RootedWarmStart CompanionRationalUpdates TwoLiftStates
open DegreeCompletion ObservableBounds
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil square_width_one_le)
open CompanionTargetMixing (restartTime )
open scoped BigOperators Classical

noncomputable section

private theorem trace_exit_congr {X : Type*} [Fintype X]
    (C D : FiniteChain X) (B : X → Prop) [Nonempty (FiniteChain.Inside B)]
    (h : C=D)
    (hC : ∀ x : FiniteChain.Outside B,∃ y : FiniteChain.Inside B,0<C.P x.val y.val)
    (hD : ∀ x : FiniteChain.Outside B,∃ y : FiniteChain.Inside B,0<D.P x.val y.val) :
    C.traceChain B (C.killedChain B hC) (by intro x y; rfl)=
      D.traceChain B (D.killedChain B hD) (by intro x y; rfl) := by
  cases h
  rfl

variable {I J : Type} [Fintype I] [Fintype J]

theorem literalTrace_eq_completed (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    literalTrace A R j hp w hw=RootedTrace.trace A R j hp (fun p q => (w p q:ℝ))
      (fun p q => by exact_mod_cast hw p q) := by
  let := plainIndex_nonempty (pairs : List (Pair A)) PairedLabels.fresh PairedLabels.cover
  let F := completeDegree (weight A R j) (pairs : List (Pair A)).length
  have hF := completeDegree_positive (weight A R j) (pairs : List (Pair A)).length
    (actual_degree A R j).1
  have h := trace_exit_congr (referenceChain A R j hp w hw)
    (metropolisChain pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
      (fun p q => (w p q:ℝ)) F (fun p q => by exact_mod_cast hw p q) hF)
    (plainPredicate pairs) (referenceChain_eq_completed A R j hp w hw)
    (metropolis_plain_exit pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
      (fun p q => (w p q:ℝ)) (weight A R j)
      (fun p q => by exact_mod_cast hw p q) (weight_positive A R j))
    (metropolis_plain_exit pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
      (fun p q => (w p q:ℝ)) F (fun p q => by exact_mod_cast hw p q) hF)
  exact h

private lemma literalTrace_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (H : PlainIndex (pairs : List (Pair A)) → ℝ) :
    (literalTrace A R j hp w hw).variance H≤
      observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)*
        (literalTrace A R j hp w hw).energy H := by
  rw [literalTrace_eq_completed]
  exact RootedTrace.trace_poincare A R j hp (fun p q => (w p q:ℝ)) hgood H

theorem targetTrace_poincare_oai (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (H : PlainIndex (pairs : List (Pair A)) → ℝ) :
    (RootedTargetTrace.actualTrace A R j hp w hw).variance H≤
      (2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))*
        (RootedTargetTrace.actualTrace A R j hp w hw).energy H := by
  let := plainIndex_nonempty (pairs : List (Pair A)) PairedLabels.fresh PairedLabels.cover
  have hnonneg : 0≤observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
    unfold observableConstant
    positivity
  have hh := FiniteChainSlowdown.trace_variance_bound (referenceChain A R j hp w hw)
    (plainPredicate pairs) (sourceKilled A R j hp w hw) (by intro x y; rfl)
    (slowdown A) (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2
    (slowdown_bounds A hp).1
    (observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)) hnonneg H
    (literalTrace_poincare A R j hp w hw hgood H)
  exact hh

end
end ContingencyTables.RootedTargetMixing

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.RootedTargetMixing.targetTrace_poincare_oai := @OAI.ContingencyTables.RootedTargetMixing.targetTrace_poincare_oai
