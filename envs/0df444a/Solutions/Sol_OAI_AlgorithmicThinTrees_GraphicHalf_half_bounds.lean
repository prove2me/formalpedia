-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:58:39.781983+00:00
-- url     : https://prove2.me/submissions/b096580f-f26d-4d12-9be6-ccbda9a02de4

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT009
import Theorems.Thm_OAI_CurrentKS_RationalFace_normalizedRun_spec

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Pivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

section TrivialStar

variable [StarRing K] [TrivialStar K]

omit [Fintype n] [DecidableEq n] in
theorem pivot_schur_formula {a : K} (ha : a ≠ 0)
    (b : n → K) (D : Matrix n n K) :
    D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
      (pivotRow b) = pivotSchur a b D := by
  ext i j
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, pivotSchur]
  ring

omit [DecidableEq n] [StarRing K] [TrivialStar K] in
theorem pivot_lift_cancel {a : K} (ha : a ≠ 0) (b y : n → K) :
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) +
      ((scalarPivot a)⁻¹ * (pivotRow b)) *ᵥ y = 0 := by
  ext u
  cases u
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] in
theorem pivotWitnessLift_quadratic {a : K} (ha : a ≠ 0)
    (b y : n → K) (D : Matrix n n K) :
    pivotWitnessLift a b y ⬝ᵥ (pivotBlock a b D *ᵥ pivotWitnessLift a b y) =
      y ⬝ᵥ (pivotSchur a b D *ᵥ y) := by
  let := scalarPivotInvertible ha
  have hA : (scalarPivot a).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [scalarPivot]
  have h := Matrix.schur_complement_eq₁₁
    (pivotRow b) D
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) y hA
  rw [pivot_lift_cancel ha, pivot_schur_formula ha] at h
  have hblock : Matrix.fromBlocks (scalarPivot a) (pivotRow b) (pivotRow b)ᴴ D =
      pivotBlock a b D := by
    ext i j
    cases i <;> cases j <;> simp [pivotBlock, pivotRow, Matrix.fromBlocks]
  rw [hblock] at h
  simpa only [← Matrix.dotProduct_mulVec, star_trivial, Matrix.zero_mulVec,
    zero_dotProduct, zero_add, pivotWitnessLift] using h

end TrivialStar

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RationalElimination
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

theorem schurTail_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (schurTail M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [schurTail]
  rw [hM.apply i.succ j.succ, hM.apply 0 j.succ, hM.apply 0 i.succ]
  rw [mul_comm (M 0 j.succ) (M 0 i.succ)]

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

theorem quadratic_submatrix_equiv {n m K : Type*} [Fintype n] [Fintype m]
    [CommSemiring K] (M : Matrix n n K) (x : n → K) (e : m ≃ n) :
    (x ∘ e) ⬝ᵥ (M.submatrix e e *ᵥ (x ∘ e)) = x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.submatrix_mulVec_equiv]
  have hc : (x ∘ e) ∘ e.symm = x := by funext i; simp
  rw [hc]
  exact comp_equiv_dotProduct_comp_equiv x (M *ᵥ x) e

theorem fin_pivotBlock {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : M.IsSymm) :
    M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n) =
      pivotBlock (M 0 0) (fun i => M 0 i.succ) (KS.W17.trailingMatrix M) := by
  ext i j
  cases i with
  | inl i => cases i; cases j <;> rfl
  | inr i =>
    cases j with
    | inl j => cases j; exact hM.apply 0 i.succ
    | inr j => rfl

theorem fin_pivotSchur {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : M.IsSymm) :
    pivotSchur (M 0 0) (fun i => M 0 i.succ) (KS.W17.trailingMatrix M) =
      KS.W17.schurTail M := by
  ext i j
  simp only [pivotSchur, KS.W17.schurTail, KS.W17.trailingMatrix, hM.apply 0 i.succ]

theorem fin_pivotWitnessLift {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    KS.W17.schurWitnessLift M y ∘ pivotIndexEquiv n =
      pivotWitnessLift (M 0 0) (fun i => M 0 i.succ) y := by
  funext i
  cases i with
  | inl i =>
    cases i
    simp [pivotIndexEquiv, KS.W17.schurWitnessLift,
      pivotWitnessLift, div_eq_mul_inv, mul_comm]
  | inr i => rfl

theorem fin_schurWitnessLift_quadratic {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : M 0 0 ≠ 0) (y : Fin n → ℚ) :
    KS.W17.schurWitnessLift M y ⬝ᵥ (M *ᵥ KS.W17.schurWitnessLift M y) =
      y ⬝ᵥ (KS.W17.schurTail M *ᵥ y) := by
  rw [← quadratic_submatrix_equiv M (KS.W17.schurWitnessLift M y) (pivotIndexEquiv n),
    fin_pivotBlock M hM, fin_pivotWitnessLift M y,
    pivotWitnessLift_quadratic ha, fin_pivotSchur M hM]

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotPSD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

open Matrix

variable {n : Type*} [Fintype n]

theorem scalarPivot_posDef {a : ℝ} (ha : 0 < a) : (scalarPivot a).PosDef := by
  have heq : scalarPivot a = Matrix.diagonal (fun _ : Unit => a) := by
    ext i j
    cases i; cases j
    simp [scalarPivot]
  rw [heq]
  exact Matrix.PosDef.diagonal (fun _ => ha)

omit [Fintype n] in
theorem real_pivot_schur_formula {a : ℝ} (ha : a ≠ 0)
    (b : n → ℝ) (D : Matrix n n ℝ) :
    D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
      (pivotRow b) = pivotSchur a b D :=
  pivot_schur_formula ha b D

theorem pivotSchur_posSemidef {a : ℝ} (ha : 0 < a)
    (b : n → ℝ) (D : Matrix n n ℝ) (hM : (pivotBlock a b D).PosSemidef) :
    (pivotSchur a b D).PosSemidef := by
  let _ := scalarPivotInvertible (ne_of_gt ha)
  have hM' : (Matrix.fromBlocks (scalarPivot a)
      (pivotRow b)
      (pivotRow b)ᴴ D).PosSemidef := by
    exact hM
  have h := (Matrix.PosDef.fromBlocks₁₁
    (pivotRow b) D (scalarPivot_posDef ha)).mp hM'
  exact real_pivot_schur_formula (ne_of_gt ha) b D ▸ h

omit [Fintype n] in
theorem rat_pivotSchur_cast (a : ℚ) (b : n → ℚ) (D : Matrix n n ℚ) :
    (pivotSchur a b D).map (fun q : ℚ => (q : ℝ)) =
      pivotSchur (a : ℝ) (fun i => (b i : ℝ)) (D.map (fun q : ℚ => (q : ℝ))) := by
  ext i j
  simp [pivotSchur]

omit [Fintype n] in
theorem rat_pivotBlock_cast (a : ℚ) (b : n → ℚ) (D : Matrix n n ℚ) :
    (pivotBlock a b D).map (fun q : ℚ => (q : ℝ)) =
      pivotBlock (a : ℝ) (fun i => (b i : ℝ)) (D.map (fun q : ℚ => (q : ℝ))) := by
  ext i j
  cases i <;> cases j <;> rfl

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivotPSD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

theorem rational_isSymm_of_cast_posSemidef {n : Type*} [Fintype n]
    {M : Matrix n n ℚ} (hM : (M.map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    M.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  apply Rat.cast_injective (α := ℝ)
  simpa using hM.isHermitian.apply i j

theorem fin_schurTail_posSemidef {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : (M.map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    ((KS.W17.schurTail M).map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  by_cases hz : M 0 0 = 0
  · have hs : KS.W17.schurTail M = KS.W17.trailingMatrix M := by
      ext i j
      simp [KS.W17.schurTail, KS.W17.trailingMatrix, hz]
    rw [hs]
    exact hM.submatrix Fin.succ
  · have hsym := rational_isSymm_of_cast_posSemidef hM
    have ha0 : 0 ≤ M 0 0 := by
      have h := hM.diag_nonneg (i := (0 : Fin (n + 1)))
      simp only [Matrix.map_apply] at h
      exact_mod_cast h
    have ha : (0 : ℝ) < (M 0 0 : ℝ) := by
      exact_mod_cast (lt_of_le_of_ne ha0 (Ne.symm hz))
    have hsub := hM.submatrix (pivotIndexEquiv n)
    change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
      (fun q : ℚ => (q : ℝ))).PosSemidef at hsub
    rw [fin_pivotBlock M hsym, rat_pivotBlock_cast] at hsub
    have h := pivotSchur_posSemidef ha _ _ hsub
    rw [← rat_pivotSchur_cast, fin_pivotSchur M hsym] at h
    exact h

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_OperatorNorm
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma operatorNorm_eq_matrix (A : H d) : operatorNorm A = ‖(A : Mat d)‖ := rfl

lemma scalarOne_eq_algebraMap (r : ℝ) : ((r • (one : H d) : H d) : Mat d) = algebraMap ℝ (Mat d) r := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

lemma le_operatorNorm_smul_one (A : H d) : A ≤ operatorNorm A • one := by
  let : CStarAlgebra (Mat d) := {}
  change (A : Mat d) ≤ ((operatorNorm A • one : H d) : Mat d)
  rw [scalarOne_eq_algebraMap,operatorNorm_eq_matrix]
  exact A.property.isSelfAdjoint.le_algebraMap_norm_self

lemma operatorNorm_le_of_psd_le {A : H d} (hA : A ∈ psdCone d) {r : ℝ} (hr : 0 ≤ r)
    (hhi : A ≤ r • (one : H d)) : operatorNorm A ≤ r := by
  let : CStarAlgebra (Mat d) := {}
  apply (CStarAlgebra.norm_le_iff_le_algebraMap (A : Mat d) hr hA.nonneg).mpr
  change (A : Mat d) ≤ ((r • one : H d) : Mat d) at hhi
  rwa [scalarOne_eq_algebraMap] at hhi

end

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTrace
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open scoped BigOperators ComplexOrder

variable {d : ℕ}

theorem traceSign_mem (A : Matrix (Fin d) (Fin d) ℂ) :
    traceSign A = -1 ∨ traceSign A = 1 := by
  unfold traceSign
  split_ifs <;> simp

theorem nonzero_eigenvalues_card_le (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ A.rank := by
  classical
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  have hr : (Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)).rank
      ≤ A.rank := by
    rw [← h]
    simp only [Unitary.conjStarAlgAut_apply]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [Matrix.rank_diagonal] at hr
  simpa only [Function.comp_apply, ne_eq, RCLike.ofReal_eq_zero] using hr

theorem nonzero_eigenvalue_unique (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1)
    (i j : Fin d) (hi : hA.eigenvalues i ≠ 0) (hj : hA.eigenvalues j ≠ 0) :
    i = j := by
  have hcard : Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ 1 :=
    (nonzero_eigenvalues_card_le A hA).trans hrank
  have hs := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact congrArg Subtype.val (hs.elim (⟨i, hi⟩ : {i // hA.eigenvalues i ≠ 0}) ⟨j, hj⟩)

theorem eigenvalue_eq_realTrace (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1)
    (i : Fin d) (hi : hA.eigenvalues i ≠ 0) :
    hA.eigenvalues i = realTrace A := by
  classical
  unfold realTrace
  rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
  symm
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hj : hA.eigenvalues j = 0 := by
      by_contra hj
      exact hji (nonzero_eigenvalue_unique A hA hrank j i hj hi)
    simp [hj]
  · simp

theorem eigenvalue_eq_zero_or_trace (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) (i : Fin d) :
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = realTrace A := by
  by_cases hi : hA.eigenvalues i = 0
  · exact Or.inl hi
  · exact Or.inr (eigenvalue_eq_realTrace A hA hrank i hi)

theorem realTrace_eq_zero_iff (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) :
    realTrace A = 0 ↔ A = 0 := by
  constructor
  · intro ht
    apply hA.eigenvalues_eq_zero_iff.mp
    funext i
    rcases eigenvalue_eq_zero_or_trace A hA hrank i with hi | hi
    · exact hi
    · exact hi.trans ht
  · rintro rfl
    simp [realTrace]

theorem traceSign_mul_trace (A : Matrix (Fin d) (Fin d) ℂ) :
    traceSign A * realTrace A = |realTrace A| := by
  unfold traceSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem traceSign_sq (A : Matrix (Fin d) (Fin d) ℂ) :
    traceSign A * traceSign A = 1 := by
  rcases traceSign_mem A with h | h <;> rw [h] <;> norm_num

theorem traceSign_smul_posSemidef (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) :
    (traceSign A • A).PosSemidef := by
  change ((traceSign A : ℂ) • A).PosSemidef
  have hd : ((traceSign A : ℂ) • Matrix.diagonal
      ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)).PosSemidef := by
    rw [← Matrix.diagonal_smul]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    change 0 ≤ (traceSign A : ℂ) * (hA.eigenvalues i : ℂ)
    rw [← Complex.ofReal_mul, Complex.zero_le_real]
    rcases eigenvalue_eq_zero_or_trace A hA hrank i with hi | hi
    · simp [hi]
    · rw [hi, traceSign_mul_trace]
      exact abs_nonneg _
  have hp := hd.mul_mul_conjTranspose_same (↑hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have he := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at he
  simpa only [Matrix.smul_mul, Matrix.mul_smul, ← he] using hp

theorem realTrace_smul (r : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    realTrace (r • A) = r * realTrace A := by
  simp [realTrace, Matrix.trace, Matrix.diag, Finset.mul_sum]

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixRealSmul
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open Matrix Hermitian State
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {d N : ℕ}
lemma matrix_real_smul_zero (r : ℝ) : r • (0 : Mat d) = 0 := by
  exact smul_zero r
lemma matrix_real_smul_sum (r : ℝ) (f : Fin N → Mat d) :
    r • (∑ i, f i) = ∑ i, r • f i := by
  exact Finset.smul_sum
lemma matrix_real_smul_smul (r s : ℝ) (A : Mat d) :
    r • (s • A) = (r*s) • A := by
  exact smul_smul r s A
lemma opNorm_real_smul (r : ℝ) (A : Mat d) : opNorm (r • A) = |r| * opNorm A := by
  change ‖(r : ℂ) • A‖ = |r| * ‖A‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
lemma coe_S (A : Fin N → H d) (x : Coordinates N) :
    ((S A x : H d) : Mat d) = ∑ i,x i • (A i : Mat d) := by
  simp [S]
lemma coe_varianceH (A : Fin N → H d) :
    ((varianceH A : H d) : Mat d) = ∑ i,(A i : Mat d)*(A i : Mat d) := by
  simp [varianceH,sandwich,Hermitian.one]
end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Space
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.HermitianCoordinates
noncomputable section
open CurrentKS.Hermitian Matrix
open scoped BigOperators Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.HermitianCoordinates.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_rbcf019_1 : NormedSpace ℝ (H d) := inferInstance
lemma assemble_extract (A : H d) : assemble (extract A)=A := by
  apply Subtype.ext
  ext i j
  have hh := Matrix.IsHermitian.apply A.property i j
  have hd := Matrix.IsHermitian.apply A.property i i
  rcases lt_trichotomy i j with hij | hij | hji
  · apply Complex.ext <;>
      simp [assemble,extract,encode,decode,hij,hij.le,not_le.mpr hij]
  · subst j
    apply Complex.ext
    · simp [assemble,extract,encode,decode]
    · have him := congrArg Complex.im hd
      simp only [Complex.star_def,Complex.conj_im] at him
      simp [assemble,extract,encode,decode]
      linarith
  · apply Complex.ext
    · have hre := congrArg Complex.re hh
      simp only [Complex.star_def,Complex.conj_re] at hre
      simpa [assemble,extract,encode,decode,hji,hji.le,not_le.mpr hji,
        min_eq_right hji.le,max_eq_left hji.le] using hre
    · have him := congrArg Complex.im hh
      simp only [Complex.star_def,Complex.conj_im] at him
      simpa [assemble,extract,encode,decode,hji,hji.le,not_lt.mpr hji.le,
        not_le.mpr hji] using him

end
end CurrentKS.HermitianCoordinates

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Normalizer
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open scoped BigOperators ComplexOrder

variable {d N : ℕ}

lemma normalizer_nonneg (H : Fin N → Matrix (Fin d) (Fin d) ℂ) : 0 ≤ normalizer H :=
  Finset.sum_nonneg fun index _ => abs_nonneg (realTrace (H index))

lemma normalizedMatrix_posSemidef (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ i, (H i).IsHermitian) (hr : ∀ i, (H i).rank ≤ 1) (i : Fin N) :
    (normalizedMatrix H i).PosSemidef := by
  change ((normalizer H)⁻¹ • (traceSign (H i) • H i)).PosSemidef
  change ((((normalizer H)⁻¹ : ℝ) : ℂ) • (traceSign (H i) • H i)).PosSemidef
  exact (traceSign_smul_posSemidef (H i) (hH i) (hr i)).smul
    (by exact_mod_cast inv_nonneg.mpr (normalizer_nonneg H))

lemma normalizedMatrix_rank (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hr : ∀ i, (H i).rank ≤ 1) (i : Fin N) : (normalizedMatrix H i).rank ≤ 1 := by
  simp only [normalizedMatrix,smul_smul]
  change (((normalizer H)⁻¹*traceSign (H i) : ℝ) • H i).rank ≤ 1
  let r : ℝ := (normalizer H)⁻¹*traceSign (H i)
  change (r • H i).rank ≤ 1
  have he : r • H i = (r • (1 : Matrix (Fin d) (Fin d) ℂ))*H i := by
    rw [Matrix.smul_mul,one_mul]
  rw [he]
  exact (Matrix.rank_mul_le_right _ _).trans (hr i)

lemma normalized_trace_sum (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (hD : normalizer H ≠ 0) :
    (∑ i,realTrace (normalizedMatrix H i)) = 1 := by
  simp only [normalizedMatrix,realTrace_smul,traceSign_mul_trace,← Finset.mul_sum]
  exact inv_mul_cancel₀ hD

lemma reconstruct_matrix (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (hD : normalizer H ≠ 0) (i : Fin N) :
    normalizer H • (traceSign (H i) • normalizedMatrix H i) = H i := by
  simp only [normalizedMatrix,smul_smul]
  have hh : normalizer H * (traceSign (H i) * ((normalizer H)⁻¹ * traceSign (H i))) = 1 := by
    calc
      _ = (normalizer H*(normalizer H)⁻¹)*(traceSign (H i)*traceSign (H i)) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hD,traceSign_sq,mul_one]
  rw [hh,one_smul]

lemma normalized_square (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (i : Fin N) :
    normalizedMatrix H i*normalizedMatrix H i = ((normalizer H)⁻¹)^2 • (H i*H i) := by
  simp only [normalizedMatrix,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  congr 1
  calc
    _ = ((normalizer H)⁻¹)^2*(traceSign (H i)*traceSign (H i)) := by ring
    _ = _ := by rw [traceSign_sq,mul_one]

lemma normalizedMatrix_eq_zero_iff (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hD : normalizer H ≠ 0) (i : Fin N) : normalizedMatrix H i = 0 ↔ H i = 0 := by
  constructor
  · intro hi
    rw [← reconstruct_matrix H hD i,hi,smul_zero,smul_zero]
  · intro hi
    simp [normalizedMatrix,hi]

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_originalView
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_one _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalInput
open scoped BigOperators ComplexOrder
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates

lemma index_injective (x : Input) : Function.Injective (index x) :=
  ((List.nodup_finRange x.N).filter _).injective_get

lemma index_range (x : Input) (i : Fin x.N) : (∃ j,index x j=i) ↔ trace x i ≠ 0 := by
  change (∃ j,(indices x).get j=i) ↔ _
  rw [← List.mem_iff_get]
  simp [indices]

lemma index_trace_ne (x : Input) (j : Fin (indices x).length) : trace x (index x j) ≠ 0 :=
  (index_range x _).mp ⟨j,rfl⟩

noncomputable section

lemma trace_cast (x : Input) (i : Fin x.N) : (trace x i : ℝ)=CurrentKS.realTrace (x.matrix i) := by
  simp [trace,CurrentKS.realTrace,Matrix.trace,Matrix.diag,Input.matrix,toComplex]

lemma orientation_cast (x : Input) (i : Fin x.N) : (orientation x i : ℝ)=traceSign (x.matrix i) := by
  have hh : 0 ≤ trace x i ↔ (0:ℝ) ≤ CurrentKS.realTrace (x.matrix i) := by
    rw [←trace_cast];exact_mod_cast Iff.rfl
  simp only [orientation,traceSign,hh]
  split_ifs <;> norm_num

lemma scale_cast (x : Input) : (scale x : ℝ)=normalizer x.matrix := by
  simp [scale,normalizer,←trace_cast]

lemma coordinates_cast (x : Input) (hx : Admissible x) (i : Fin x.N) :
    (fun p => (coordinates x i p:ℝ))=HermitianCoordinates.encode ⟨x.matrix i,(hx i).1⟩ := by
  funext p
  simp only [coordinates,HermitianCoordinates.encode,Input.matrix,Matrix.map_apply,toComplex]
  split_ifs <;> rfl

lemma decode_coordinates (x : Input) (hx : Admissible x) (i : Fin x.N) :
    decode (fun p => (coordinates x i p:ℝ))=x.matrix i := by
  rw [coordinates_cast x hx i]
  exact congrArg Subtype.val (assemble_extract (⟨x.matrix i,(hx i).1⟩ : H x.d))

lemma trace_zero_iff (x : Input) (hx : Admissible x) (i : Fin x.N) :
    trace x i=0 ↔ x.matrix i=0 := by
  rw [← realTrace_eq_zero_iff (x.matrix i) (hx i).1 (hx i).2,←trace_cast]
  exact_mod_cast Iff.rfl

lemma scale_pos (x : Input) (hne : (indices x).length ≠ 0) : 0 < scale x := by
  have hl : 0 < (indices x).length := Nat.pos_of_ne_zero hne
  let j : Fin (indices x).length := ⟨0,hl⟩
  exact Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨index x j,Finset.mem_univ _,
    abs_pos.mpr (index_trace_ne x j)⟩

lemma dimension_ne (x : Input) (hx : Admissible x) (hne : (indices x).length ≠ 0) : x.d ≠ 0 := by
  intro hd
  let i := index x ⟨0,Nat.pos_of_ne_zero hne⟩
  have hz : x.matrix i=0 := by
    ext j k
    have hj := j.isLt
    omega
  exact index_trace_ne x _ ((trace_zero_iff x hx i).mpr hz)

lemma decode_normalizedCoordinates (x : Input) (hx : Admissible x) (j : Fin (indices x).length) :
    decode (fun p => (normalizedCoordinates x j p:ℝ))=normalizedMatrix x.matrix (index x j) := by
  have he : (fun p => (normalizedCoordinates x j p:ℝ))=
      (scale x:ℝ)⁻¹ • ((orientation x (index x j):ℝ) • (fun p => (coordinates x (index x j) p:ℝ))) := by
    funext p
    simp [normalizedCoordinates]
  rw [he,decode_smul,decode_smul,decode_coordinates x hx,scale_cast,orientation_cast]
  rfl

lemma normalized_input_properties (x : Input) (hx : Admissible x)
    (hne : (indices x).length ≠ 0) :
    let A := fun j => assemble (WithLp.toLp 2 fun p => (normalizedCoordinates x j p:ℝ))
    (∀ j,A j∈psdCone x.d) ∧ (∀ j,A j≠0) ∧
    (∀ j,(A j:Mat x.d).rank ≤ 1) ∧ (∑ j,Hermitian.realTrace (A j))=1 := by
  let A := fun j => assemble (WithLp.toLp 2 fun p => (normalizedCoordinates x j p:ℝ))
  have hA (j) : (A j:Mat x.d)=normalizedMatrix x.matrix (index x j) :=
    decode_normalizedCoordinates x hx j
  have hD : normalizer x.matrix ≠ 0 := by
    rw [←scale_cast]
    exact_mod_cast (scale_pos x hne).ne'
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    change (A j:Mat x.d).PosSemidef
    rw [hA]
    exact normalizedMatrix_posSemidef x.matrix (fun i => (hx i).1) (fun i => (hx i).2) _
  · intro j hj
    change A j=0 at hj
    have hz : normalizedMatrix x.matrix (index x j)=0 := by rw [←hA j,hj];rfl
    exact index_trace_ne x j ((trace_zero_iff x hx _).mpr
      ((normalizedMatrix_eq_zero_iff x.matrix hD _).mp hz))
  · intro j
    rw [hA]
    exact normalizedMatrix_rank x.matrix (fun i => (hx i).2) _
  · change (∑ j,Hermitian.realTrace (A j))=1
    have he : (∑ j,CurrentKS.realTrace (normalizedMatrix x.matrix (index x j)))=
        ∑ i,CurrentKS.realTrace (normalizedMatrix x.matrix i) := by
      apply Fintype.sum_of_injective (index x) (index_injective x)
      · intro i hi
        have hz : trace x i=0 := by
          by_contra hz
          exact hi ((index_range x i).mpr hz)
        have hm := (trace_zero_iff x hx i).mp hz
        rw [(normalizedMatrix_eq_zero_iff x.matrix hD i).mpr hm]
        simp [CurrentKS.realTrace]
      · intro j;rfl
    have ht := normalized_trace_sum x.matrix hD
    rw [←he] at ht
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro j _
    change CurrentKS.realTrace (A j:Mat x.d)=_
    rw [hA]

end
end CurrentKS.RationalInput

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Lookup
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N n : ℕ}

lemma lookup_some {e : Fin n → Fin N} {i : Fin N} {j : Fin n}
    (h : lookup e i=some j) : e j=i := by
  have hh := List.find?_some h
  exact of_decide_eq_true hh

lemma lookup_none_iff (e : Fin n → Fin N) (i : Fin N) :
    lookup e i=none ↔ ∀ j,e j≠i := by
  simp [lookup,List.find?_eq_none]

lemma lookup_self {e : Fin n → Fin N} (he : Function.Injective e) (j : Fin n) :
    lookup e (e j)=some j := by
  cases hh : lookup e (e j) with
  | none => exact False.elim ((lookup_none_iff e (e j)).mp hh j rfl)
  | some k =>
    have hk := he (lookup_some hh)
    cases hk
    rfl

lemma extend_at {β : Type*} {e : Fin n → Fin N} (he : Function.Injective e)
    (base : Fin N → β) (y : Fin n → β) (j : Fin n) : extend e base y (e j)=y j := by
  simp [extend,lookup_self he]

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CovarianceE
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open scoped BigOperators
open Matrix

variable {m : ℕ}

attribute [local instance] OAI.CurrentKS.Covariance.instInnerProductSpaceReal_solutions
local instance instLocallyConvexSpaceRealMat_rbcf019_1 : LocallyConvexSpace ℝ (Mat m) :=
  inferInstanceAs (LocallyConvexSpace ℝ (Fin m → Fin m → ℝ))
theorem entry_sq_le_diag_mul {A : Mat m} (hA : A.PosSemidef) (i j : Fin m) :
    (A i j) ^ 2 ≤ A i i * A j j := by
  have hsym : A j i = A i j := by simpa using hA.isHermitian.apply i j
  have hq : ∀ t : ℝ, 0 ≤ A i i * (t * t) + (2 * A i j) * t + A j j := by
    intro t
    have hp := hA.2 (Finsupp.single i t + Finsupp.single j 1)
    simp [Finsupp.sum_add_index, mul_add, add_mul, hsym] at hp
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

theorem entry_eq_zero_of_diag_eq_zero {A : Mat m} (hA : A.PosSemidef)
    (i j : Fin m) (hi : A i i = 0) : A i j = 0 := by
  have h := entry_sq_le_diag_mul hA i j
  rw [hi, zero_mul] at h
  nlinarith [sq_nonneg (A i j)]

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Signing
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_originalView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalInput
open CurrentKS.RationalFace CurrentKS.RationalSDP
open scoped BigOperators

lemma orientation_abs (x : Input) (i : Fin x.N) : |orientation x i|=1 := by
  unfold orientation
  split_ifs <;> norm_num

end CurrentKS.RationalInput

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Outside
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_originalView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalInput
noncomputable section
open Matrix CurrentKS.Hermitian CurrentKS.State CurrentKS.Difference
open CurrentKS.RationalFace CurrentKS.RationalSDP
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

lemma zero_outside (x : Input) (hx : Admissible x) (i : Fin x.N)
    (hi : i∉Set.range (index x)) : x.matrix i=0 := by
  apply (trace_zero_iff x hx i).mp
  by_contra hn
  exact hi ((index_range x i).mpr hn)

lemma trimmed_square_sum (x : Input) (hx : Admissible x) :
    (∑ j,x.matrix (index x j)*x.matrix (index x j))=∑ i,x.matrix i*x.matrix i := by
  apply Fintype.sum_of_injective (index x) (index_injective x)
  · intro i hi
    rw [zero_outside x hx i hi,mul_zero]
  · intro j;rfl

lemma lifted_signs_abs (x : Input) (s : Fin (indices x).length → ℚ) (hs : ∀ j,|s j|=1) :
    ∀ i,|orientation x i*extend (index x) (fun _=>1) s i|=1 := by
  intro i
  rw [abs_mul,orientation_abs,one_mul]
  unfold extend
  cases lookup (index x) i with
  | none => norm_num
  | some j => exact hs j

lemma sign_bits_value (x : Input) (s : Fin (indices x).length → ℚ) (hs : ∀ j,|s j|=1) (i : Fin x.N) :
    signValue ((List.ofFn fun i => decide (orientation x i*extend (index x) (fun _=>1) s i=1)).getD i.val false)=
      ((orientation x i*extend (index x) (fun _=>1) s i:ℚ):ℝ) := by
  have ha := (abs_eq (show (0:ℚ)≤1 by norm_num)).mp (lifted_signs_abs x s hs i)
  rcases ha with h|h
  · norm_num [List.getD,signValue,h]
  · norm_num [List.getD,signValue,h]

theorem signing_good (x : Input) (hx : Admissible x) : GoodOutput x (signing x) := by
  by_cases hn : (indices x).length=0
  · have hz : ∀ i,x.matrix i=0 := by
      intro i
      apply zero_outside x hx i
      rintro ⟨j,_⟩
      have hj := j.isLt
      omega
    constructor
    · simp [signing,hn]
    · have hsum : signedSum x (signing x)=0 := by simp only [signedSum,hz,matrix_real_smul_zero,Finset.sum_const_zero]
      have hvar : variance x=0 := by simp [variance,hz]
      rw [hsum,hvar]
      simp only [opNorm,map_zero,norm_zero,Real.sqrt_zero,mul_zero,le_refl]
  · let : NeZero (indices x).length := ⟨hn⟩
    let : NeZero x.d := ⟨dimension_ne x hx hn⟩
    let coords := normalizedCoordinates x
    let A := rationalAtoms coords
    let s := normalizedRun coords
    have hp := normalized_input_properties x hx hn
    have hh := normalizedRun_spec coords hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hs : ∀ j,|s j|=1 := hh.1
    have hmat (j) : (A j:Mat x.d)=normalizedMatrix x.matrix (index x j) :=
      decode_normalizedCoordinates x hx j
    have hD : 0 < normalizer x.matrix := by
      rw [←scale_cast]
      exact_mod_cast scale_pos x hn
    have hout : signing x=List.ofFn (fun i => decide (orientation x i*extend (index x) (fun _=>1) s i=1)) := by
      simp only [signing,ite_eq_right hn]
      rfl
    have hsign (i) : signValue ((signing x).getD i.val false)=
        ((orientation x i*extend (index x) (fun _=>1) s i:ℚ):ℝ) := by
      rw [hout]
      exact sign_bits_value x s hs i
    have hsum : signedSum x (signing x)=normalizer x.matrix • (S A (pointCast s):H x.d).val := by
      unfold signedSum
      simp only [hsign,Rat.cast_mul,orientation_cast]
      have he : (∑ j,(traceSign (x.matrix (index x j))*(s j:ℝ)) • x.matrix (index x j))=
          ∑ i,(traceSign (x.matrix i)*((extend (index x) (fun _=>1) s i:ℚ):ℝ)) • x.matrix i := by
        apply Fintype.sum_of_injective (index x) (index_injective x)
        · intro i hi
          rw [zero_outside x hx i hi,matrix_real_smul_zero]
        · intro j
          rw [extend_at (index_injective x)]
      rw [←he,coe_S,matrix_real_smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hmat]
      simp only [normalizedMatrix,pointCast,matrix_real_smul_smul]
      congr 1
      field_simp [hD.ne']
    have hv : operatorNorm (varianceH A)=(normalizer x.matrix)⁻¹^2*opNorm (variance x) := by
      change opNorm ((varianceH A:H x.d):Mat x.d)=_
      rw [coe_varianceH]
      simp only [hmat,normalized_square]
      rw [←matrix_real_smul_sum,trimmed_square_sum x hx,opNorm_real_smul,abs_of_nonneg (sq_nonneg _)]
      rfl
    have hroot : Real.sqrt (operatorNorm (varianceH A))=
        (normalizer x.matrix)⁻¹*Real.sqrt (opNorm (variance x)) := by
      rw [hv,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos (inv_pos.mpr hD)]
    refine ⟨by rw [hout,List.length_ofFn],?_⟩
    rw [hsum,opNorm_real_smul,abs_of_pos hD]
    have hb := mul_le_mul_of_nonneg_left hh.2 hD.le
    rw [hroot] at hb
    change normalizer x.matrix*operatorNorm (S A (pointCast s)) ≤ _
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | field_simp [hD.ne']
end
end CurrentKS.RationalInput

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ShortcutDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

lemma eval_incidence (x : Fin n → ℝ) (e : Fin m) :
    (∑v, x v*G.incidence e v)=x (G.left e)-x (G.right e) := by
  simp [incidence,point,Pi.sub_apply,mul_sub,sum_sub_distrib,Pi.single_apply,mul_ite]

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Matrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open Matrix
namespace StrongThinTree
section Resistance
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma rankOne_quadratic (b x : ι → ℝ) :
    x ⬝ᵥ (vecMulVec b b *ᵥ x) = (b ⬝ᵥ x) ^ 2 := by
  rw [vecMulVec_mulVec]
  simp [dotProduct, Finset.mul_sum, pow_two, mul_comm, mul_left_comm]

end Resistance
end StrongThinTree

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_GraphMatrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
lemma qform_add (X Y : Matrix V V ℝ) (v : V → ℝ) : qform (X+Y) v=qform X v+qform Y v := by
  simp [qform,add_mulVec,dotProduct_add]
omit [DecidableEq V] in
lemma qform_sub (X Y : Matrix V V ℝ) (v : V → ℝ) : qform (X-Y) v=qform X v-qform Y v := by
  simp [qform,sub_mulVec,dotProduct_sub]
omit [DecidableEq V] in
lemma qform_mono {X Y : Matrix V V ℝ} (h : X ≤ Y) (v : V → ℝ) : qform X v ≤ qform Y v := by
  have hh := qform_nonneg (Matrix.le_iff.mp h) v
  rw [qform_sub] at hh
  linarith

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_qform (F : Finset (Fin m)) (v : Fin n → ℝ) :
    qform (G.laplacian F) v=∑e ∈ F, (v (G.left e)-v (G.right e))^2 := by
  simp only [laplacian,qform,sum_mulVec,dotProduct_sum,rankOne_quadratic]
  apply sum_congr rfl
  intro e _
  rw [dotProduct_comm]
  congr 1
  exact G.eval_incidence v e

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Representation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uE uT uI uE2 uE3 uV uE4 uV2 uW

section

open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {n m : ℕ} (G : MultiGraph n m)

lemma edgeSpan_le_zeroSum (T : Finset (Fin m)) : G.edgeSpan T ≤ zeroSumSpace n :=
  (Packing.span_le_iff G.incidence).mpr (fun e _he => G.incidence_zeroSum e)

lemma connected_span_zeroSum {T : Finset (Fin m)} (hn : 0 < n) (hT : G.Connected T) :
    G.edgeSpan T = zeroSumSpace n := by
  apply le_antisymm (G.edgeSpan_le_zeroSum T)
  intro x hx
  have hx0 := (mem_zeroSumSpace x).mp hx
  let u₀ : Fin n := ⟨0, hn⟩
  have hs : ∑ u, x u • (point u - point u₀) ∈ G.edgeSpan T := by
    apply Submodule.sum_mem
    intro u hu
    exact Submodule.smul_mem _ _ ((G.connected_iff_same T).mp hT u u₀)
  have heq : ∑ u, x u • (point u - point u₀) = x := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hx0, zero_smul, sub_zero]
    ext u
    simp [point, Pi.single_apply, Finset.sum_apply, mul_ite]
  rwa [heq] at hs

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_Squares
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational squares. -/

section

namespace AlgorithmicThinTrees.RationalGram
open CurrentKS.RationalBits

lemma base4Squares_sum (k n : ℕ) (hn : n < 4^k) :
    ((base4Squares k n).map (·^2)).sum = n := by
  induction k generalizing n with
  | zero =>
    have hz : n=0 := by simpa using hn
    subst n
    rfl
  | succ k ih =>
    have hn' : n/4 < 4^k := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
      simpa only [pow_succ] using hn)
    have hsum : ((base4Squares k (n/4)).map (fun a => (2*a)^2)).sum =
        4*((base4Squares k (n/4)).map (fun a => a^2)).sum := by
      rw [← List.sum_map_mul_left]
      congr 2
      funext a
      ring
    simp only [base4Squares,List.map_append,List.map_replicate,one_pow,
      List.map_map,Function.comp_def,List.sum_append,List.sum_replicate,nsmul_eq_mul,mul_one]
    rw [hsum,ih _ hn']
    exact Nat.mod_add_div n 4

lemma scalarFactors_sum (q : ℚ) (hq : 0 ≤ q) :
    ((scalarFactors q).map (·^2)).sum=q := by
  let n := q.num.natAbs*q.den
  have hn : n < 4^n.size := (Nat.lt_size_self n).trans_le
    (Nat.pow_le_pow_left (by decide : 2≤4) _)
  have hh := base4Squares_sum n.size n hn
  have hcast : ((base4Squares n.size n).map (fun a : ℕ => (a:ℚ)^2)).sum=(n:ℚ) := by
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_pow] using
      congrArg (fun a : ℕ => (a:ℚ)) hh
  have hden : (q.den:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hnum : (q.num.natAbs:ℚ)=(q.num:ℚ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun a : ℤ => (a:ℚ)) (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq))
  simp only [scalarFactors,List.map_map,Function.comp_def,div_pow]
  change ((base4Squares n.size n).map (fun a : ℕ => (a:ℚ)^2/(q.den:ℚ)^2)).sum=q
  simp_rw [div_eq_mul_inv]
  rw [List.sum_map_mul_right,hcast,←div_eq_mul_inv]
  dsimp [n]
  push_cast
  rw [hnum]
  rw [show (q.num:ℚ)*(q.den:ℚ)/(q.den:ℚ)^2 = (q.num:ℚ)/q.den by field_simp]
  exact Rat.num_div_den q

end AlgorithmicThinTrees.RationalGram
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_Gram
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational gram. -/

section

namespace AlgorithmicThinTrees.RationalGram
open Matrix CurrentKS.RationalBits
variable {n : ℕ}

lemma sum_scaled_outer (L : List ℚ) (u : Fin n → ℚ) (i j : Fin n) :
    (L.map (fun a => (a*u i)*(a*u j))).sum =
      (L.map (fun a => a^2)).sum*(u i*u j) := by
  rw [← List.sum_map_mul_right]
  congr 2
  funext a
  ring

lemma zero_pivot_row {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosSemidef) (i j : Fin n)
    (hi : A i i=0) : A i j=0 := by
  have h := CurrentKS.Covariance.entry_eq_zero_of_diag_eq_zero hA i j (by simp [hi])
  simpa only [Matrix.map_apply,Rat.cast_eq_zero] using h

lemma factorColumns_correct : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
    (A.map (fun q : ℚ => (q:ℝ))).PosSemidef → ∀ i j,
      ((factorColumns n A).map (fun v => v i*v j)).sum=A i j := by
  intro n
  induction n with
  | zero => intro A hA i;exact Fin.elim0 i
  | succ n ih =>
    intro A hA i j
    have hsym := KS.W07.rational_isSymm_of_cast_posSemidef hA
    have hdiag : 0 ≤ A 0 0 := by
      have hh := hA.diag_nonneg (i:=0)
      simp only [Matrix.map_apply] at hh
      exact_mod_cast hh
    have hp := scalarFactors_sum (A 0 0)⁻¹ (inv_nonneg.mpr hdiag)
    have ht := ih (KS.W17.schurTail A) (KS.W07.fin_schurTail_posSemidef A hA)
    simp only [factorColumns,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    rw [sum_scaled_outer (u := fun i => A i 0),hp]
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero,mul_zero,List.map_const',List.sum_replicate,nsmul_zero,add_zero]
        by_cases hz : A 0 0=0
        · simp [hz]
        · field_simp
      · simp only [Fin.cons_zero,zero_mul,List.map_const',List.sum_replicate,nsmul_zero,add_zero]
        by_cases hz : A 0 0=0
        · simp [hz,zero_pivot_row hA 0 j.succ hz]
        · rw [show A j.succ 0=A 0 j.succ from hsym.apply _ _]
          field_simp
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero,mul_zero,List.map_const',List.sum_replicate,nsmul_zero,add_zero]
        by_cases hz : A 0 0=0
        · have hrow := zero_pivot_row hA 0 i.succ hz
          rw [←hsym.apply 0 i.succ] at hrow
          simp [hz,hrow]
        · field_simp
      · simp only [Fin.cons_succ]
        rw [ht,KS.W17.schurTail,show A j.succ 0=A 0 j.succ from hsym.apply _ _]
        ring

lemma factorMatrix_correct (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    factorMatrix A*(factorMatrix A)ᵀ=A := by
  ext i j
  rw [Matrix.mul_apply]
  change (∑k, (factorColumns n A).get k i*(factorColumns n A).get k j)=A i j
  rw [← List.sum_ofFn]
  have hh : (List.ofFn fun k => (factorColumns n A).get k i*(factorColumns n A).get k j) =
      (factorColumns n A).map (fun v => v i*v j) := by
    change List.ofFn ((fun (v : Fin n → ℚ) => v i*v j) ∘ (factorColumns n A).get) = _
    rw [← List.map_ofFn,List.ofFn_get]
  rw [hh]
  exact factorColumns_correct n A hA i j

end AlgorithmicThinTrees.RationalGram
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CenteredMatrices
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered matrices. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma ones_dot (x : Fin n → ℝ) : ones n ⬝ᵥ x=∑i, x i := by
  simp [ones,dotProduct]

lemma constantProjection_mulVec (x : Fin n → ℝ) :
    constantProjection n *ᵥ x=((∑i, x i)/(n:ℝ)) • ones n := by
  ext j
  simp [constantProjection,mulVec,dotProduct,Matrix.smul_apply,vecMulVec,ones,div_eq_mul_inv,Finset.sum_mul,mul_comm]

lemma qform_constantProjection (x : Fin n → ℝ) :
    qform (constantProjection n) x=(∑i, x i)^2/(n:ℝ) := by
  rw [qform,constantProjection_mulVec,dotProduct_smul,dotProduct_comm x,ones_dot]
  simp only [smul_eq_mul]
  ring

lemma centering_mulVec (x : Fin n → ℝ) :
    centering n *ᵥ x=x-((∑i, x i)/(n:ℝ)) • ones n := by
  rw [centering,sub_mulVec,one_mulVec,constantProjection_mulVec]

lemma centering_mulVec_of_sum_zero {x : Fin n → ℝ} (hx : ∑i, x i=0) :
    centering n *ᵥ x=x := by
  simp only [centering_mulVec,hx,zero_div,zero_smul,sub_zero]

lemma centering_mulVec_sum (hn : 0 < n) (x : Fin n → ℝ) :
    ∑i, (centering n *ᵥ x) i=0 := by
  rw [centering_mulVec]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,ones,sum_sub_distrib,mul_one,
    sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

lemma qform_centered (D : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform (centered D) x=qform D (centering n *ᵥ x) := by
  unfold centered qform
  rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec,←mulVec_transpose,centering_symmetric]

lemma laplacian_zeroSum_pos (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ)
    (x : Fin n → ℝ) (hx : (∑i, x i)=0) (hxne : x ≠ 0) :
    0 < qform (G.laplacian univ) x := by
  have hnonneg := qform_nonneg (G.laplacian_psd univ) x
  by_contra hpos
  have hzero : qform (G.laplacian univ) x=0 := le_antisymm (not_lt.mp hpos) hnonneg
  have hedge (e : Fin m) : x (G.left e)-x (G.right e)=0 := by
    rw [G.laplacian_qform] at hzero
    have he := (single_le_sum (fun i _ => sq_nonneg (x (G.left i)-x (G.right i))) (mem_univ e))
    rw [hzero] at he
    exact sq_eq_zero_iff.mp (le_antisymm he (sq_nonneg _))
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => x ⬝ᵥ v
      map_add' := fun v w => dotProduct_add x v w
      map_smul' := fun c v => dotProduct_smul c x v }
  have hf : G.edgeSpan univ ≤ f.ker := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e _
    change (∑v, x v*G.incidence e v)=0
    rw [G.eval_incidence]
    exact hedge e
  have hxx : x ⬝ᵥ x=0 := hf (by rw [G.connected_span_zeroSum hn hc]; exact (mem_zeroSumSpace x).mpr hx)
  exact hxne (dotProduct_self_eq_zero.mp hxx)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_CenteredDomain
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma mul_constant_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*constantProjection n=0 := by
  simp only [constantProjection,mul_smul_comm,mul_vecMulVec,hD0,zero_vecMulVec,smul_zero]

lemma constant_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : constantProjection n*D=0 := by
  have hh := congrArg transpose (mul_constant_of_ones hD0)
  simpa only [transpose_mul,constantProjection_symmetric,
    (isHermitian_iff_isSymm.mp hD).eq,transpose_zero] using hh

lemma mul_centering_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*centering n=D := by
  rw [centering,mul_sub,mul_one,mul_constant_of_ones hD0,sub_zero]

lemma centering_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centering n*D=D := by
  rw [centering,sub_mul,one_mul,constant_mul_of_ones hD hD0,sub_zero]

lemma centered_eq {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centered D=D := by
  rw [centered,centering_mul_of_ones hD hD0,mul_centering_of_ones hD0]

lemma centeredPositive_psd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) : D.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg hD.1
  intro x
  change 0 ≤ qform D x
  rw [←centered_eq hD.1 hD.2.1,qform_centered]
  by_cases hx : centering n *ᵥ x=0
  · simp [hx,qform]
  · exact (hD.2.2 _ (centering_mulVec_sum hn x) hx).le

lemma regularize_pd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) : (regularize D).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos (hD.1.add constantProjection_psd.isHermitian)
  intro x hx
  change 0 < qform (regularize D) x
  rw [regularize,qform_add]
  by_cases hp : centering n *ᵥ x=0
  · have hs : (∑i, x i) ≠ 0 := by
      intro hs
      rw [centering_mulVec_of_sum_zero hs] at hp
      exact hx hp
    have hq : 0 < qform (constantProjection n) x := by
      rw [qform_constantProjection]
      exact div_pos (sq_pos_of_ne_zero hs) (Nat.cast_pos.mpr hn)
    exact add_pos_of_nonneg_of_pos (qform_nonneg (centeredPositive_psd hn hD) _) hq
  · have hq : 0 < qform D x := by
      rw [←centered_eq hD.1 hD.2.1,qform_centered]
      exact hD.2.2 _ (centering_mulVec_sum hn x) hp
    exact add_pos_of_pos_of_nonneg hq (qform_nonneg constantProjection_psd _)

lemma domain_positive (G : MultiGraph n m) (hn : 0 < n) (hG : G.Connected univ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain G) : CenteredPositive X := by
  refine ⟨hX.1,hX.2.1,?_⟩
  intro x hx hx0
  exact (laplacian_zeroSum_pos G hn hG x hx hx0).trans_le (qform_mono hX.2.2.1 x)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_Inverse
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational inverse. -/

section


namespace AlgorithmicThinTrees.RationalInverse
open Matrix Finset
variable {n : ℕ}

lemma posDef_of_cast (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosDef) : A.PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
  · exact (isHermitian_iff_isSymm.mpr (KS.W07.rational_isSymm_of_cast_posSemidef hA.posSemidef))
  · intro x hx
    have hx' : (fun i => (x i:ℝ)) ≠ 0 := by
      intro he
      apply hx
      funext i
      have hh := congrFun he i
      change (x i:ℝ)=0 at hh
      change x i=0
      exact_mod_cast hh
    have hh := hA.dotProduct_mulVec_pos hx'
    simp only [star_trivial,dotProduct,mulVec,map_apply] at hh ⊢
    exact_mod_cast hh

lemma schur_posDef (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hA : A.PosDef) : (KS.W17.schurTail A).PosDef := by
  have hs : A.IsSymm := isHermitian_iff_isSymm.mp hA.isHermitian
  apply PosDef.of_dotProduct_mulVec_pos
  · exact isHermitian_iff_isSymm.mpr (KS.W17.schurTail_isSymm A hs)
  · intro x hx
    have hlift : KS.W17.schurWitnessLift A x ≠ 0 := by
      intro h
      apply hx
      funext i
      exact congrFun h i.succ
    simpa only [star_trivial,KS.W07.fin_schurWitnessLift_quadratic A hs hA.diag_pos.ne'] using
      hA.dotProduct_mulVec_pos hlift

lemma liftSolve_correct (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) (b : Fin (n+1) → ℚ)
    (hp : A 0 0 ≠ 0) (hB : KS.W17.schurTail A*B=1) :
    A*ᵥliftSolve A B b=b := by
  let y := B*ᵥ(fun i => b i.succ-A i.succ 0*(b 0/A 0 0))
  have hy : KS.W17.schurTail A*ᵥy=(fun i => b i.succ-A i.succ 0*(b 0/A 0 0)) := by
    rw [show y=B*ᵥ(fun i => b i.succ-A i.succ 0*(b 0/A 0 0)) from rfl,
      Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]
  ext i
  rw [mulVec,dotProduct,Fin.sum_univ_succ]
  change A i 0*((b 0-(fun j => A 0 j.succ) ⬝ᵥ y)/A 0 0)+
    ∑j, A i j.succ*y j=b i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [mul_div_cancel₀ _ hp]
    simp only [dotProduct]
    ring
  · have he := congrFun hy i
    change (∑j, (A i.succ j.succ-A i.succ 0*A 0 j.succ/A 0 0)*y j)=
      b i.succ-A i.succ 0*(b 0/A 0 0) at he
    have he' : (∑j, A i.succ j.succ*y j)-
        A i.succ 0*(A 0 0)⁻¹*((fun j => A 0 j.succ) ⬝ᵥ y)=
      b i.succ-A i.succ 0*(b 0/A 0 0) := by
      have hsum : (∑j, (A i.succ j.succ-A i.succ 0*A 0 j.succ/A 0 0)*y j)=
          (∑j, A i.succ j.succ*y j)-
          A i.succ 0*(A 0 0)⁻¹*((fun j => A 0 j.succ) ⬝ᵥ y) := by
        simp only [dotProduct,mul_sum,←sum_sub_distrib]
        apply sum_congr rfl
        intro j hj
        ring
      rwa [hsum] at he
    simp only [div_eq_mul_inv]
    linear_combination he'

lemma inverse_mul_correct : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
    A.PosDef → A*inverse n A=1 := by
  intro n
  induction n with
  | zero => intro A hA;ext i;exact Fin.elim0 i
  | succ n ih =>
    intro A hA
    have hB := ih (KS.W17.schurTail A) (schur_posDef A hA)
    ext i j
    have hh := congrFun (liftSolve_correct A (inverse n (KS.W17.schurTail A))
      (Pi.single j 1) hA.diag_pos.ne' hB) i
    simpa only [inverse,Matrix.mul_apply,Matrix.mulVec,dotProduct,Pi.single_apply,
      one_apply,eq_comm] using! hh

lemma inverse_eq (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.PosDef) : inverse n A=A⁻¹ := by
  exact (inv_eq_right_inv (inverse_mul_correct n A hA)).symm

lemma inverse_eq_of_cast (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosDef) : inverse n A=A⁻¹ :=
  inverse_eq A (posDef_of_cast A hA)

end AlgorithmicThinTrees.RationalInverse
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramWhitening
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram whitening. -/

section

namespace AlgorithmicThinTrees.GramWhitening
open Matrix Finset
open scoped MatrixOrder
variable {n d m : ℕ}

lemma congruence_mono {A B : Matrix (Fin n) (Fin n) ℝ} (h : A ≤ B)
    (R : Matrix (Fin n) (Fin d) ℝ) : Rᵀ*A*R ≤ Rᵀ*B*R := by
  rw [Matrix.le_iff]
  have hh := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same R
  simpa only [conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul] using hh

lemma symmetric_of_psd {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) : Aᵀ=A :=
  (isHermitian_iff_isSymm.mp hA.isHermitian).eq

lemma projection_le_one {Q : Matrix (Fin d) (Fin d) ℝ}
    (hQ : Qᵀ=Q) (hQQ : Q*Q=Q) : Q ≤ 1 := by
  rw [Matrix.le_iff]
  have hh := posSemidef_conjTranspose_mul_self (1-Q)
  rw [conjTranspose_eq_transpose_of_trivial] at hh
  have he : (1-Q)ᵀ*(1-Q) = 1-Q := by
    rw [transpose_sub,transpose_one,hQ,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,Matrix.one_mul,Matrix.one_mul,Matrix.mul_one,hQQ]
    abel
  rwa [he] at hh

lemma normalized_covariance (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin d) ℝ) (hRR : R*Rᵀ=P⁻¹) :
    Rᵀ*P*R ≤ 1 := by
  have hPP : P⁻¹*P=1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).mp hP.isUnit)
  apply projection_le_one
  · rw [transpose_mul,transpose_mul,transpose_transpose,symmetric_of_psd hP.posSemidef]
    simp only [Matrix.mul_assoc]
  · calc
      Rᵀ*P*R*(Rᵀ*P*R) = Rᵀ*P*(R*Rᵀ)*P*R := by simp only [Matrix.mul_assoc]
      _ = Rᵀ*P*R := by rw [hRR,Matrix.mul_assoc (Rᵀ*P) P⁻¹ P,hPP,Matrix.mul_one]

lemma rectangular_norm (R : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) :
    (Rᵀ*ᵥb) ⬝ᵥ (Rᵀ*ᵥb)=b ⬝ᵥ ((R*Rᵀ)*ᵥb) := by
  rw [dotProduct_mulVec,vecMul_transpose,dotProduct_comm,←mulVec_mulVec,dotProduct_mulVec]

lemma recover (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin d) ℝ) (hRR : R*Rᵀ=P⁻¹) :
    P*R*Rᵀ=1 ∧ (P*R)*(P*R)ᵀ=P := by
  have hPP : P*P⁻¹=1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).mp hP.isUnit)
  constructor
  · rw [Matrix.mul_assoc,hRR,hPP]
  · rw [transpose_mul,symmetric_of_psd hP.posSemidef,←Matrix.mul_assoc,Matrix.mul_assoc P R Rᵀ,hRR,hPP,Matrix.one_mul]

lemma congruence_outer (R : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) :
    vecMulVec (Rᵀ*ᵥb) (Rᵀ*ᵥb) = Rᵀ*vecMulVec b b*R := by
  rw [mul_vecMulVec,vecMulVec_mul,←vecMul_transpose Rᵀ,transpose_transpose]

lemma congruence_sum_outer (R : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin m → Fin n → ℝ) (A : Finset (Fin m)) :
    (∑e∈A,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e)) = Rᵀ*(∑e∈A,vecMulVec (b e) (b e))*R := by
  simp only [congruence_outer,Matrix.mul_sum,Matrix.sum_mul]

lemma cov_bound (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin d) ℝ) (hRR : R*Rᵀ=P⁻¹)
    (b : Fin m → Fin n → ℝ) (hb : (∑e,vecMulVec (b e) (b e)) ≤ P) :
    (∑e,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e)) ≤ (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [congruence_sum_outer]
  exact (congruence_mono hb R).trans (normalized_covariance P hP R hRR)

lemma transfer (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin d) ℝ) (hRR : R*Rᵀ=P⁻¹)
    (b : Fin m → Fin n → ℝ) (A : Finset (Fin m)) {ε : ℝ}
    (h : -(ε • (1 : Matrix (Fin d) (Fin d) ℝ)) ≤
      (∑e∈A,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e))-(1/2:ℝ) • (∑e,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e)) ∧
      (∑e∈A,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e))-(1/2:ℝ) • (∑e,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e)) ≤ ε • 1) :
    -(ε • P) ≤ (∑e∈A,vecMulVec (b e) (b e))-(1/2:ℝ) • (∑e,vecMulVec (b e) (b e)) ∧
      (∑e∈A,vecMulVec (b e) (b e))-(1/2:ℝ) • (∑e,vecMulVec (b e) (b e)) ≤ ε • P := by
  let S := P*R
  have hu := congruence_mono h.2 Sᵀ
  have hl := congruence_mono h.1 Sᵀ
  have hs : S*Rᵀ=1 := (recover P hP R hRR).1
  have hss : S*Sᵀ=P := (recover P hP R hRR).2
  have ht : R*Sᵀ=1 := by
    have hh := congrArg transpose hs
    simpa only [transpose_mul,transpose_transpose,transpose_one] using hh
  have simplify (F : Matrix (Fin n) (Fin n) ℝ) : S*(Rᵀ*F*R)*Sᵀ=F := by
    rw [Matrix.mul_assoc Rᵀ F R,←Matrix.mul_assoc S Rᵀ,hs,Matrix.one_mul,Matrix.mul_assoc,ht,Matrix.mul_one]
  simp only [transpose_transpose,congruence_sum_outer,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_one,simplify,hss,Matrix.mul_neg,Matrix.neg_mul] at hu hl
  exact ⟨hl,hu⟩

lemma cast_inverse (P : Matrix (Fin n) (Fin n) ℚ) :
    (P⁻¹).map (fun q : ℚ => (q:ℝ)) = (P.map (fun q : ℚ => (q:ℝ)))⁻¹ := by
  have hadj : P.adjugate.map (fun q : ℚ => (q:ℝ)) =
      (P.map (fun q : ℚ => (q:ℝ))).adjugate := (Rat.castHom ℝ).map_adjugate P
  rw [Matrix.inv_def,Matrix.inv_def,Ring.inverse_eq_inv,Ring.inverse_eq_inv]
  ext i j
  simp only [map_apply,Matrix.smul_apply,smul_eq_mul,Rat.cast_mul,Rat.cast_inv]
  rw [←Rat.cast_det]
  have hh := congrFun (congrFun hadj i) j
  exact congrArg ((P.det:ℝ)⁻¹ * ·) hh

lemma rationalFactor_correct (P : Matrix (Fin n) (Fin n) ℚ)
    (hP : (P.map (fun q : ℚ => (q:ℝ))).PosDef) :
    (rationalFactor P).map (fun q : ℚ => (q:ℝ)) *
      ((rationalFactor P).map (fun q : ℚ => (q:ℝ)))ᵀ = (P.map (fun q : ℚ => (q:ℝ)))⁻¹ := by
  unfold rationalFactor
  rw [RationalInverse.inverse_eq_of_cast P hP]
  have hInv : (P⁻¹.map (fun q : ℚ => (q:ℝ))).PosSemidef := by
    rw [cast_inverse]; exact hP.inv.posSemidef
  have hh := congrArg (fun M => M.map (fun q : ℚ => (q:ℝ)))
    (RationalGram.factorMatrix_correct P⁻¹ hInv)
  change (RationalGram.factorMatrix P⁻¹ * (RationalGram.factorMatrix P⁻¹)ᵀ).map
    (Rat.castHom ℝ) = _ at hh
  rw [Matrix.map_mul] at hh
  exact hh.trans (cast_inverse P)

end AlgorithmicThinTrees.GramWhitening
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_RealMatrixBridge
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real matrix bridge. -/

section

namespace AlgorithmicThinTrees.RealMatrixBridge
noncomputable section
open Matrix CurrentKS
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n m d : ℕ}

lemma complexMatrix_one : complexMatrix (1 : Matrix (Fin n) (Fin n) ℝ)=1 := by
  exact Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

lemma complexMatrix_sub (A B : Matrix (Fin n) (Fin m) ℝ) :
    complexMatrix (A-B)=complexMatrix A-complexMatrix B := by
  ext i j;simp [complexMatrix]

lemma complexMatrix_smul (r : ℝ) (A : Matrix (Fin n) (Fin m) ℝ) :
    complexMatrix (r • A)=r • complexMatrix A := by
  ext i j;simp [complexMatrix]

lemma complexMatrix_mul (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ) :
    complexMatrix (A*B)=complexMatrix A*complexMatrix B := by
  exact Matrix.map_mul (f:=Complex.ofRealHom)

lemma complexMatrix_transpose (A : Matrix (Fin n) (Fin m) ℝ) :
    complexMatrix Aᵀ=(complexMatrix A)ᴴ := by
  ext i j;simp [complexMatrix]

lemma complexMatrix_hermitian {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (complexMatrix A).IsHermitian := by
  apply hA.map
  intro r
  simp

lemma complexMatrix_psd {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (complexMatrix A).PosSemidef := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB]
  change (complexMatrix (Bᴴ*B)).PosSemidef
  rw [conjTranspose_eq_transpose_of_trivial,complexMatrix_mul,complexMatrix_transpose]
  exact posSemidef_conjTranspose_mul_self _

lemma of_complexMatrix_psd {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : (complexMatrix A).PosSemidef) : A.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · apply isHermitian_iff_isSymm.mpr
    ext i j
    have hh := hA.isHermitian.apply i j
    have hr := congrArg Complex.re hh
    simpa [complexMatrix] using hr
  · intro x
    have hh := hA.dotProduct_mulVec_nonneg (fun i => (x i:ℂ))
    have he : star (fun i => (x i:ℂ)) ⬝ᵥ
        (complexMatrix A *ᵥ (fun i => (x i:ℂ)))=((x ⬝ᵥ (A*ᵥx):ℝ):ℂ) := by
      simp only [dotProduct,mulVec,complexMatrix,map_apply,Pi.star_apply,
        Complex.star_def,Complex.conj_ofReal,Complex.ofReal_sum,Complex.ofReal_mul]
    rw [he,Complex.zero_le_real] at hh
    simpa only [star_trivial] using hh

lemma complexMatrix_mono {A B : Matrix (Fin n) (Fin n) ℝ} (h : A ≤ B) :
    complexMatrix A ≤ complexMatrix B := by
  rw [Matrix.le_iff,←complexMatrix_sub]
  exact complexMatrix_psd h

lemma of_complexMatrix_le {A B : Matrix (Fin n) (Fin n) ℝ}
    (h : complexMatrix A ≤ complexMatrix B) : A ≤ B := by
  apply of_complexMatrix_psd
  rw [complexMatrix_sub]
  exact h

lemma le_norm_identity {A : Matrix (Fin n) (Fin n) ℝ} (hh : A.IsHermitian) :
    A ≤ opNorm (complexMatrix A) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  apply of_complexMatrix_le
  rw [complexMatrix_smul,complexMatrix_one]
  exact Hermitian.le_operatorNorm_smul_one ⟨complexMatrix A,complexMatrix_hermitian hh⟩

lemma norm_le_of_psd_bound {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {r : ℝ} (hr : 0 ≤ r) (h : A ≤ r • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    opNorm (complexMatrix A) ≤ r := by
  apply Hermitian.operatorNorm_le_of_psd_le (A:=⟨complexMatrix A,complexMatrix_hermitian hA.isHermitian⟩)
    (complexMatrix_psd hA) hr
  have hh := complexMatrix_mono h
  rwa [complexMatrix_smul,complexMatrix_one] at hh

lemma bounds_of_norm_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    {r : ℝ} (h : opNorm (complexMatrix A) ≤ r) :
    (-r) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A ∧ A ≤ r • 1 := by
  have hs {s t : ℝ} (hst : s ≤ t) : s • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ t • 1 := by
    rw [Matrix.le_iff,←sub_smul]
    exact PosSemidef.one.smul (sub_nonneg.mpr hst)
  constructor
  · have hh := le_norm_identity hA.neg
    have hn : opNorm (complexMatrix (-A))=opNorm (complexMatrix A) := by
      have he : complexMatrix (-A)=-complexMatrix A := by ext i j;simp [complexMatrix]
      rw [he,opNorm,map_neg,norm_neg]
      rfl
    rw [hn] at hh
    have hu := hh.trans (hs h)
    have hl := neg_le_neg hu
    simpa only [neg_neg,neg_smul] using hl
  · exact (le_norm_identity hA).trans (hs h)

end
end AlgorithmicThinTrees.RealMatrixBridge
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_RationalSigning
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_originalView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational signing. -/

section

namespace AlgorithmicThinTrees.RationalSigning
open Matrix Finset CurrentKS
open RealMatrixBridge
open scoped MatrixOrder ComplexOrder
variable {d m : ℕ}

lemma input_matrix (v : Fin m → Fin d → ℚ) (e : Fin m) :
    (input v).matrix e=complexMatrix (outer v e) := by
  change (fun i j => CurrentKS.toComplex (entry (v e i*v e j),entry 0)) =
    complexMatrix (outer v e)
  ext i j
  apply Complex.ext <;>
    simp [CurrentKS.toComplex,entry_value,outer,realVec,complexMatrix,vecMulVec_apply]

lemma complex_outer (u : Fin d → ℝ) :
    complexMatrix (vecMulVec u u)=vecMulVec (fun i => (u i:ℂ)) (star (fun i => (u i:ℂ))) := by
  ext i j
  simp [complexMatrix,vecMulVec_apply]

lemma input_admissible (v : Fin m → Fin d → ℚ) : CurrentKS.Admissible (input v) := by
  intro e
  change Fin m at e
  rw [input_matrix,outer,complex_outer]
  exact ⟨(posSemidef_vecMulVec_self_star _).isHermitian,rank_vecMulVec_le _ _⟩

lemma outer_psd (v : Fin m → Fin d → ℚ) (e : Fin m) : (outer v e).PosSemidef := by
  simpa only [outer,star_trivial] using posSemidef_vecMulVec_self_star (realVec v e)

lemma outer_square (v : Fin m → Fin d → ℚ) (e : Fin m) :
    outer v e*outer v e=(realVec v e ⬝ᵥ realVec v e) • outer v e := by
  rw [outer,vecMulVec_mul_vecMulVec]
  ext i j
  simp only [vecMulVec_apply,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma complexMatrix_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d) (Fin d) ℝ) :
    complexMatrix (∑e∈s, A e)=∑e∈s, complexMatrix (A e) := by
  ext i j
  simp only [complexMatrix,map_apply,Matrix.sum_apply,Complex.ofReal_sum]

lemma variance_eq (v : Fin m → Fin d → ℚ) :
    variance (input v)=complexMatrix (∑e, (realVec v e ⬝ᵥ realVec v e) • outer v e) := by
  have hm (e : Fin m) := input_matrix v e
  dsimp only [input] at hm
  simp only [variance,input]
  simp only [hm]
  change (∑e : Fin m, complexMatrix (outer v e)*complexMatrix (outer v e)) = _
  simp only [←complexMatrix_mul,outer_square,complexMatrix_sum]

lemma scalar_order {A B : Matrix (Fin d) (Fin d) ℝ} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  rw [Matrix.le_iff,←smul_sub]
  exact (Matrix.le_iff.mp h).smul hc

lemma variance_bound (v : Fin m → Fin d → ℚ) {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hcov : (∑e, outer v e) ≤ c • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hnorm : ∀e, realVec v e ⬝ᵥ realVec v e ≤ δ) :
    opNorm (variance (input v)) ≤ c*δ := by
  rw [variance_eq]
  have hp : (∑e, (realVec v e ⬝ᵥ realVec v e) • outer v e).PosSemidef := by
    refine Matrix.posSemidef_sum _ ?_
    intro e _
    exact (outer_psd v e).smul (by unfold dotProduct;exact sum_nonneg (fun e _ => mul_self_nonneg _))
  apply norm_le_of_psd_bound hp (mul_nonneg hc hδ)
  have hle : (∑e, (realVec v e ⬝ᵥ realVec v e) • outer v e) ≤ δ • (∑e, outer v e) := by
    rw [smul_sum]
    apply sum_le_sum
    intro e _
    rw [Matrix.le_iff,←sub_smul]
    exact (outer_psd v e).smul (sub_nonneg.mpr (hnorm e))
  exact hle.trans ((scalar_order hcov hδ).trans_eq (by rw [smul_smul,mul_comm δ c]))

lemma signed_eq (v : Fin m → Fin d → ℚ) (bits : List Bool) :
    CurrentKS.signedSum (input v) bits=complexMatrix
      (∑e, CurrentKS.signValue (bits.getD e.val false) • outer v e) := by
  have hm (e : Fin m) := input_matrix v e
  dsimp only [input] at hm
  simp only [signedSum,input]
  simp only [hm,complexMatrix_sum,complexMatrix_smul]
  rfl

lemma half_identity (v : Fin m → Fin d → ℚ) :
    (∑e∈selected v, outer v e)-(1/2:ℝ) • (∑e,outer v e)=
      (1/2:ℝ) • (∑e, CurrentKS.signValue
        ((CurrentKS.RationalInput.signing (input v)).getD e.val false) • outer v e) := by
  rw [selected,sum_filter,smul_sum,smul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  cases (CurrentKS.RationalInput.signing (input v)).getD e.val false <;>
    simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,signValue,smul_smul] <;> module

theorem half_bounds (v : Fin m → Fin d → ℚ) {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hcov : (∑e,outer v e) ≤ c • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hnorm : ∀e, realVec v e ⬝ᵥ realVec v e ≤ δ) :
    let D := (∑e∈selected v,outer v e)-(1/2:ℝ) • (∑e,outer v e)
    (-(20*Real.sqrt (c*δ))) • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ D ∧
      D ≤ (20*Real.sqrt (c*δ)) • 1 := by
  let bits := CurrentKS.RationalInput.signing (input v)
  have hsign := (CurrentKS.RationalInput.signing_good (input v) (input_admissible v)).2
  have hvar := variance_bound v hδ hc hcov hnorm
  have hnorm' : opNorm (complexMatrix (∑e,CurrentKS.signValue (bits.getD e.val false) • outer v e)) ≤
      40*Real.sqrt (c*δ) := by
    rw [←signed_eq]
    exact hsign.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) (by norm_num))
  have hH : (∑e,CurrentKS.signValue (bits.getD e.val false) • outer v e).IsHermitian := by
    change (∑e,CurrentKS.signValue (bits.getD e.val false) • outer v e)ᴴ = _
    rw [conjTranspose_sum]
    apply sum_congr rfl
    intro e _
    exact (outer_psd v e).isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial _))
  obtain ⟨hl,hu⟩ := bounds_of_norm_le hH hnorm'
  dsimp only
  rw [half_identity]
  have hhalf : (0:ℝ) ≤ 1/2 := by norm_num
  constructor
  · convert scalar_order hl hhalf using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_smul]
    congr 1
    ring
  · convert scalar_order hu hhalf using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_smul]
    congr 1
    ring

end AlgorithmicThinTrees.RationalSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_StackedSigning
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stacked signing. -/

section

namespace AlgorithmicThinTrees.StackedSigning
open Matrix Finset
open scoped MatrixOrder
variable {a b m : ℕ}

lemma dot_stack (x : Fin (a+b) → ℝ) (u : Fin a → ℝ) (v : Fin b → ℝ) :
    x ⬝ᵥ stack u v = (fun i => x (Fin.castAdd b i)) ⬝ᵥ u +
      (fun i => x (Fin.natAdd a i)) ⬝ᵥ v := by
  simp only [dotProduct,Fin.sum_univ_add,stack_left,stack_right]

lemma stack_norm (u : Fin a → ℝ) (v : Fin b → ℝ) :
    stack u v ⬝ᵥ stack u v=u ⬝ᵥ u+v ⬝ᵥ v := by
  simp only [dot_stack,stack_left,stack_right]

lemma gram_psd {d : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m)) :
    (gram v A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (v e)

lemma gram_eval {d : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m)) (x : Fin d → ℝ) :
    x ⬝ᵥ (gram v A*ᵥx)=∑e∈A,(x ⬝ᵥ v e)^2 := by
  simp only [gram,Matrix.sum_mulVec,dotProduct_sum,vecMulVec_mulVec,dotProduct_smul]
  apply sum_congr rfl
  intro e _
  rw [dotProduct_comm (v e) x,pow_two]
  rfl

lemma gram_eval_le {d : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m))
    {c : ℝ} (h : gram v A ≤ c • (1 : Matrix (Fin d) (Fin d) ℝ)) (x : Fin d → ℝ) :
    (∑e∈A,(x ⬝ᵥ v e)^2) ≤ c*(x ⬝ᵥ x) := by
  have hh := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,smul_eq_mul,gram_eval] at hh
  linarith only [hh]

lemma stack_covariance (u : Fin m → Fin a → ℝ) (v : Fin m → Fin b → ℝ)
    (hu : gram u univ ≤ 1) (hv : gram v univ ≤ 1) :
    gram (fun e => stack (u e) (v e)) univ ≤ (2:ℝ) • 1 := by
  rw [Matrix.le_iff]
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (Matrix.PosSemidef.one.smul (by norm_num : (0:ℝ) ≤ 2)).isHermitian.sub
      (gram_psd _ _).isHermitian
  intro x
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,smul_eq_mul,gram_eval]
  have h1 := gram_eval_le u univ (c:=1) (by simpa only [one_smul] using hu)
    (fun i => x (Fin.castAdd b i))
  have h2 := gram_eval_le v univ (c:=1) (by simpa only [one_smul] using hv)
    (fun i => x (Fin.natAdd a i))
  have hs : (∑e : Fin m, (x ⬝ᵥ stack (u e) (v e))^2) ≤
      2*(∑e : Fin m, ((fun i => x (Fin.castAdd b i)) ⬝ᵥ u e)^2)+
        2*(∑e : Fin m, ((fun i => x (Fin.natAdd a i)) ⬝ᵥ v e)^2) := by
    rw [mul_sum,mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro e _
    rw [dot_stack]
    nlinarith only [sq_nonneg (((fun i => x (Fin.castAdd b i)) ⬝ᵥ u e)-
      ((fun i => x (Fin.natAdd a i)) ⬝ᵥ v e))]
  have hx : x ⬝ᵥ x=(fun i => x (Fin.castAdd b i)) ⬝ᵥ (fun i => x (Fin.castAdd b i))+
      (fun i => x (Fin.natAdd a i)) ⬝ᵥ (fun i => x (Fin.natAdd a i)) := by
    exact Fin.sum_univ_add _
  nlinarith only [h1,h2,hs,hx]

lemma submatrix_mono {d e : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ} (h : A ≤ B)
    (f : Fin e → Fin d) : A.submatrix f f ≤ B.submatrix f f := by
  rw [Matrix.le_iff]
  exact (Matrix.le_iff.mp h).submatrix f

lemma gram_submatrix {d e : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m))
    (f : Fin e → Fin d) :
    (gram v A).submatrix f f=gram (fun j i => v j (f i)) A := by
  ext i j
  simp only [gram,submatrix_apply,Matrix.sum_apply,vecMulVec_apply]

lemma compress_half {d e : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m))
    (f : Fin e → Fin d) (hf : Function.Injective f) {ε : ℝ}
    (h : -(ε • (1 : Matrix (Fin d) (Fin d) ℝ)) ≤ gram v A-(1/2:ℝ) • gram v univ ∧
      gram v A-(1/2:ℝ) • gram v univ ≤ ε • 1) :
    -(ε • (1 : Matrix (Fin e) (Fin e) ℝ)) ≤
        gram (fun j i => v j (f i)) A-(1/2:ℝ) • gram (fun j i => v j (f i)) univ ∧
      gram (fun j i => v j (f i)) A-(1/2:ℝ) • gram (fun j i => v j (f i)) univ ≤ ε • 1 := by
  have h1 := submatrix_mono h.1 f
  have h2 := submatrix_mono h.2 f
  change -(ε • (1 : Matrix (Fin d) (Fin d) ℝ).submatrix f f) ≤
    (gram v A).submatrix f f-(1/2:ℝ) • (gram v univ).submatrix f f at h1
  change (gram v A).submatrix f f-(1/2:ℝ) • (gram v univ).submatrix f f ≤
    ε • (1 : Matrix (Fin d) (Fin d) ℝ).submatrix f f at h2
  simpa only [submatrix_one f hf,gram_submatrix] using And.intro h1 h2

lemma real_stack (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) (e : Fin m) :
    RationalSigning.realVec (fun e => stack (u e) (v e)) e=
      stack (RationalSigning.realVec u e) (RationalSigning.realVec v e) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [RationalSigning.realVec,stack_left,stack_right]

theorem simultaneous (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hu : gram (RationalSigning.realVec u) univ ≤ 1)
    (hv : gram (RationalSigning.realVec v) univ ≤ 1)
    (hnorm : ∀e, RationalSigning.realVec u e ⬝ᵥ RationalSigning.realVec u e+
      RationalSigning.realVec v e ⬝ᵥ RationalSigning.realVec v e ≤ δ) :
    let A := selected u v
    let ε := 20*Real.sqrt (2*δ)
    (-(ε • (1 : Matrix (Fin a) (Fin a) ℝ)) ≤
        gram (RationalSigning.realVec u) A-(1/2:ℝ) • gram (RationalSigning.realVec u) univ ∧
      gram (RationalSigning.realVec u) A-(1/2:ℝ) • gram (RationalSigning.realVec u) univ ≤ ε • 1) ∧
    (-(ε • (1 : Matrix (Fin b) (Fin b) ℝ)) ≤
        gram (RationalSigning.realVec v) A-(1/2:ℝ) • gram (RationalSigning.realVec v) univ ∧
      gram (RationalSigning.realVec v) A-(1/2:ℝ) • gram (RationalSigning.realVec v) univ ≤ ε • 1) := by
  have hcov := stack_covariance (RationalSigning.realVec u) (RationalSigning.realVec v) hu hv
  have hs := RationalSigning.half_bounds (fun e => stack (u e) (v e)) hδ (by norm_num : (0:ℝ) ≤ 2)
    (by simpa only [RationalSigning.outer,real_stack,gram] using hcov)
    (fun e => by simpa only [real_stack,stack_norm] using hnorm e)
  change (-(20*Real.sqrt (2*δ))) • (1 : Matrix (Fin (a+b)) (Fin (a+b)) ℝ) ≤ _ ∧ _ at hs
  simp only [neg_smul] at hs
  have hl := compress_half _ (selected u v) (Fin.castAdd b) (Fin.castAdd_injective a b) hs
  have hr := compress_half _ (selected u v) (Fin.natAdd a) (Fin.natAdd_injective b a) hs
  simpa only [real_stack,stack_left,stack_right] using And.intro hl hr

end AlgorithmicThinTrees.StackedSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_FormSigning
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Form signing. -/

section

namespace AlgorithmicThinTrees.FormSigning
open Matrix Finset GramWhitening StackedSigning RationalSigning
open scoped MatrixOrder
variable {a b m : ℕ}

lemma whiten_cast (P : Matrix (Fin a) (Fin a) ℚ) (v : Fin m → Fin a → ℚ) (e : Fin m) :
    realVec (whiten P v) e=((rationalFactor P).map (fun q : ℚ => (q:ℝ)))ᵀ*ᵥrealVec v e := by
  ext i
  simp only [whiten,realVec,mulVec,dotProduct,transpose_apply,map_apply,Rat.cast_sum,Rat.cast_mul]

lemma whiten_covariance (P : Matrix (Fin a) (Fin a) ℚ)
    (hP : (P.map (fun q : ℚ => (q:ℝ))).PosDef) (v : Fin m → Fin a → ℚ)
    (hv : StackedSigning.gram (realVec v) univ ≤ P.map (fun q : ℚ => (q:ℝ))) :
    StackedSigning.gram (realVec (whiten P v)) univ ≤ 1 := by
  simpa only [StackedSigning.gram,whiten_cast] using
    cov_bound _ hP _ (rationalFactor_correct P hP) (realVec v) hv

lemma whiten_norm (P : Matrix (Fin a) (Fin a) ℚ)
    (hP : (P.map (fun q : ℚ => (q:ℝ))).PosDef) (v : Fin m → Fin a → ℚ) (e : Fin m) :
    realVec (whiten P v) e ⬝ᵥ realVec (whiten P v) e=
      realVec v e ⬝ᵥ ((P.map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec v e) := by
  rw [whiten_cast,rectangular_norm,rationalFactor_correct P hP]

theorem simultaneous (P : Matrix (Fin a) (Fin a) ℚ) (Q : Matrix (Fin b) (Fin b) ℚ)
    (hP : (P.map (fun q : ℚ => (q:ℝ))).PosDef) (hQ : (Q.map (fun q : ℚ => (q:ℝ))).PosDef)
    (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : StackedSigning.gram (realVec u) univ ≤ P.map (fun q : ℚ => (q:ℝ)))
    (hv : StackedSigning.gram (realVec v) univ ≤ Q.map (fun q : ℚ => (q:ℝ)))
    (hnorm : ∀e, realVec u e ⬝ᵥ ((P.map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec u e)+
      realVec v e ⬝ᵥ ((Q.map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec v e) ≤ δ) :
    let A := selected P Q u v
    let ε := 20*Real.sqrt (2*δ)
    (-(ε • P.map (fun q : ℚ => (q:ℝ))) ≤
        StackedSigning.gram (realVec u) A-(1/2:ℝ) • StackedSigning.gram (realVec u) univ ∧
      StackedSigning.gram (realVec u) A-(1/2:ℝ) • StackedSigning.gram (realVec u) univ ≤ ε • P.map (fun q : ℚ => (q:ℝ))) ∧
    (-(ε • Q.map (fun q : ℚ => (q:ℝ))) ≤
        StackedSigning.gram (realVec v) A-(1/2:ℝ) • StackedSigning.gram (realVec v) univ ∧
      StackedSigning.gram (realVec v) A-(1/2:ℝ) • StackedSigning.gram (realVec v) univ ≤ ε • Q.map (fun q : ℚ => (q:ℝ))) := by
  have h := StackedSigning.simultaneous (whiten P u) (whiten Q v) hδ
    (whiten_covariance P hP u hu) (whiten_covariance Q hQ v hv)
    (fun e => by simpa only [whiten_norm P hP,whiten_norm Q hQ] using hnorm e)
  constructor
  · exact transfer _ hP _ (rationalFactor_correct P hP) (realVec u) (selected P Q u v)
      (by simpa only [StackedSigning.gram,whiten_cast,selected] using h.1)
  · exact transfer _ hQ _ (rationalFactor_correct Q hQ) (realVec v) (selected P Q u v)
      (by simpa only [StackedSigning.gram,whiten_cast,selected] using h.2)

lemma gram_restrict {d : ℕ} (v : Fin m → Fin d → ℝ) (B A : Finset (Fin m))
    (h : ∀e, e ∉ B → v e=0) : StackedSigning.gram v (A∩B)=StackedSigning.gram v A := by
  unfold StackedSigning.gram
  apply sum_subset_zero_on_sdiff inter_subset_left
  · intro e he
    obtain ⟨he,he'⟩ := mem_sdiff.mp he
    have hb : e ∉ B := fun hb => he' (mem_inter.mpr ⟨he,hb⟩)
    rw [h e hb,zero_vecMulVec]
  · intros; rfl

end AlgorithmicThinTrees.FormSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_GraphicNormalization
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graphic normalization. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
variable {d m q : ℕ}

lemma graphColumns_cast (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (e : Fin m) :
    realColumns (graphColumns G B) e = if e ∈ B then
      dropRoot d ⟨G.incidence e,G.incidence_zeroSum e⟩ else 0 := by
  funext i
  by_cases he : e ∈ B
  · rw [ite_eq_left he]
    change ((integerColumns G B e i : ℚ):ℝ) = G.incidence e i.succ
    simp only [integerColumns,ite_eq_left he,Int.cast_sub,incidence,
      point,Pi.sub_apply,Pi.single_apply,eq_comm (a:=i.succ)]
    split_ifs <;> norm_num
  · simp [he,realColumns,graphColumns,integerColumns]

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_GraphicHalf
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graphic half. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {n d m : ℕ}

lemma fullColumns_cast (G : MultiGraph n m) (B : Finset (Fin m)) (e : Fin m) :
    realVec (fullColumns G B) e=if e ∈ B then G.incidence e else 0 := by
  ext i
  by_cases he : e ∈ B
  · simp only [realVec,fullColumns,ite_eq_left he,cast_qinc]
  · simp only [fullColumns,he,ite_false, if_false,realVec,Pi.zero_apply,Rat.cast_zero]

lemma fullColumns_gram (G : MultiGraph n m) (B A : Finset (Fin m)) :
    StackedSigning.gram (realVec (fullColumns G B)) A=G.laplacian (A∩B) := by
  simp only [StackedSigning.gram,fullColumns_cast]
  rw [laplacian]
  rw [show A∩B=A.filter (fun e => e ∈ B) by ext; simp]
  rw [sum_filter]
  apply sum_congr rfl
  intro e he
  split_ifs <;> simp only [zero_vecMulVec]

lemma positiveForm_cast (X : Matrix (Fin n) (Fin n) ℚ) :
    (positiveForm X).map (fun q : ℚ => (q:ℝ))=regularize (X.map (fun q : ℚ => (q:ℝ))) := by
  ext i j
  simp only [positiveForm,map_apply,Matrix.add_apply,Rat.cast_add,Matrix.of_apply,Rat.cast_inv,
    Rat.cast_natCast,regularize,constantProjection,Matrix.smul_apply,smul_eq_mul,vecMulVec,ones,mul_one]

lemma scaledColumns_cast (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (s : Fin m → ℚ) (e : Fin m) :
    realVec (scaledColumns G B s) e=(s e:ℝ) • realColumns (graphColumns G B) e := by
  ext i
  simp only [realVec,scaledColumns,Pi.smul_apply,smul_eq_mul,Rat.cast_mul,realColumns]

lemma scaledForm_cast (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ) :
    (scaledForm G B s).map (fun q : ℚ => (q:ℝ))=
      covariance (realColumns (graphColumns G B)) (realWeights s) := by
  ext i j
  simp only [scaledForm,covariance,map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    vecMulVec,weights,realColumns,realWeights,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Matrix.of_apply]

lemma scaledColumns_gram (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ) :
    StackedSigning.gram (realVec (scaledColumns G B s)) univ=
      (scaledForm G B s).map (fun q : ℚ => (q:ℝ)) := by
  rw [scaledForm_cast]
  ext i j
  simp only [StackedSigning.gram,scaledColumns_cast,covariance,realWeights,
    Matrix.sum_apply,vecMulVec,Pi.smul_apply,smul_eq_mul,Matrix.smul_apply,Matrix.of_apply]
  apply sum_congr rfl
  intro e _
  ring

lemma scaledColumns_zero (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ)
    (e : Fin m) (he : e ∉ B) : realVec (scaledColumns G B s) e=0 := by
  rw [scaledColumns_cast,graphColumns_cast,ite_eq_right he,smul_zero]

lemma scaledColumns_leverage (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (s : Fin m → ℚ) (e : Fin m) :
    realVec (scaledColumns G B s) e ⬝ᵥ
      (((scaledForm G B s).map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec (scaledColumns G B s) e)=
      leverage (realColumns (graphColumns G B)) (realWeights s) e := by
  rw [scaledColumns_cast,scaledForm_cast]
  simp only [leverage,realWeights,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

lemma laplacian_mono (G : MultiGraph n m) {A B : Finset (Fin m)} (h : A ⊆ B) :
    G.laplacian A ≤ G.laplacian B := by
  apply sum_le_sum_of_subset_of_nonneg h
  intro e _ _
  exact Matrix.nonneg_iff_posSemidef.mpr (ShortcutDual.outer_posSemidef _)

lemma fullColumns_covariance (G : MultiGraph n m) (B : Finset (Fin m))
    (X : Matrix (Fin n) (Fin n) ℚ) (hX : X.map (fun q : ℚ => (q:ℝ)) ∈ metricDomain G) :
    StackedSigning.gram (realVec (fullColumns G B)) univ ≤
      (positiveForm X).map (fun q : ℚ => (q:ℝ)) := by
  rw [fullColumns_gram,univ_inter,positiveForm_cast]
  apply ((laplacian_mono G (subset_univ B)).trans hX.2.2.1).trans
  exact le_add_of_nonneg_right (Matrix.nonneg_iff_posSemidef.mpr constantProjection_psd)

theorem half_bounds_oai (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (X : Matrix (Fin (d+1)) (Fin (d+1)) ℚ) (s : Fin m → ℚ)
    (hconn : G.Connected univ) (hX : X.map (fun q : ℚ => (q:ℝ)) ∈ metricDomain G)
    (hQ : ((scaledForm G B s).map (fun q : ℚ => (q:ℝ))).PosDef)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnorm : ∀e, realVec (fullColumns G B) e ⬝ᵥ
        (((positiveForm X).map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec (fullColumns G B) e)+
      leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ δ) :
    let A := halfEdges G B X s
    let ε := 20*Real.sqrt (2*δ)
    G.laplacian A ≤ (1/2:ℝ) • G.laplacian B+ε • regularize (X.map (fun q : ℚ => (q:ℝ))) ∧
    (1/2-ε) • (scaledForm G B s).map (fun q : ℚ => (q:ℝ)) ≤
      StackedSigning.gram (realVec (scaledColumns G B s)) A := by
  have hP : ((positiveForm X).map (fun q : ℚ => (q:ℝ))).PosDef := by
    rw [positiveForm_cast]
    exact regularize_pd (by omega) (domain_positive G (by omega) hconn hX)
  obtain ⟨hu,hv⟩ := FormSigning.simultaneous (positiveForm X) (scaledForm G B s) hP hQ
    (fullColumns G B) (scaledColumns G B s) hδ (fullColumns_covariance G B X hX)
    (scaledColumns_gram G B s).le (by simpa only [scaledColumns_leverage] using hnorm)
  simp only [fullColumns_gram,univ_inter,positiveForm_cast] at hu
  rw [scaledColumns_gram] at hv
  dsimp only
  constructor
  · exact (sub_le_iff_le_add.mp hu.2).trans_eq (add_comm _ _)
  · rw [halfEdges,FormSigning.gram_restrict _ B _ (scaledColumns_zero G B s)]
    rw [sub_smul]
    have hh := (le_sub_iff_add_le.mp hv.1)
    simpa only [add_comm,sub_eq_add_neg] using hh

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

theorem solution : type_of% @OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds_oai := @OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds_oai
